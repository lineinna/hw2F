#include "sp.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#ifndef _WIN32
#include <sys/wait.h>
#else
#include <process.h>
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct Entry {
  char *key;
  char *value;
  struct Entry *next;
} Entry;

typedef struct {
  char *data;
  size_t len;
  size_t capacity;
} InputBuffer;

typedef struct Child {
  pid_t pid;
  int command_fd;
  int reply_fd;
  char *command_path;
  char *reply_path;
  struct Child *next;
} Child;

enum {
  READ_LINE_OK = 0,
  READ_LINE_EOF = 1,
  READ_LINE_ERROR = -1
};

static Entry *table = NULL;
static Child *children = NULL;
static Entry *find_entry(const char *key);
static int set_entry(const char *key, const char *value);
static int remove_entry(const char *key);
static void free_table(void);
static int read_command_line(int fd, InputBuffer *input, char **line,
                             size_t *line_len);
static int classify_command(const char *line, size_t line_len);
static int parse_key_value(const char *line, size_t line_len, const char *name,
                           char **key, char **value);
static int parse_single_key(const char *line, size_t line_len,
                            const char *name, char **key);
static int parse_two_keys(const char *line, size_t line_len, const char *name,
                          char **first, char **second);
static int run_child(const char *command_path, const char *reply_path,
                     int ready_fd);
static void terminate_children(void);

static int command_name_matches(const char *line, size_t line_len,
                                const char *name) {
  size_t name_len = strlen(name);

  if (line_len < name_len || memcmp(line, name, name_len) != 0) {
    return 0;
  }

  return line_len == name_len || line[name_len] == ' ';
}

static int classify_command(const char *line, size_t line_len) {
  if (command_name_matches(line, line_len, "create")) {
    return CREATE;
  }
  if (command_name_matches(line, line_len, "store")) {
    return STORE;
  }
  if (command_name_matches(line, line_len, "delete")) {
    return DELETE;
  }
  if (command_name_matches(line, line_len, "fetch")) {
    return FETCH;
  }
  if (command_name_matches(line, line_len, "kill")) {
    return KILL;
  }
  if (command_name_matches(line, line_len, "update")) {
    return UPDATE;
  }

  return UNKNOWN;
}

static char *duplicate_string(const char *source) {
  size_t length = strlen(source);
  if (length == SIZE_MAX) {
    return NULL;
  }
  char *copy = malloc(length + 1);
  if (copy == NULL) {
    return NULL;
  }
  memcpy(copy, source, length + 1);
  return copy;
}

static int copy_range(const char *source, size_t length, char **result) {
  if (length == SIZE_MAX) {
    return -1;
  }

  *result = malloc(length + 1);
  if (*result == NULL) {
    return -1;
  }

  memcpy(*result, source, length);
  (*result)[length] = '\0';
  return 0;
}

static int parse_key_value(const char *line, size_t line_len, const char *name,
                           char **key, char **value) {
  size_t name_len = strlen(name);
  size_t key_start = name_len + 1;
  size_t key_end;

  *key = NULL;
  *value = NULL;

  if (!command_name_matches(line, line_len, name) ||
      line_len <= key_start) {
    return -1;
  }

  key_end = key_start;
  while (key_end < line_len && line[key_end] != ' ') {
    key_end++;
  }

  if (key_end == key_start || key_end == line_len) {
    return -1;
  }

  if (copy_range(line + key_start, key_end - key_start, key) != 0) {
    return -1;
  }

  if (copy_range(line + key_end + 1, line_len - key_end - 1, value) != 0) {
    free(*key);
    *key = NULL;
    return -1;
  }

  if ((*value)[0] == '\0') {
    free(*key);
    free(*value);
    *key = NULL;
    *value = NULL;
    return -1;
  }

  return 0;
}

static int parse_single_key(const char *line, size_t line_len,
                            const char *name, char **key) {
  size_t name_len = strlen(name);
  size_t key_start = name_len + 1;

  *key = NULL;

  if (!command_name_matches(line, line_len, name) ||
      line_len <= key_start) {
    return -1;
  }

  for (size_t i = key_start; i < line_len; i++) {
    if (line[i] == ' ') {
      return -1;
    }
  }

  return copy_range(line + key_start, line_len - key_start, key);
}

static int parse_two_keys(const char *line, size_t line_len, const char *name,
                          char **first, char **second) {
  size_t name_len = strlen(name);
  size_t first_start = name_len + 1;
  size_t first_end = first_start;
  size_t second_start;

  *first = NULL;
  *second = NULL;

  if (!command_name_matches(line, line_len, name) ||
      line_len <= first_start) {
    return -1;
  }

  while (first_end < line_len && line[first_end] != ' ') {
    first_end++;
  }

  if (first_end == first_start || first_end == line_len) {
    return -1;
  }

  second_start = first_end + 1;
  if (second_start == line_len) {
    return -1;
  }

  for (size_t i = second_start; i < line_len; i++) {
    if (line[i] == ' ') {
      return -1;
    }
  }

  if (copy_range(line + first_start, first_end - first_start, first) != 0) {
    return -1;
  }

  if (copy_range(line + second_start, line_len - second_start, second) != 0) {
    free(*first);
    *first = NULL;
    return -1;
  }

  return 0;
}
static Entry *find_entry(const char *key) {
  for (Entry *entry = table; entry != NULL; entry = entry->next) {
    if (strcmp(entry->key, key) == 0) {
      return entry;
    }
  }
  return NULL;
}
static int set_entry(const char *key, const char *value) {
  Entry *entry = find_entry(key);
  if (entry != NULL) {
    char *new_value = duplicate_string(value);
    if (new_value == NULL) {
      return -1;
    }
    free(entry->value);
    entry->value = new_value;
    return 0;
  }
  Entry *new_entry = malloc(sizeof(*new_entry));
  if (new_entry == NULL) {
    return -1;
  }
  new_entry->key = duplicate_string(key);
  if (new_entry->key == NULL) {
    free(new_entry);
    return -1;
  }
  new_entry->value = duplicate_string(value);
  if (new_entry->value == NULL) {
    free(new_entry->key);
    free(new_entry);
    return -1;
  }
  new_entry->next = table;
  table = new_entry;
  return 0;
}

static int remove_entry(const char *key) {
  Entry *previous = NULL;
  Entry *entry = table;
  while (entry != NULL) {
    if (strcmp(entry->key, key) == 0) {
      if (previous == NULL) {
        table = entry->next;
      } else {
        previous->next = entry->next;
      }

      free(entry->key);
      free(entry->value);
      free(entry);
      return 0;
    }

    previous = entry;
    entry = entry->next;
  }
  return 0;
}

static void free_table(void) {
  Entry *entry = table;
  while (entry != NULL) {
    Entry *next = entry->next;
    free(entry->key);
    free(entry->value);
    free(entry);
    entry = next;
  }
  table = NULL;
}

static void reap_child(pid_t pid) {
#ifdef _WIN32
  int status;
  _cwait(&status, pid, 0);
#else
  waitpid(pid, NULL, 0);
#endif
}

static void stop_child(pid_t pid) {
#ifdef _WIN32
  _kill(pid, SIGTERM);
#else
  kill(pid, SIGTERM);
#endif
}

static void free_child(Child *child) {
  if (child == NULL) {
    return;
  }
  if (child->command_fd >= 0) {
    close(child->command_fd);
  }
  if (child->reply_fd >= 0) {
    close(child->reply_fd);
  }
  unlink(child->command_path);
  unlink(child->reply_path);
  free(child->command_path);
  free(child->reply_path);
  free(child);
}

static void terminate_children(void) {
  Child *child = children;

  while (child != NULL) {
    stop_child(child->pid);
    child = child->next;
  }

  child = children;
  while (child != NULL) {
    Child *next = child->next;
    reap_child(child->pid);
    free_child(child);
    child = next;
  }
  children = NULL;
}

static int read_command_line(int fd, InputBuffer *input, char **line,
                             size_t *line_len) {
  char chunk[4096];

  *line = NULL;
  *line_len = 0;

  for (;;) {
    char *newline = memchr(input->data, '\n', input->len);
    if (newline != NULL) {
      size_t command_length = (size_t)(newline - input->data);
      size_t consumed = command_length + 1;
      size_t remaining = input->len - consumed;

      char *command = malloc(command_length + 1);
      if (command == NULL) {
        perror("malloc");
        return READ_LINE_ERROR;
      }

      memcpy(command, input->data, command_length);
      command[command_length] = '\0';

      memmove(input->data, input->data + consumed, remaining);
      input->len = remaining;

      *line = command;
      *line_len = command_length;
      return READ_LINE_OK;
    }

    ssize_t bytes_read = read(fd, chunk, sizeof(chunk));
    if (bytes_read < 0) {
      if (errno == EINTR) {
        continue;
      }

      perror("read command");
      return READ_LINE_ERROR;
    }

    if (bytes_read == 0) {
      return READ_LINE_EOF;
    }

    size_t count = (size_t)bytes_read;
    if (input->len > SIZE_MAX - count) {
      fprintf(stderr, "Input buffer size overflow\n");
      return READ_LINE_ERROR;
    }

    size_t required = input->len + count;
    if (required > input->capacity) {
      size_t new_capacity = input->capacity == 0 ? sizeof(chunk)
                                                 : input->capacity;

      while (new_capacity < required) {
        if (new_capacity > SIZE_MAX / 2) {
          new_capacity = required;
          break;
        }
        new_capacity *= 2;
      }

      char *new_data = realloc(input->data, new_capacity);
      if (new_data == NULL) {
        perror("realloc");
        return READ_LINE_ERROR;
      }

      input->data = new_data;
      input->capacity = new_capacity;
    }

    memcpy(input->data + input->len, chunk, count);
    input->len += count;
  }
}

static int run_command_loop(int input_fd) {
  InputBuffer input = {0};
  int result_code = 0;

  for (;;) {
    char *command_buffer = NULL;
    size_t command_length = 0;
    int read_result = read_command_line(input_fd, &input, &command_buffer,
                                        &command_length);

    if (read_result == READ_LINE_EOF) {
      free(command_buffer);
      break;
    }
    if (read_result == READ_LINE_ERROR) {
      free(command_buffer);
      result_code = 1;
      break;
    }

    Command command = {
        .buf = command_buffer,
        .len = command_length,
        .type = classify_command(command_buffer, command_length),
    };

    if (command.type == KILL) {
      free(command_buffer);
      break;
    }
    if (command.type == UNKNOWN || command_handler(&command) < 0) {
      free(command_buffer);
      result_code = 1;
      break;
    }
    free(command_buffer);
  }

  free(input.data);
  free_table();
  return result_code;
}

static int run_child(const char *command_path, const char *reply_path,
                     int ready_fd) {
  int command_fd = -1;
  int reply_fd = -1;

  if (mkfifo(command_path, 0600) < 0 && errno != EEXIST) {
    perror("mkfifo command");
    close(ready_fd);
    return 1;
  }
  if (mkfifo(reply_path, 0600) < 0 && errno != EEXIST) {
    perror("mkfifo reply");
    unlink(command_path);
    close(ready_fd);
    return 1;
  }

  if (write(ready_fd, "R", 1) != 1) {
    perror("child ready");
    close(ready_fd);
    unlink(command_path);
    unlink(reply_path);
    return 1;
  }
  close(ready_fd);

  command_fd = open(command_path, O_RDONLY);
  if (command_fd < 0) {
    perror("open command FIFO");
    unlink(command_path);
    unlink(reply_path);
    return 1;
  }
  reply_fd = open(reply_path, O_WRONLY);
  if (reply_fd < 0) {
    perror("open reply FIFO");
    close(command_fd);
    unlink(command_path);
    unlink(reply_path);
    return 1;
  }
  if (dup2(reply_fd, STDOUT_FILENO) < 0) {
    perror("dup2 reply FIFO");
    close(command_fd);
    close(reply_fd);
    unlink(command_path);
    unlink(reply_path);
    return 1;
  }
  if (reply_fd != STDOUT_FILENO) {
    close(reply_fd);
  }

  int result = run_command_loop(command_fd);
  close(command_fd);
  unlink(command_path);
  unlink(reply_path);
  return result;
}

int main(int argc, char *argv[]) {
  if (argc == 5 && strcmp(argv[1], "--child") == 0) {
    return run_child(argv[2], argv[3], atoi(argv[4]));
  }
  if (argc > 1) {
    fprintf(stderr, "Usage: ./sp\n");
    return 1;
  }

  int result = run_command_loop(STDIN_FILENO);
  terminate_children();
  return result;
}

int command_handler(Command *cmd) {
  switch (cmd->type) {
  case CREATE:
    return create_handler(cmd->buf, cmd->len);
  case STORE:
    return store_handler(cmd->buf, cmd->len);
  case DELETE:
    return delete_handler(cmd->buf, cmd->len);
  case FETCH:
    return fetch_handler(cmd->buf, cmd->len);
  case KILL:
    return kill_handler(cmd->buf, cmd->len);
  case UPDATE:
    return update_handler(cmd->buf, cmd->len);
  default:
    fprintf(stderr, "Unknown command type\n");
    return -1;
  }
}

int create_handler(char *buf, size_t len) {
  char *command_path = NULL;
  char *reply_path = NULL;
  int ready_pipe[2] = {-1, -1};

  if (parse_two_keys(buf, len, "create", &command_path, &reply_path) != 0) {
    fprintf(stderr, "Invalid create command\n");
    return -1;
  }
  if (pipe(ready_pipe) < 0) {
    perror("pipe");
    free(command_path);
    free(reply_path);
    return -1;
  }

  pid_t pid = fork();
  if (pid < 0) {
    perror("fork");
    close(ready_pipe[0]);
    close(ready_pipe[1]);
    free(command_path);
    free(reply_path);
    return -1;
  }

  if (pid == 0) {
    char ready_fd_text[32];

    close(ready_pipe[0]);
    snprintf(ready_fd_text, sizeof(ready_fd_text), "%d", ready_pipe[1]);
    execl("./sp", "./sp", "--child", command_path, reply_path,
          ready_fd_text, (char *)NULL);
    perror("exec ./sp");
    _exit(127);
  }

  close(ready_pipe[1]);
  char ready = '\0';
  ssize_t ready_result;
  do {
    ready_result = read(ready_pipe[0], &ready, 1);
  } while (ready_result < 0 && errno == EINTR);
  close(ready_pipe[0]);

  if (ready_result != 1 || ready != 'R') {
    fprintf(stderr, "Child failed to initialize FIFOs\n");
    stop_child(pid);
    reap_child(pid);
    unlink(command_path);
    unlink(reply_path);
    free(command_path);
    free(reply_path);
    return -1;
  }

  int parent_command_fd = open(command_path, O_WRONLY);
  if (parent_command_fd < 0) {
    perror("open child command FIFO");
    stop_child(pid);
    reap_child(pid);
    unlink(command_path);
    unlink(reply_path);
    free(command_path);
    free(reply_path);
    return -1;
  }

  int parent_reply_fd = open(reply_path, O_RDONLY);
  if (parent_reply_fd < 0) {
    perror("open child reply FIFO");
    close(parent_command_fd);
    stop_child(pid);
    reap_child(pid);
    unlink(command_path);
    unlink(reply_path);
    free(command_path);
    free(reply_path);
    return -1;
  }

  Child *child = malloc(sizeof(*child));
  if (child == NULL) {
    perror("malloc child");
    close(parent_command_fd);
    close(parent_reply_fd);
    stop_child(pid);
    reap_child(pid);
    unlink(command_path);
    unlink(reply_path);
    free(command_path);
    free(reply_path);
    return -1;
  }

  child->pid = pid;
  child->command_fd = parent_command_fd;
  child->reply_fd = parent_reply_fd;
  child->command_path = command_path;
  child->reply_path = reply_path;
  child->next = children;
  children = child;
  return 0;
}

int store_handler(char *buf, size_t len) {
  char *key = NULL;
  char *value = NULL;

  if (parse_key_value(buf, len, "store", &key, &value) != 0) {
    fprintf(stderr, "Invalid store command\n");
    return -1;
  }

  int result = set_entry(key, value);
  if (result != 0) {
    perror("set_entry");
  }

  free(key);
  free(value);
  return result;
}

int delete_handler(char *buf, size_t len) {
  char *key = NULL;

  if (parse_single_key(buf, len, "delete", &key) != 0) {
    fprintf(stderr, "Invalid delete command\n");
    return -1;
  }

  int result = remove_entry(key);
  free(key);
  return result;
}

int fetch_handler(char *buf, size_t len) {
  char *hash = NULL;
  char *key = NULL;

  if (parse_two_keys(buf, len, "fetch", &hash, &key) != 0) {
    fprintf(stderr, "Invalid fetch command\n");
    return -1;
  }

  Entry *entry = find_entry(key);
  if (entry == NULL) {
    free(hash);
    free(key);
    return 1;
  }

  if (printf("%s %s\n", hash, entry->value) < 0 || fflush(stdout) != 0) {
    perror("write fetch reply");
    free(hash);
    free(key);
    return -1;
  }

  free(hash);
  free(key);
  return 0;
}

int kill_handler(char *buf, size_t len) {
  (void)buf;
  (void)len;
  free_table();
  return 1;
}

int update_handler(char *buf, size_t len) {
  // TODO: Implement the UPDATE command handler.
  (void)buf;
  (void)len;
  return -1;
}
