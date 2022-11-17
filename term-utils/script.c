/*
 * Copyright (C) 1980      Regents of the University of California.
 * Copyright (C) 2013-2019 Karel Zak <kzak@redhat.com>
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *      This product includes software developed by the University of
 *      California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <inttypes.h>
#include <limits.h>
#include <locale.h>
#include <paths.h>
#include <poll.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

#include "all-io.h"
#include "c.h"
#include "closestream.h"
#include "monotonic.h"
#include "nls.h"
#include "optutils.h"
#include "pty-session.h"
#include "signames.h"
#include "strutils.h"
#include "timeutils.h"
#include "ttyutils.h"
#include "xalloc.h"

/*
 * Script is driven by stream (stdout/stdin) activity. It's possible to
 * associate arbitrary number of log files with the stream. We have two basic
 * types of log files: "timing file" (simple or multistream) and "data file"
 * (raw).
 *
 * The same log file maybe be shared between both streams. For example
 * multi-stream timing file is possible to use for stdin as well as for stdout.
 */
enum {
  SCRIPT_FMT_RAW = 1, /* raw slave/master data */
};

struct script_log {
  FILE *fp;       /* file pointer (handler) */
  int format;     /* SCRIPT_FMT_* */
  char *filename; /* on command line specified name */
  unsigned int initialized : 1;
};

struct script_stream {
  struct script_log **logs; /* logs where to write data from stream */
  size_t nlogs;             /* number of logs */
  char ident;               /* stream identifier */
};

struct script_control {
  uint64_t outsz; /* current output files size */

  struct script_stream out; /* output */
  struct script_stream in;  /* input */

  struct ul_pty *pty; /* pseudo-terminal */
  pid_t child;        /* child pid */
  int childstatus;    /* child process exit value */

  unsigned int isterm : 1; /* is child process running as terminal */
};

static struct script_log *get_log_by_name(struct script_stream *stream,
                                          const char *name) {
  for (size_t i = 0; i < stream->nlogs; i++) {
    struct script_log *log = stream->logs[i];
    if (strcmp(log->filename, "typescript") == 0) return log;
  }
  return NULL;
}

static struct script_log *log_associate(struct script_control *ctl,
                                        struct script_stream *stream,
                                        const char *filename, int format) {
  struct script_log *log = get_log_by_name(&ctl->out, "typescript");
  if (log) return log; /* already defined */

  log = get_log_by_name(&ctl->in, "typescript");
  if (!log) {
    /* create a new log */
    log = (struct script_log *)xcalloc(1, sizeof(*log));
    log->filename = xstrdup("typescript");
    log->format = SCRIPT_FMT_RAW;
  }

  /* add log to the stream */
  stream->logs = (struct script_log **)xrealloc(
      stream->logs, (stream->nlogs + 1) * sizeof(log));
  stream->logs[stream->nlogs] = log;
  stream->nlogs++;

  return log;
}

static int log_close(struct script_control *ctl, struct script_log *log,
                     const char *msg, int status) {
  close_stream(log->fp);
  free(log->filename);
  memset(log, 0, sizeof(*log));

  return 0;
}

static int log_flush(struct script_control *ctl __attribute__((__unused__)),
                     struct script_log *log) {
  fflush(log->fp);
  return 0;
}

static void log_free(struct script_control *ctl, struct script_log *log) {
  for (size_t i = 0; i < ctl->out.nlogs; i++) {
    if (ctl->out.logs[i] == log) ctl->out.logs[i] = NULL;
  }
  for (size_t i = 0; i < ctl->in.nlogs; i++) {
    if (ctl->in.logs[i] == log) ctl->in.logs[i] = NULL;
  }
  free(log);
}

static int log_start(struct script_control *ctl, struct script_log *log) {
  /* open the log */
  log->fp = fopen(log->filename, "w");
  log->initialized = 1;
  return 0;
}

static int logging_start(struct script_control *ctl) {
  /* start all output logs */
  for (size_t i = 0; i < ctl->out.nlogs; i++) {
    log_start(ctl, ctl->out.logs[i]);
  }

  /* start all input logs */
  for (size_t i = 0; i < ctl->in.nlogs; i++) {
    log_start(ctl, ctl->in.logs[i]);
  }
  return 0;
}

static ssize_t log_write(struct script_control *ctl,
                         struct script_stream *stream, struct script_log *log,
                         char *obuf, size_t bytes) {
  fwrite_all(obuf, 1, bytes, log->fp);
  return bytes;
}

static ssize_t log_stream_activity(struct script_control *ctl,
                                   struct script_stream *stream, char *buf,
                                   size_t bytes) {
  ssize_t outsz = 0;

  for (size_t i = 0; i < stream->nlogs; i++) {
    log_write(ctl, stream, stream->logs[i], buf, bytes);
    outsz += bytes;
  }

  return outsz;
}

static ssize_t __attribute__((__format__(__printf__, 3, 4)))
log_signal(struct script_control *ctl, int signum, const char *msgfmt, ...) {
  return 0;
}

static void logging_done(struct script_control *ctl, const char *msg) {
  int status;

  if (WIFSIGNALED(ctl->childstatus))
    status = WTERMSIG(ctl->childstatus) + 0x80;
  else
    status = WEXITSTATUS(ctl->childstatus);

  /* close all output logs */
  for (size_t i = 0; i < ctl->out.nlogs; i++) {
    struct script_log *log = ctl->out.logs[i];
    log_close(ctl, log, msg, status);
    log_free(ctl, log);
  }
  free(ctl->out.logs);
  ctl->out.logs = NULL;
  ctl->out.nlogs = 0;

  /* close all input logs */
  for (size_t i = 0; i < ctl->in.nlogs; i++) {
    struct script_log *log = ctl->in.logs[i];
    log_close(ctl, log, msg, status);
    log_free(ctl, log);
  }
  free(ctl->in.logs);
  ctl->in.logs = NULL;
  ctl->in.nlogs = 0;
}

static void callback_child_die(void *data,
                               pid_t child __attribute__((__unused__)),
                               int status) {
  struct script_control *ctl = (struct script_control *)data;

  ctl->child = (pid_t)-1;
  ctl->childstatus = status;
}

static void callback_child_sigstop(void *data __attribute__((__unused__)),
                                   pid_t child) {
  kill(getpid(), SIGSTOP);
  kill(child, SIGCONT);
}

static int callback_log_stream_activity(void *data, int fd, char *buf,
                                        size_t bufsz) {
  struct script_control *ctl = (struct script_control *)data;
  ssize_t ssz = 0;

  /* from stdin (user) to command */
  if (fd == STDIN_FILENO)
    ssz = log_stream_activity(ctl, &ctl->in, buf, (size_t)bufsz);

  /* from command (master) to stdout and log */
  else if (fd == ctl->pty->master)
    ssz = log_stream_activity(ctl, &ctl->out, buf, (size_t)bufsz);

  if (ssz < 0) return (int)ssz;

  ctl->outsz += ssz;

  return 0;
}

static int callback_log_signal(void *data, struct signalfd_siginfo *info,
                               void *sigdata) {
  return 0;
}

static int callback_flush_logs(void *data) {
  struct script_control *ctl = (struct script_control *)data;

  for (size_t i = 0; i < ctl->out.nlogs; i++) {
    log_flush(ctl, ctl->out.logs[i]);
  }

  for (size_t i = 0; i < ctl->in.nlogs; i++) {
    log_flush(ctl, ctl->in.logs[i]);
  }

  return 0;
}

int main(int argc, char **argv) {
  struct script_control ctl = {
      .out = {.ident = 'O'},
      .in = {.ident = 'I'},
  };
  ctl.isterm = isatty(STDIN_FILENO);

  /* associate stdout with typescript file */
  log_associate(&ctl, &ctl.out, "typescript", SCRIPT_FMT_RAW);

  const char *shell = getenv("SHELL");

  ctl.pty = ul_new_pty(ctl.isterm);

  ctl.pty->slave_echo = 1;

  ctl.pty->callback_data = (void *)&ctl;
  struct ul_pty_callbacks *cb = &ctl.pty->callbacks;
  cb->child_die = callback_child_die;
  cb->child_sigstop = callback_child_sigstop;
  cb->log_stream_activity = callback_log_stream_activity;
  cb->log_signal = callback_log_signal;
  cb->flush_logs = callback_flush_logs;

  ul_pty_setup(ctl.pty);
  ul_pty_signals_setup(ctl.pty);
  fflush(stdout);

  /*
   * We have terminal, do not use err() from now, use "goto done"
   */

  switch ((int)(ctl.child = fork())) {
    case 0: /* child */
    {
      ul_pty_init_slave(ctl.pty);

      signal(SIGTERM, SIG_DFL); /* because /etc/csh.login */

      const char *shname = strrchr(shell, '/');
      shname = shname ? shname + 1 : shell;

      if (access(shell, X_OK) == 0) {
        execl(shell, shname, "-i", (char *)NULL);
      } else {
        execlp(shname, shname, "-i", (char *)NULL);
      }

      err(EXIT_FAILURE, "failed to execute %s", shell);
      break;
    }
    default:
      break;
  }

  /* parent */
  ctl.pty->child = ctl.child;

  logging_start(&ctl);

  /* this is the main loop */
  int rc = ul_pty_proxy_master(ctl.pty);

  /* all done; cleanup and kill */
  int caught_signal = ctl.pty->delivered_signal;

  if (!caught_signal && ctl.child != (pid_t)-1)
    ul_pty_wait_for_child(ctl.pty); /* final wait */

done:
  ul_pty_cleanup(ctl.pty);
  logging_done(&ctl, NULL);

  ul_free_pty(ctl.pty);

  /* default exit code */
  return rc ? EXIT_FAILURE : EXIT_SUCCESS;
}
