#include "logger.h"
#include "assert.h"

static int log_fd;

static void logger_clean () {
    close(log_fd);
}

int logger_init (LogTo to) {
    switch (to) {
        case LOG_USE_STDERR:
            log_fd = STDERR_FILENO;
            break;
        case LOG_USE_LOGFILE:
            log_fd = open("./log.txt", O_WRONLY | O_CREAT | O_TRUNC, 0600);
            if (log_fd == -1) return 0;
            atexit(logger_clean);
            break;
    }
    return 1;
}

void report_assertion_failure(const char* expression, const char* message, const char* file, int line) {
    _log_output(LOG_LEVEL_FATAL, "Assertion Failure: %s, message: '%s', %s:%d\n", expression, message, file, line);
}

void _log_output(LogLevel level, const char* message, ...) {
    const char* level_strs[6] = {"[FATAL]: ", "[ERROR]: ", "[WARN]:  ", "[INFO]:  ", "[DEBUG]: ", "[TRACE]: "};
    static char buffer[2000];

    __builtin_va_list arg_ptr; //va_list would work, but not on windows..
    va_start(arg_ptr, message);
    vsnprintf(buffer, 2000, message, arg_ptr);
    va_end(arg_ptr);

    dprintf(log_fd, "%s%s", level_strs[level], buffer);
}
