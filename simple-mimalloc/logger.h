#ifndef LOGGER_H
#define LOGGER_H

//for dprintf!? otherwise not in stdio
#define _GNU_SOURCE

#include <stdarg.h>
#include <stdio.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

#define LOG_WARN_ENABLED 1
#define LOG_INFO_ENABLED 1

#if SMRELEASE == 1
#define LOG_DEBUG_ENABLED 0
#define LOG_TRACE_ENABLED 0
#else
#define LOG_DEBUG_ENABLED 1
#define LOG_TRACE_ENABLED 1
#endif

typedef enum {
    LOG_LEVEL_FATAL = 0,
    LOG_LEVEL_ERROR = 1,
    LOG_LEVEL_WARN = 2,
    LOG_LEVEL_INFO = 3,
    LOG_LEVEL_DEBUG = 4,
    LOG_LEVEL_TRACE = 5
} LogLevel;

typedef enum {
    LOG_USE_STDERR,
    LOG_USE_LOGFILE
} LogTo;

int logger_init();

void _log_output(LogLevel level, const char* message, ...);

#define SMFATAL(...) _log_output(LOG_LEVEL_FATAL, ##__VA_ARGS__);

#ifndef SMERROR
#define SMERROR(...) _log_output(LOG_LEVEL_ERROR, ##__VA_ARGS__);
#endif

#if LOG_WARN_ENABLED == 1
#define SMWARN(...) _log_output(LOG_LEVEL_WARN, ##__VA_ARGS__);
#else
#define SMWARN(...)
#endif

#if LOG_INFO_ENABLED == 1
#define SMINFO(...) _log_output(LOG_LEVEL_INFO, ##__VA_ARGS__);
#else
#define SMINFO(...)
#endif

#if LOG_DEBUG_ENABLED == 1
#define SMDEBUG(...) _log_output(LOG_LEVEL_DEBUG, ##__VA_ARGS__);
#else
#define SMDEBUG(...)
#endif

#if LOG_TRACE_ENABLED == 1
#define SMTRACE(...) _log_output(LOG_LEVEL_TRACE, ##__VA_ARGS__);
#else
#define SMTRACE(...)
#endif

#endif //LOGGER_H
