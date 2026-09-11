#ifndef SMASSERT_H
#define SMASSERT_H

#ifndef SMRELEASSE 

#include <stdlib.h> //for exit(EXIT_FAILURE) maybe replace by builtin trap to from compilers to stop break execution.

void report_assertion_failure(const char *expr, const char *message, const char *file, int line); 

#define SMASSERT(expr)                                                 \
   {                                                                   \
        if (expr) {                                                    \
        } else {                                                       \
            report_assertion_failure(#expr, "", __FILE__, __LINE__);   \
            exit(EXIT_FAILURE);                                        \
        }                                                              \
    }

#define SMASSERT_MSG(expr, message)                                         \
   {                                                                        \
        if (expr) {                                                         \
        } else {                                                            \
            report_assertion_failure(#expr, message, __FILE__, __LINE__);   \
            exit(EXIT_FAILURE);                                             \
        }                                                                   \
    }

#ifdef _DEBUG
#define SMASSERT_DEBUG(expr)                                           \
   {                                                                   \
        if (expr) {                                                    \
        } else {                                                       \
            report_assertion_failure(#expr, "", __FILE__, __LINE__);   \
            exit(EXIT_FAILURE);                                        \
        }                                                              \
    }
#else 
#define SMASSERT_DEBUG(expr)  
#endif //_DEBUG

#else 
#define SMASSERT(expr)
#define SMASSERT_MSG(expr, message)
#define SMASSERT_DEBUG(expr)
#endif //SMRELEASE

#endif //SMASSERT_H
