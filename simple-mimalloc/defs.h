#ifndef DEFS_H
#define DEFS_H

#include <stdint.h>   //for usefull integer types
#include <inttypes.h> //for safe printing and scanning PRIu8 etc
#include <stddef.h>   //for size_t and uintptr_t assertions
#include <stdbool.h>

#define internal        static 
#define local_persist   static 
#define global_persist  static 

typedef unsigned char      u8;
typedef unsigned short     u16;
typedef unsigned int       u32;
typedef unsigned long long u64;

typedef signed char        i8;
typedef signed short       i16;
typedef signed int         i32;
typedef signed long long   i64;

typedef float              f32;
typedef double             f64;

#define U8_MAX  UINT8_MAX
#define U16_MAX UINT16_MAX
#define U32_MAX UINT32_MAX
#define U64_MAX UINT64_MAX

#define I8_MAX  INT8_MAX
#define I16_MAX INT16_MAX
#define I32_MAX INT32_MAX
#define I64_MAX INT64_MAX

#define I8_MIN  INT8_MIN
#define I16_MIN INT16_MIN
#define I32_MIN INT32_MIN
#define I64_MIN INT64_MIN

#define U8_MIN  0U
#define U16_MIN 0U
#define U32_MIN 0U
#define U64_MIN 0UL

#define STATIC_ASSERT(cond, name) typedef char static_assert_##name[(cond)?1:-1]

//NOTE: changed allocators to use size_t, so assert no longer necessary, but I do work with this assumption in mind 
STATIC_ASSERT(sizeof(size_t) >= sizeof(u64), sizet_at_least_as_big_as_u64);

//NOTE: Very important the offset based arena relies on this, I think in general a lot of code does!
STATIC_ASSERT(sizeof(size_t) >= sizeof(uintptr_t), sizet_at_least_as_big_as_uintptr_t);

//TODO(Ben): think of something: no portable way for max alignment using c99
//maybe write the allocators using from the (raw) pointers and not offset based then this is not that relevant
//using c11 -> #define MAX_ALIGNMENT _Alignof(max_align_t)
//a good heuristic one in c99 is #define MAX_ALIGNMENTN sizeof(long double) 

#endif //DEFS_H
