#ifndef ARCH_TYPES_H
#define ARCH_TYPES_H

typedef signed char int8_t;
typedef signed short int16_t;
typedef signed int int32_t;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;
/* fully typed log buffer size */
typedef uint8_t logsize_t;


#define KBYTE 1024
#define MBYTE 1048576
#define GBYTE 1073741824

#define NULL				((void *)0)

/* 32bits targets specific */
typedef uint32_t physaddr_t;

typedef unsigned int size_t;
typedef int ssize_t;

#endif/*!ARCH_TYPES_H*/
