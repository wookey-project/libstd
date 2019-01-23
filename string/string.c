#include "string.h"
#include "print.h"

#include "print_priv.h"


extern struct s_ring ring_buffer; /* hosted by libstd libstream print.c */

#define PUT_CHAR(c)					\
	stream_rb_get()->buf[stream_rb_get()->end++] = c;		\
	stream_rb_get()->end %= BUF_MAX;			\
	if (stream_rb_get()->end == stream_rb_get()->start) {	\
		stream_rb_get()->start++;			\
		stream_rb_get()->start %= BUF_MAX;		\
	}



uint32_t strlen(const char *s)
{
    uint32_t i = 0;
    while (*s) {
        i++;
        s++;
    }
    return i;
}

int      strcmp(const char *s1, const char *s2)
{
    if (!s1 && !s2) {
        return 0;
    }
    if (s1 && !s2) {
        return 1;
    }
    if (!s1 && s2) {
        return -1;
    }
    for (uint32_t i = 0; s1[i] != '\0' && s2[i] != '\0'; ++i) {
        if (s1[i] == s2[i]) {
            continue;
        } else if (s1[i] > s2[i]) {
            return 1;
        } else {
            return -1;
        }
    }
    return 0;
}

char *strncpy(char *dest, const char *src, uint32_t n)
{
    char *return_value = dest;

    while (n && *src) {
        *dest = *src;
        dest++;
        src++;
        n--;
    }

    while (n) {
        *dest = '\0';
        dest++;
        n--;
    }

    return return_value;
}

static void write_digit(uint8_t digit)
{
    if (digit < 0xa)
        digit += '0';
    else
        digit += 'a' - 0xa;
    PUT_CHAR(digit);
}

void itoa(unsigned long long value, uint8_t base)
{
    if (value / base == 0) {
        write_digit(value % base);
    } else {
        itoa(value / base, base);
        write_digit(value % base);
    }
}

void copy_string(char *str, uint32_t len)
{
    uint32_t size =
        len < (BUF_MAX - stream_rb_get()->end) ? len : BUF_MAX - stream_rb_get()->end;
    strncpy(stream_rb_get()->buf + stream_rb_get()->end, str, size);
    uint32_t dist = stream_rb_get()->start - stream_rb_get()->end;
    if (stream_rb_get()->end < stream_rb_get()->start && dist < size) {
        stream_rb_get()->start += size - dist + 1;
        stream_rb_get()->start %= BUF_MAX;
    }
    stream_rb_get()->end += size;
    stream_rb_get()->end %= BUF_MAX;
    if (len - size)
        copy_string(str + size, len - size);
}

uint32_t sprintf(char *dst, uint16_t len, char *fmt, ...)
{
    va_list args;
    uint32_t sizew = 0;

    va_start(args, fmt);
    print(fmt, args);
    va_end(args);
    if (stream_rb_get()->end < len) {
      sizew = stream_rb_get()->end;
    } else {
      sizew = len - 1;
    }
    memcpy(dst, &(stream_rb_get()->buf[stream_rb_get()->start]), sizew);
    dst[sizew] = '\0';

    stream_rb_get()->end = 0;
    stream_rb_get()->start = stream_rb_get()->end;
    for (uint16_t i = 0; i < BUF_MAX; i++) {
        stream_rb_get()->buf[i] = '\0';
    }
    return sizew + 1;
}


