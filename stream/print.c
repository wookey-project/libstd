#include "api/print.h"
#include "api/string.h"
#include "api/types.h"
#include "api/syscall.h"
#include "stream/print_priv.h"
#include "string/string_priv.h"


#define PUT_CHAR(c)					\
	ring_buffer.buf[ring_buffer.end] = c;		\
    if (((ring_buffer.end + 1) % BUF_MAX) != ring_buffer.start) {\
        ring_buffer.end++; \
        ring_buffer.end %= BUF_MAX; \
    }

/* not static because it is used */
static struct s_ring ring_buffer;

struct s_ring *stream_rb_get(void)
{
    return &ring_buffer;
}
/***********************************************
 * local utility functions
 **********************************************/

static void write_digit(uint8_t digit)
{
    if (digit < 0xa)
        digit += '0';
    else
        digit += 'a' - 0xa;
    PUT_CHAR(digit);
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


/***********************************************
 * libstream API implementation
 **********************************************/

static void print_and_reset_buffer(void)
{
    int i;

    if (ring_buffer.end > ring_buffer.start) {
        sys_log(ring_buffer.end - ring_buffer.start,
                &(ring_buffer.buf[ring_buffer.start]));
    } else if (ring_buffer.end < ring_buffer.start) {
        sys_log(BUF_SIZE - ring_buffer.start,
                &(ring_buffer.buf[ring_buffer.start]));
        sys_log(ring_buffer.end, &(ring_buffer.buf[0]));
    }
    ring_buffer.end = 0;
    ring_buffer.start = ring_buffer.end;

    for (i = 0; i < BUF_MAX; i++) {
        ring_buffer.buf[i] = '\0';
    }
}

/*
 * automatically called by do_starttask
 */
void init_ring_buffer(void)
{
    int i = 0;
    ring_buffer.end = 0;
    ring_buffer.start = ring_buffer.end;

    for (i = 0; i < BUF_MAX; i++) {
        ring_buffer.buf[i] = '\0';
    }
}


void print(char *fmt, va_list args)
{
    uint32_t i = 0;
    char *string;

    for (i = 0; fmt[i]; i++) {
        if (fmt[i] == '%') {
            i++;
            switch (fmt[i]) {
            case 'd':
                itoa(va_arg(args, uint32_t), 10);
                break;
            case 'x':
                PUT_CHAR('0');
                PUT_CHAR('x');
                itoa(va_arg(args, uint32_t), 16);
                break;
            case 'o':
                PUT_CHAR('0');
                PUT_CHAR('o');
                itoa(va_arg(args, uint32_t), 8);
                break;
            case '%':
                PUT_CHAR('%');
                break;
            case 's':
                string = va_arg(args, char *);
                copy_string(string, strlen(string));
                break;
            case 'l':
                if (fmt[i + 1] == 'l' && fmt[i + 2] == 'd') {
                    itoa(va_arg(args, unsigned long long), 10);
                    i += 2;
                } else if (fmt[i + 1] == 'd') {
                    itoa(va_arg(args, unsigned long), 10);
                    i++;
                }
                break;
            case 'c':
                PUT_CHAR((unsigned char)va_arg(args, int));
                break;
            default:
                PUT_CHAR('?');
            }
        } else if (fmt[i] == '\n' && fmt[i + 1] != '\r') {
            copy_string("\n\r", 2);
        } else {
            PUT_CHAR(fmt[i]);
        }
    }
}

/* asyncrhonous printf, for handlers */
void aprintf(char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    print(fmt, args);
    va_end(args);
}

void aprintf_flush(void)
{
    print_and_reset_buffer();
}

void printf(char *fmt, ...)
{
    va_list args;

    /*
     * if there is some asyncrhonous printf to pass to the kernel, do it
     * before execute the current printf command
     */
    print_and_reset_buffer();
    va_start(args, fmt);
    print(fmt, args);
    va_end(args);
    print_and_reset_buffer();
}


void hexdump(const uint8_t *bin, uint32_t len)
{
  for (uint32_t i = 0; i < len; i++) {
    printf("%x ", bin[i]);
    if (i % 16 == 0 && i != 0) {
      printf("\n");
    }
  }
  printf("\n");
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

void itoa(uint64_t value, uint8_t base)
{
    /* we define a local storage to hold the digits list
     * in any possible base up to base 2 (64 bits) */
    uint8_t number[64] = { 0 };
    int index = 0;

    for (; value / base != 0; value /= base) {
        number[index++] = value % base;
    }
    /* finishing with most significant unit */
    number[index++] = value % base;

    /* Due to the last 'index++', index is targetting the first free cell.
     * We make it points the last *used* cell instead */
    index--;

    /* now we can print out, starting with the most significant unit */
    for (; index >= 0; index--) {
        write_digit(number[index]);
    }
}


