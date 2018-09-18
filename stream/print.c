#include "api/print.h"
#include "api/types.h"
#include "api/syscall.h"
#include "stream/print_priv.h"
#include "string/string_priv.h"
#include "kernel/exported/syscalls.h"

#define PUT_CHAR(c)					\
	ring_buffer.buf[ring_buffer.end++] = c;		\
	ring_buffer.end %= BUF_MAX;			\
	if (ring_buffer.end == ring_buffer.start) {	\
		ring_buffer.start++;			\
		ring_buffer.start %= BUF_MAX;		\
	}

static const char *strerror_tab[4] = {
    "Done", //"Done: Syscall finished successfully",
    "Inval", //"Inval: user informations are not valid",
    "Denied", //"Denied: not the good time or access prohibed",
    "Busy", //"Busy: already used or not enough space to use",
};

/* not static because it is used */
static struct s_ring ring_buffer;

struct s_ring *stream_rb_get(void)
{
    return &ring_buffer;
}

const char *strerror(uint8_t ret)
{
    if (ret < SYS_E_MAX) {
        return strerror_tab[ret];
    }
    return 0;
}

static void print_and_reset_buffer(void)
{
    int i;
    if (ring_buffer.end > ring_buffer.start) {
        sys_ipc(IPC_LOG, ring_buffer.end - ring_buffer.start,
                &(ring_buffer.buf[ring_buffer.start]));
    } else if (ring_buffer.end <= ring_buffer.start) {
        sys_ipc(IPC_LOG, BUF_SIZE - ring_buffer.start,
                &(ring_buffer.buf[ring_buffer.start]));
        sys_ipc(IPC_LOG, ring_buffer.end, &(ring_buffer.buf[0]));
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

void *memset(void *s, int c, uint32_t n)
{
    char *bytes = s;
    while (n) {
        *bytes = c;
        bytes++;
        n--;
    }
    return s;
}

void *memcpy(void *dest, const void *src, uint32_t n)
{
    char *d_bytes = dest;
    const char *s_bytes = src;

    while (n) {
        *d_bytes = *s_bytes;
        d_bytes++;
        s_bytes++;
        n--;
    }

    return dest;
}

int memcmp(const void *s1, const void *s2, int n)
{
    unsigned char u1, u2;

    for (; n--; s1++, s2++) {
        u1 = *(unsigned char *)s1;
        u2 = *(unsigned char *)s2;
        if (u1 != u2) {
            return (u1 - u2);
        }
    }

    return 0;
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

void printf(char *fmt, ...)
{
    va_list args;

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
