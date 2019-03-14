#include "api/print.h"
#include "api/string.h"
#include "api/types.h"
#include "api/syscall.h"
#include "stream/print_priv.h"
#include "string/string_priv.h"


/***********************************************
 * local utility functions
 **********************************************/

/*
 * Stdio functions (*printf) use a local ring buffer
 * to hold formated content before sending it to the
 * kernel via the kernel log API (typically sys_log()
 * for EwoK).
 * This ring buffer is holded in the libstd as a global
 * variable, local to this very file.
 * The ring buffer is initialized by the libstd at
 * application boot time, as the libstd is managing the
 * application starting point, including the ring buffer
 * and stack canaries initialization in the do_starttask()
 * function.
 *
 * All the ring-buffer associated function, used only by
 * the stdio functions, are implemented here.
 */


/*
 * Here is the effective global holding the ring buffer.
 * The ring buffer is local to this object file only.
 */
static struct s_ring ring_buffer;

/*
 * the ring buffer is a part of bss (not data, making it
 * useless in flash, reducing the task flash consumption).
 *
 * As a consequence, it has to be initialized at boot time.
 * This is done by this function, called by do_starttask().
 */
void init_ring_buffer(void)
{
    /* init flags */
    int i = 0;
    ring_buffer.end = 0;
    ring_buffer.start = ring_buffer.end;
    ring_buffer.full = false;

    /* memsetting buffer
     * NOTE: This may be useless as, in EwoK, the BSS is zeroified
     * at boot time.
     */
    for (i = 0; i < BUF_MAX; i++) {
        ring_buffer.buf[i] = '\0';
    }
}

/*
 * add a char in the ring buffer.
 *
 * INFO: by now, there is no bound check here. As a consequence, if
 * the ring buffer is full,
 *
 * WARNING: this function is the only one holding the ring buffer full
 * flag detection. As a consequence, any write access to the ring buffer
 * must be done through this function *exclusively*.
 */
volatile void ring_buffer_put_char(const char c)
{
    /* if the ring buffer is full when we try to put char in it,
     * the car is discared, waiting for the ring buffer to be flushed.
     */
    if (ring_buffer.full) {
        goto end;
    }
	ring_buffer.buf[ring_buffer.end] = c;
    if (((ring_buffer.end + 1) % BUF_MAX) != ring_buffer.start) {
        ring_buffer.end++;
        ring_buffer.end %= BUF_MAX;
    } else {
        /* full buffer detection */
        ring_buffer.full = true;
    }
end:
    return;
}

/*
 * Write a digit to the ring buffer.
 * This function convert a basic digit into a printable one.
 *
 * This function support usual bases such as binary
 *
 * INFO: this function can write digits in base up to hexadecimal one.
 * Bases bigger than hex are not supported.
 *
 */
void ring_buffer_write_digit(uint8_t digit)
{
    if (digit < 0xa) {
        digit += '0';
        ring_buffer_put_char(digit);
    } else if (digit <= 0xf) {
        digit += 'a' - 0xa;
        ring_buffer_put_char(digit);
    }
}

/*
 * copy a string to the ring buffer. This is an abstraction of the
 * ring_buffer_put_char() function.
 */
void ring_buffer_copy_string(char *str, uint32_t len)
{
    if (!str) {
        goto end;
    }
    for (uint32_t i = 0; i < len && str[i]; ++i) {
        ring_buffer_put_char(str[i]);
    }
end:
    return;
}


void print_and_reset_buffer(void)
{

    /* there is two cases here:
     *    * end is after start in the ring buffer. This means that
     *      all the string chars are contigous and can be printed once
     *    * start is after end, the string must be printed in two
     *      sections
     */
    if (ring_buffer.end > ring_buffer.start) {
        sys_log(ring_buffer.end - ring_buffer.start,
                &(ring_buffer.buf[ring_buffer.start]));
    } else if (ring_buffer.end < ring_buffer.start) {
        sys_log(BUF_SIZE - ring_buffer.start,
                &(ring_buffer.buf[ring_buffer.start]));
        sys_log(ring_buffer.end, &(ring_buffer.buf[0]));
    }
    /* reset the ring buffer flags now that the content has been
     * sent to the kernel I/O API
     */
    ring_buffer.end = 0;
    ring_buffer.start = ring_buffer.end;
    ring_buffer.full = false;

    for (uint32_t i = 0; i < BUF_MAX; i++) {
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
                ring_buffer_put_char('0');
                ring_buffer_put_char('x');
                itoa(va_arg(args, uint32_t), 16);
                break;
            case 'o':
                ring_buffer_put_char('0');
                ring_buffer_put_char('o');
                itoa(va_arg(args, uint32_t), 8);
                break;
            case '%':
                ring_buffer_put_char('%');
                break;
            case 's':
                string = va_arg(args, char *);
                ring_buffer_copy_string(string, strlen(string));
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
                ring_buffer_put_char((unsigned char)va_arg(args, int));
                break;
            default:
                ring_buffer_put_char('?');
            }
        } else if (fmt[i] == '\n' && fmt[i + 1] != '\r') {
            ring_buffer_copy_string("\n\r", 2);
        } else {
            ring_buffer_put_char(fmt[i]);
        }
    }
}


/***********************************************
 * libstream API implementation
 **********************************************/

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


uint32_t sprintf(char *dst, uint16_t len, char *fmt, ...)
{
    va_list args;
    uint32_t sizew = 0;

    va_start(args, fmt);
    print(fmt, args);
    va_end(args);
    if (ring_buffer.end < len) {
      sizew = ring_buffer.end;
    } else {
      sizew = len - 1;
    }
    memcpy(dst, &(ring_buffer.buf[ring_buffer.start]), sizew);
    dst[sizew] = '\0';

    ring_buffer.end = 0;
    ring_buffer.start = ring_buffer.end;
    for (uint16_t i = 0; i < BUF_MAX; i++) {
        ring_buffer.buf[i] = '\0';
    }
    return sizew + 1;
}


