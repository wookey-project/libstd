#include "api/print.h"
#include "api/string.h"
#include "api/types.h"
#include "api/syscall.h"
#include "stream/print_priv.h"
#include "string/string_priv.h"

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

