#include "api/print.h"
#include "api/string.h"
#include "api/types.h"
#include "api/syscall.h"
#include "stream/stream_priv.h"
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

