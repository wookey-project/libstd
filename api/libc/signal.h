/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef SIGNAL_H_
#define SIGNAL_H_

#include "autoconf.h"
#include "libc/types.h"

/* Future for multithreads compatible sigev structure */
#define __SIGEV_MAX_SIZE	64
#if __WORDSIZE == 64
# define __SIGEV_PAD_SIZE	((__SIGEV_MAX_SIZE / sizeof (int)) - 4)
#else
# define __SIGEV_PAD_SIZE	((__SIGEV_MAX_SIZE / sizeof (int)) - 3)
#endif

enum
{
  SIGEV_SIGNAL = 0,		/* Notify via POSIX signal, not supported by libstd (no signal in EwoK */
  SIGEV_NONE,			/* Pure userspace handling, timer polling only */
  SIGEV_THREAD 			/* execute given handler at timer terminaison */
};

union sigval
{
  int sival_int;
  void *sival_ptr;
};

typedef union sigval __sigval_t;


/*
 * Simplified, yet POSIX sigevent_t. No support for pid_t
 */
typedef struct sigevent {
    __sigval_t sigev_value;
    int sigev_signo;
    int sigev_notify;
    void (*sigev_notify_function)(__sigval_t);
} sigevent_t;


#endif/*!SIGNAL_H_*/
