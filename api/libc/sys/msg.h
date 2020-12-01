/*
 *
 * copyright 2018 the wookey project team <wookey@ssi.gouv.fr>
 *   - ryad     benadjila
 *   - arnauld  michelizza
 *   - mathieu  renard
 *   - philippe thierry
 *   - philippe trebuchet
 *
 * this package is free software; you can redistribute it and/or modify
 * it under the terms of the gnu lesser general public license as published
 * the free software foundation; either version 2.1 of the license, or (at
 * ur option) any later version.
 *
 * this package is distributed in the hope that it will be useful, but without any
 * warranty; without even the implied warranty of merchantability or fitness for a
 * particular purpose. see the gnu lesser general public license for more details.
 *
 * you should have received a copy of the gnu lesser general public license along
 * with this package; if not, write to the free software foundation, inc., 51
 * franklin st, fifth floor, boston, ma 02110-1301 usa
 *
 */
#ifndef SYS_MSG_H_
#define SYS_MSG_H_
/*
 * This is a ligthway, high performance implementation of the POSIX message passing service.
 * There is, by now, no effective userspace queueing but only kernel queueing and IPC handling.
 * The goal here is to abstract the EwoK kernel IPC complexity into a user-friendly interface
 * without reducing their performances.
 *
 * Although, for a more intelligent message passing mechanism (i.e. effective userspace bus)
 * check the liberpes (RPC implementation) instead.
 */


#include "autoconf.h"
#include "libc/sys/types.h"

#ifdef CONFIG_STD_SYSV_MSQ

/* messaging mode */
#define MSG_NOERROR    010000 /* truncate silently message if too long */
#define MSG_EXCEPT     020000 /* recv any msg excepting specifyed type */
#define MSG_COPY       040000 /* copy instead of removing queued msg (NOT SUPPORTED) */

#define IPC_CREAT	01000		/* Create key if key does not exist. */
#define IPC_EXCL	02000		/* Fail if key exists.  */
#define IPC_NOWAIT	04000		/* Do not wait, return with EAGAIN flag in case of error */

/* generic IPC key_t for EwoK IPC (remote task name) */
typedef char const * key_t;

/**/
typedef union {
    char       c[64];
    uint8_t   u8[64];
    uint16_t u16[32];
    uint32_t u32[16];
    uint64_t u64[8];
} msg_mtext_union_t;

/* Here, we hold a word-aligned structure in order to avoid
 * any unaligned access to mtex fields for u32 & u64 types.
 * The difference with the POSIX type is the mtext definition,
 * in order to simplify the content typing. Though, mtype handling
 * is the same:
 * msgsnd() must send typed messages (i.e. data containing a mtype field
 * in its first 4 bytes)
 * msgrcv() get back the mtext content directly, without the mtype field,
 * as the type is requested in argument.
 *
 * The message queue handles messages while not requested by msgrcv() in a
 * local cache.
 * Usual SysV message flags (see above) can be used to modify the API behavior
 * w. respect for the POSIX standard. */
struct msgbuf {
    long mtype;
    msg_mtext_union_t mtext;
} __attribute__((packed));

/*
 * As the following API tries to be rspectful of the POSIX API, return codes and arguments do
 * not used embedded oriented types (typically mbed_error_t and so on).
 */

/*
 * Get back queue identifier from given key
 *
 * Typical usage:
 *
 * initial get in init mode:
 *
 * msgget("task", IPC_CREAT | IPC_EXCL);
 *
 * other gets, in nominal mode:
 *
 * msgget("task");
 */
int msgget(key_t key, int msgflg);

/*
 * Send a message to the given queue
 *
 * sending a message without blocking
 * msgsnd(qid, buf, msize, IPC_NOWAIT);
 */
int msgsnd(int msqid, const void *msgp, size_t msgsz, int msgflg);

/*
 * Receive a message from the given queue
 *
 * Receive a message in buf of any type but MAGIC_TYPE_X, that can be truncated
 * if its size is bigger than msgsz, without blocking (EAGAIN in case of nothing to read).
 *
 * msgrcv(qid, buf, msgsz, MAGIC_TYPE_X, IPC_NOWAIT| MSG_NOERROR|MSG_EXCEPT);
 *
 * Receive a message of type MAGIC_TYPE_Y only, that can't be truncated.
 * Blocks if no corresponding message upto cache full (in that case return with ENOMEM).
 * If a message of the corresponding type exists but is too big, return with E2BIG.
 *
 * msgrcv(qid, bug, msgsz, MAGIC_TYPE_Y, 0);
 *
 */
ssize_t msgrcv(int msqid, void *msgp, size_t msgsz, long msgtyp,
               int msgflg);

#endif/*!CONFIG_STD_SYSV_MSQ*/

#endif/*!SYS_MSG_H_*/
