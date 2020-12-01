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


/* messaging mode */
#define MSG_NOERROR    010000 /* truncate silently message if too long */
#define MSG_EXCEPT     020000 /* recv any msg excepting specifyed type */
#define MSG_COPY       040000 /* copy instead of removing queued msg (NOT SUPPORTED) */

#define IPC_CREAT	01000		/* Create key if key does not exist. */
#define IPC_EXCL	02000		/* Fail if key exists.  */
#define IPC_NOWAIT	04000		/* Do not wait, return with EAGAIN flag */

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
 * any unaligned access to mtex fields for u32 & u64 types */
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
 */
int msgsnd(int msqid, const void *msgp, size_t msgsz, int msgflg);

/*
 * Receive a message from the given queue
 */
ssize_t msgrcv(int msqid, void *msgp, size_t msgsz, long msgtyp,
               int msgflg);

#endif/*!SYS_MSG_H_*/
