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

/*
 * This is a ligthway, high performance implementation of the POSIX message passing service.
 * There is, by now, no effective userspace queueing but only kernel queueing and IPC handling.
 * The goal here is to abstract the EwoK kernel IPC complexity into a user-friendly interface
 * without reducing their performances.
 *
 * Although, for a more intelligent message passing mechanism (i.e. effective userspace bus)
 * check the liberpes (RPC implementation) instead.
 */


#include "libc/stdio.h"
#include "libc/stdint.h"
#include "libc/sys/msg.h"
#include "libc/syscall.h"
#include "libc/types.h"
#include "libc/errno.h"
#include "libc/string.h"

#include "errno.h"

/* TODO: this must be associated to the kernel max IPC msg size, not hard-coded */
#define MAX_IPC_MSG_SIZE 128
#define MSG_MAX_DEPTH 2

/* A message received by the kernel genuine type is char*. Though, its effective type here is struct msgbuf.
 * We use an union for clean cast. */
typedef union {
  struct msgbuf msgbuf;
  char          ewok_msg[MAX_IPC_MSG_SIZE];
} qsmsg_msgbuf_data_t;

typedef struct {
  qsmsg_msgbuf_data_t msg;
  uint8_t             msg_size;
  bool                set;
} qmsg_msgbuf_t;

typedef struct {
    bool    set;
    key_t   key;
    uint8_t id;
    uint32_t msg_lspid; /* for broadcasting recv queue, id of the last sender */
#if 0
    uint32_t msg_qnum; /* number of msg in queue. With EwoK IPC, only one msg at a time */
#endif
    uint16_t      msg_perm; /* queue permission, used for the broadcast recv queue case (send forbidden) */
    uint32_t      msg_stime; /* time of last snd event */
    uint32_t      msg_rtime; /* time of last rcv event */
    qmsg_msgbuf_t msgbuf_v[MSG_MAX_DEPTH];
    uint8_t       msgbuf_ent;
} qmsg_entry_t;

/*
 * list of all msg queues. If key == 0, the message queue is not initalised.
 */
static qmsg_entry_t qmsg_vector[CONFIG_MAXTASKS+1] = { 0 };

/*
 * POSIX message passing API
 */
int msgget(key_t key, int msgflg)
{
    /* POSIX compliant */
    int errcode;
    uint8_t syserr;

    /* by now, we use task identifier as queue identifier, as queues are monodirectional pipes
     * between current task and the target task identifier */
    uint8_t tid;

    /*
     * 1. Is there a previously cached qmsg id for the given key ?
     */
    /*@
      @ loop invariant \valid_read(qmsg_vector[0..CONFIG_MAXTASKS]);
      @ loop invariant 0 <= i <= CONFIG_MAXTASKS+1;
      @ loop assigns i;
      @ loop variant ((CONFIG_MAXTASKS+1) - errcode);
      */
    for (uint8_t i = 0; i <= CONFIG_MAXTASKS; ++i) {
        if (qmsg_vector[i].key == key && qmsg_vector[i].set == true) {
            if (msgflg & IPC_EXCL) {
                /* fails if key exists */
                errcode = -1; /* POSIX Compliance */
                __libstd_set_errno(EEXIST);
            } else {
                errcode = qmsg_vector[i].id;
            }
            goto err;
        }
    }

    /*
     * 2. No cache entry found. Try to get back the id from the kernel, and cache it
     */
    if (!(msgflg & IPC_CREAT)) {
        /* no cache entry found but cache entry creation **not** requested */
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(ENOENT);
        goto err;
    }
    if (key == NULL) {
        tid = CONFIG_MAXTASKS;
        /* requesting queue for broadcast, recv only in that case. For this, we
         * use the POSIX DAC permission to lock snd() requests */
        qmsg_vector[tid].key = key;
        qmsg_vector[tid].id = 0xff; /* EwoK identifier for broadcast */
        qmsg_vector[tid].msg_perm = 0x444; /*recv() only (RO) */
        qmsg_vector[tid].msg_stime = 0;
        qmsg_vector[tid].msg_rtime = 0;
        qmsg_vector[tid].set = true;
        errcode = tid;
        goto err;
    }

    /* Here, the qmsg has not yet been declared, request the id from the kernel (i.e. the remote task id) */
    /*@ assert \valid_read(key); */
    syserr = sys_init(INIT_GETTASKID, (char*)key, &tid);
    switch (syserr) {
        case SYS_E_INVAL:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EINVAL);
            goto err;
            break;
        case SYS_E_DENIED:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EACCES);
            goto err;
            break;
        case SYS_E_DONE:
            break;
        default:
            /* abnormal other return code, should not happen */
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EINVAL);
            goto err;
            break;
    }
    /* On successful remote task id load, return remote taskid as qmsg identifier */
    /*@ assert tid < CONFIG_MAXTASKS; */
    qmsg_vector[tid].key = key;
    qmsg_vector[tid].id = tid;
    qmsg_vector[tid].msg_perm = 0x666; /* unicast communication. Permission is handled by kernel */
    qmsg_vector[tid].msg_stime = 0;
    qmsg_vector[tid].msg_rtime = 0;
    qmsg_vector[tid].set = true;
    errcode = tid;
err:
    return errcode;
}

/*
 * Sending message msgp of size msgsz to 'msqid'.
 */
int msgsnd(int msqid, const void *msgp, size_t msgsz, int msgflg)
{
    int errcode = -1;
    uint8_t ret;

    if (msgp == NULL) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EFAULT);
        goto err;
    }
    if (msqid < 0 || msqid > CONFIG_MAXTASKS) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EINVAL);
        goto err;
    }
    if (qmsg_vector[msqid].set == false) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EINVAL);
        goto err;
    }
    if (msgsz > MAX_IPC_MSG_SIZE) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(E2BIG);
        goto err;
    }
    if (qmsg_vector[msqid].msg_perm == 0x444) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EPERM);
        goto err;
    }

    if (msgflg & IPC_NOWAIT) {
        ret = sys_ipc(IPC_SEND_ASYNC, msqid, msgsz, (const char*)msgp);
    } else {
        ret = sys_ipc(IPC_SEND_SYNC, msqid, msgsz, (const char*)msgp);
    }
    switch (ret) {
        case SYS_E_INVAL:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EINVAL);
            goto err;
            break;
        case SYS_E_DENIED:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EACCES);
            goto err;
            break;
        case SYS_E_BUSY:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EAGAIN);
            goto err;
        case SYS_E_DONE:
            break;
        default:
            /* abnormal other return code, should not happen */
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EINVAL);
            goto err;
            break;
    }
    /* default on success */
    errcode = 0;
err:
    return errcode;
}

/*
 * msgrcv return in msgp the content of mtext[]. The mtype field is ignored
 * as used as a discriminant for message selection purpose.
 * Although, as msgsnd()/msgrcv() API is **not** a kernel API, the received
 * buffer content the overall data (including mtype), as the kernel as no
 * idea of the msgbuf structure.
 *
 * As a consequence, we can't recv the content directly in msgp, as msgp
 * (and msgz) may be too short to recv the buffer including the mtype.
 *
 * A possible way, here is to:
 * - if the local msgbuf vector is full and mtype does not match any of the
 *   stored message, returns ENOMEM
 * - check the local msgbuf vector if there is a pending message with the
 *   corresponding mtype. If yes, returns it.
 * - If not, get back 'something' from the kernel (what sys_ipc(IPC_RECV_XXX)
 *   gave back and:
 *      * if the mtype flags match the msgtyp argument, copy back the mtext content
 *        to msgp
 *      * if the mtype flag does not match the msgtyp argument, store the overall
 *        msgbuf content localy to a msgbuf vector, and:
 *          -> if IPC_NOWAIT is not set, try agin
 *          -> in IPC_NOWAIT is set, return EGAIN.
 */
ssize_t msgrcv(int msqid,
               void *msgp,
               size_t msgsz,
               long msgtyp,
               int msgflg)
{
    int errcode = -1;
    uint8_t ret;
    uint8_t tid = qmsg_vector[msqid].id;
    logsize_t rcv_size;
    uint8_t i = 0;
    uint8_t free_cell = 0;

    /* sanitation */
    if (msgp == NULL) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EFAULT);
        goto err;
    }
    if (msqid < 0 || msqid > CONFIG_MAXTASKS) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EINVAL);
        goto err;
    }
    if (qmsg_vector[msqid].set == false) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EINVAL);
        goto err;
    }
    if (qmsg_vector[msqid].msg_perm == 0x444) {
        errcode = -1; /* POSIX Compliance */
        __libstd_set_errno(EPERM);
        goto err;
    }

tryagain:

    /* check local previously stored messages */
    for (i = 0; i < MSG_MAX_DEPTH; ++i) {
        if (qmsg_vector[msqid].msgbuf_v[i].set == true) {
            /* no EXCEPT mode, try to match msgtyp */
            if ((msgflg & MSG_EXCEPT) && (qmsg_vector[msqid].msgbuf_v[i].msg.msgbuf.mtype != msgtyp)) {
                /* found a waiting msg for except mode */
                if (qmsg_vector[msqid].msgbuf_v[i].msg_size > msgsz && !(msgflg & MSG_NOERROR)) {
                    /* truncate not allowed!*/
                    errcode = -1;
                    __libstd_set_errno(E2BIG);
                    goto err;
                }
                goto handle_cached_msg;

            } else if (!(msgflg & MSG_EXCEPT) && (qmsg_vector[msqid].msgbuf_v[i].msg.msgbuf.mtype == msgtyp)) {
                /* found a waiting msg with corresponding type */
                if (qmsg_vector[msqid].msgbuf_v[i].msg_size > msgsz && !(msgflg & MSG_NOERROR)) {
                    /* truncate not allowed!*/
                    errcode = -1;
                    __libstd_set_errno(E2BIG);
                    goto err;
                }
                goto handle_cached_msg;
            }
        } else {
            free_cell = i;
        }
    }
    /* no cached message found ? if msgbuf_vector is full, NOMEM */
    if (qmsg_vector[msqid].msgbuf_ent == MSG_MAX_DEPTH) {
        errcode = -1;
        __libstd_set_errno(ENOMEM);
        goto err;
    }
    /* here, free_cell should have been set at least one time, or the execution derivated to
     * handle_cached_msg. we can use free_cell as cell id for next sys_ipc() call  */

    if (msgflg & MSG_NOERROR) {
        /* we can truncate what we received */
        rcv_size = 128;
    } else {
        /* or not */
        rcv_size = msgsz + sizeof(long);
    }

    /* get back message content from kernel */
    if (msgflg & IPC_NOWAIT) {
        ret = sys_ipc(IPC_RECV_ASYNC, &tid, &rcv_size, &(qmsg_vector[msqid].msgbuf_v[free_cell].msg.ewok_msg[0]));
    } else {
        ret = sys_ipc(IPC_RECV_SYNC, &tid, &rcv_size, &(qmsg_vector[msqid].msgbuf_v[free_cell].msg.ewok_msg[0]));
    }
    switch (ret) {
        case SYS_E_INVAL:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EINVAL);
            goto err;
            break;
        case SYS_E_DENIED:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EACCES);
            goto err;
            break;
        case SYS_E_BUSY:
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EAGAIN);
            goto err;
        case SYS_E_DONE:
            break;
        default:
            /* abnormal other return code, should not happen */
            errcode = -1; /* POSIX Compliance */
            __libstd_set_errno(EINVAL);
            goto err;
            break;
    }
    /* set recv msg size, removing the mtype field size */
    qmsg_vector[msqid].msgbuf_v[free_cell].msg_size = rcv_size - sizeof(long);
    qmsg_vector[msqid].msgbuf_ent++;

    /* Now that the buffer received. Check its content. Here, like for cache check, we must check
     * mtype according to msgflg */
    if ((msgflg & MSG_EXCEPT) && (qmsg_vector[msqid].msgbuf_v[free_cell].msg.msgbuf.mtype != msgtyp)) {
        /* if this message matches, check for its size, according to MSG_NOERROR flag */
        if (qmsg_vector[msqid].msgbuf_v[free_cell].msg_size > msgsz && !(msgflg & MSG_NOERROR)) {
            /* truncate not allowed!*/
            qmsg_vector[msqid].msgbuf_v[free_cell].set = true;
            errcode = -1;
            __libstd_set_errno(E2BIG);
            goto err;
        }
        i = free_cell;
        goto handle_cached_msg;


    } else if (!(msgflg & MSG_EXCEPT) && (qmsg_vector[msqid].msgbuf_v[free_cell].msg.msgbuf.mtype == msgtyp)) {
        /* if this message matches, check for its size, according to MSG_NOERROR flag */
        if (qmsg_vector[msqid].msgbuf_v[free_cell].msg_size > msgsz && !(msgflg & MSG_NOERROR)) {
            /* truncate not allowed!*/
            qmsg_vector[msqid].msgbuf_v[free_cell].set = true;
            errcode = -1;
            __libstd_set_errno(E2BIG);
            goto err;
        }
        i = free_cell;
        goto handle_cached_msg;
    }

    /* message doesn't match at all... cache it for next time */
    qmsg_vector[msqid].msgbuf_v[free_cell].set = true;
    qmsg_vector[msqid].msgbuf_ent++;

    /* is the queue full now ? */

    /* In the case of msgflag without IPC_NOWAIT, if the message of type mtype is not found
     * (i.e. we arrived here), we try again, until the queue is full. */
    if (msgflg & IPC_NOWAIT) {
        errcode = -1;
        __libstd_set_errno(EAGAIN);
        goto err;
    } else {
        goto tryagain;
    }

    /* default on success */
err:
    return errcode;

    /* handle found cached message or just received message */
handle_cached_msg:
    rcv_size = (msgsz < qmsg_vector[msqid].msgbuf_v[i].msg_size) ? msgsz : qmsg_vector[msqid].msgbuf_v[i].msg_size;
    memcpy(msgp, &(qmsg_vector[msqid].msgbuf_v[i].msg.msgbuf.mtext.u8[0]), rcv_size);
    qmsg_vector[msqid].msgbuf_ent--;
    qmsg_vector[msqid].msgbuf_v[i].set = false;
    return rcv_size;
}
