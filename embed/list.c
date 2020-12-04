#include "libc/types.h"
#include "libc/list.h"
#include "libc/stdio.h"
#include "libc/semaphore.h"

/* FIXME: get_current_ctx_id() should not be there */
#include "arch/cores/armv7-m/m4_syscall.h"

/*
 * ordered list implementation, basic
 * This is the only function that does not requires a HEAP (no malloc).
 */
mbed_error_t list_create(uint32_t capacity, list_t *l)
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* sanitizing */
    if (!l) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (capacity > MAX_LIST_DEPTH) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (capacity == 0) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

#if LIST_DEBUG
    printf("list address is %x\n", l);
#endif
    /* initializing */
    l->head = NULL;
    l->max = capacity;
    l->size = 0;
    mutex_init(&l->lock);

err:
    return errcode;
}

mbed_error_t list_insert(list_t *l, void *data, uint64_t key)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    struct list_node *n;
    int     ret;

    if (!l || !data) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    if (l->size == l->max) {
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    if ((ret = wmalloc((void **) &n, sizeof(struct list_node), ALLOC_NORMAL)) != 0) {
        printf("Error in malloc: %d\n", ret);
        errcode = MBED_ERROR_NOMEM;
        goto err;
    }

    /* We manipulate the queue: we need to lock it to stay thread-safe */
    if (get_current_ctx_id() == CTX_ISR) {
        if (!mutex_trylock(&l->lock)) {
            errcode = MBED_ERROR_BUSY;
            goto err;
        }
    } else {
        mutex_lock(&l->lock);
    }
    n->data = data;
    n->key = key;

    struct list_node *node = l->head;
    /* empty list ? */
    if (node == NULL) {
        l->head = n;
        n->next = NULL;
        n->prev = NULL;
        goto err_lock;
    }

    /* or find the correct position */
    while (node && node->key <= key && node->next) {
        node = node->next;
    }
    if (node->key <= key) {
        /* current node has the bigger key */
        node->next = n;
        n->next = NULL;
        n->prev = node;
    } else {
        n->next = node;
        if (node->prev == NULL) {
            /* set node before first */
            l->head = n;
            n->prev = NULL;
        } else {
            n->prev = node->prev;
            n->prev->next = n;
        }
        node->prev = n;
    }
    l->size++;

err_lock:
    mutex_unlock(&l->lock);
err:
    return errcode;

}


mbed_error_t list_remove(list_t *l, void **data, uint64_t key)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    struct list_node *n;

    if (!l || !data) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (l->head == NULL) {
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }
    /* We manipulate the queue: we need to lock it to stay thread-safe */
    if (get_current_ctx_id() == CTX_ISR) {
        if (!mutex_trylock(&l->lock)) {
            errcode = MBED_ERROR_BUSY;
            goto err;
        }
    } else {
        mutex_lock(&l->lock);
    }

    n = l->head;
    /* or find the correct position */
    while (n && n->key != key && n->next) {
        n = n->next;
    }
    if (n->key != key) {
        errcode = MBED_ERROR_NOTFOUND;
        goto err_lock;
    }
    /* We have found the node ! */

    /*get back data and remove the node */
    *data = n->data;
    if (n->next) {
        n->next->prev = n->prev;
    }
    if (n->prev) {
        n->prev->next = n->next;
    }
    if (wfree((void **) &n) != 0) {
#if LIST_DEBUG
        /* this error should not happend. */
        printf("free failed with %x\n", ret);
#endif
    }
    l->size--;

err_lock:
    mutex_unlock(&l->lock);
err:
    return errcode;
}

/* update a list item with a new key */
mbed_error_t list_update(list_t*l, uint64_t key, uint64_t newkey)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    void *data;
    /* remove the item from the list... */
    errcode = list_remove(l, &data, key);
    if (errcode != MBED_ERROR_NONE) {
        printf("failed to remove item at update time\n");
        goto err;
    }
    /* and add it with the new key :-) */
    errcode = list_insert(l, data, newkey);
    printf("failed to reinsert item at update time\n");

err:
    return errcode;
}
