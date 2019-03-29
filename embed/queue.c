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
#include "api/queue.h"

#include "api/nostd.h"
#include "api/stdio.h"
#include "api/semaphore.h"

#define QUEUE_DEBUG 0

mbed_error_t queue_create(uint32_t capacity, queue_t **queue)
{
	queue_t *q = 0;

    /* sanitizing */
    if (!queue) {
        goto invparam;
    }
    if (capacity > MAX_QUEUE_DEPTH) {
        goto invparam;
    }
    if (capacity == 0) {
        goto invparam;
    }

    /* allocating */
    if (wmalloc((void**)&q, sizeof(queue_t), ALLOC_NORMAL) != 0) {
        goto nomem;
    }
#if QUEUE_DEBUG
    aprintf("queue address is %x\n", q);
#endif
    /* initializing */
    q->head = NULL;
    q->tail = NULL;
	q->max = capacity;
	q->size = 0;
    mutex_init(&q->lock);

    *queue = q;

	return MBED_ERROR_NONE;
nomem:
    return MBED_ERROR_NOMEM;
invparam:
    return MBED_ERROR_INVPARAM;
}

mbed_error_t queue_enqueue(queue_t *q, void *data)
{
    if (!q || !data) {
        return MBED_ERROR_INVPARAM;
    }
    if (q->size == q->max) {
        return MBED_ERROR_NOMEM;
    }


	struct node *n;
    if(wmalloc((void**)&n, sizeof(struct node), ALLOC_NORMAL) != 0) {
        return MBED_ERROR_NOMEM;
    }

    /* from now on, we manipulate the queue, we lock it to stay
     * thread-safe
     */
    if (!mutex_trylock(&q->lock)) {
        return MBED_ERROR_BUSY;
    }

	n->next = q->head;
	n->prev = NULL;
	n->data = data;
	if (q->head){
		q->head->prev = n;
	}
	q->head = n;
	if (!q->tail) {
		q->tail = q->head;
	}
	q->size++;
    mutex_unlock(&q->lock);

	return MBED_ERROR_NONE;
}

mbed_error_t queue_next_element(queue_t *q, void **next)
{
    if (!q || !next) {
        return MBED_ERROR_INVPARAM;
    }

    if (!mutex_trylock(&q->lock)) {
        return MBED_ERROR_BUSY;
    }
    if (q->size == 0) {
        /* in this very case, q->tail is null */
        *next = NULL;
        mutex_unlock(&q->lock);
        return MBED_ERROR_NOSTORAGE;
    }

	*next = (void*)q->tail->data;
    mutex_unlock(&q->lock);
    return MBED_ERROR_NONE;
}

mbed_error_t queue_dequeue(queue_t *q, void **data)
{
    mbed_error_t ret = MBED_ERROR_NONE;
    if (!q || !data) {
        ret = MBED_ERROR_INVPARAM;
        goto early_error;
    }

    if (!mutex_trylock(&q->lock)) {
        ret = MBED_ERROR_BUSY;
        goto early_error;
    }
    if (q->size == 0) {
        /* in this very case, q->tail is null */
        ret = MBED_ERROR_NOSTORAGE;
        goto nostorage;
    }

	struct node *last = q->tail;
	*data = last->data;

    if (!*data) {
       ret = MBED_ERROR_NOSTORAGE;
    }

	if(last->prev != NULL){
		last->prev->next = NULL;
	}

	q->tail = last->prev;

	if (last == q->head){
		q->head = NULL;
	}
	q->size--;

	if (wfree((void**)&last) != 0) {
#if QUEUE_DEBUG
        /* this error should not happend. */
        aprintf("free failed with %x\n", ret);
#endif
    }

nostorage:
    mutex_unlock(&q->lock);
early_error:
	return ret;
}

bool queue_is_empty(queue_t *q)
{
    /* q->size access should be atomic (after the q
     * address derefrence). As it is a basic field
     * atomic read, we prefer not to lock here */
    return (q->size == 0);
}

mbed_error_t queue_available_space(queue_t *q, uint32_t *space)
{
    if (!q || !space) {
        return MBED_ERROR_INVPARAM;
    }
    if (!mutex_trylock(&q->lock)) {
        return MBED_ERROR_BUSY;
    }

    *space = q->max - q->size;

    mutex_unlock(&q->lock);
	return MBED_ERROR_NONE;
}
