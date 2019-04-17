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
#ifndef QUEUE_H
# define QUEUE_H

#include "libc/types.h"
#include "libc/malloc.h"

#define MAX_QUEUE_DEPTH 512

struct node {
	struct node *next;
	struct node *prev;
	void *data;
};

typedef struct queue {
	struct node *head;
	struct node *tail;
    volatile uint32_t lock;
	uint32_t size;
	uint32_t max;
} queue_t;

/**
 * \fn queue_create
 * \brief Create an empty queue
 *
 * \param capacity Maximum number of elements in the queue. Should be between 0 and 512.
 * \param queue    queue the queue pointer that will be updated
 *
 * \return MBED_ERROR_NONE if everything is ok. another error code in other case (see types.h)
 */
mbed_error_t queue_create(uint32_t capacity, queue_t **queue);

/**
 * \fn queue_enqueue
 * \brief Add an element in the queue
 *
 * \param q     The queue to work on
 * \param data  payload to add in the queue
 *
 * \return MBED_ERROR_NONE if everything is ok. another error code in other case (see types.h)
 */
mbed_error_t queue_enqueue(queue_t *q, void *data);

/**
 * \fn queue_next_element
 * \brief Get the next element of the queue
 *
 * \param q    The queue to work on
 * \return     The next element of the queue, or NULL if the queue is empty
 *
 * This function returns the next element of the queue that will be removed
 * from the queue but it *does not remove* this element from the queue. See
 * @queue_dequeue which return the next element and remove it from the queue.
 *
 */
mbed_error_t queue_next_element(queue_t *q, void **next);

/**
 * \fn queue_dequeue
 * \brief Dequeue the next element
 *
 * \param q The queue to work on
 * \param data the element pointer which will hold the dequeued content
 *
 * \return This function remove the next element from the queue and returns it.
 *
 * \return MBED_ERROR_NONE if everything is ok. another error code in other case (see types.h)
 */
mbed_error_t queue_dequeue(queue_t *q, void **data);

/**
 * \fn queue_is_empty
 * \brief return the status of the queue
 *
 * \param  q The queue to work on.
 *
 * \return True if the queue is empty, false otherwise
 */
bool queue_is_empty(queue_t *q);

/**
 * \fn queue_available_space
 * \brief Get the remaining slots count
 *
 * \param q The queue to work on.
 *
 * \return The number of free cells of the queue
 */
mbed_error_t queue_available_space(queue_t *q, uint32_t *space);


mbed_error_t queue_dump(queue_t *q);

#endif /* QUEUE_H */
