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
    uint32_t lock;
	uint32_t size;
	uint32_t max;
} queue_t;

#ifdef __FRAMAC__
/*@
  // logic function that check if data exists in the queue (recursive)
  logic boolean data_in_cell(struct node *node, void *data) =
     node == NULL ? \false :
         node->data == data ? \true :
             node->next != NULL ? data_in_cell(node->next, data) : \false;

  // parent logic function that calls data_in_cell
  logic boolean data_in_queue(queue_t *q, void* data) =
    q->size == 0 ? \false :
      data_in_cell(q->head, data);

  // logic function that check that a cell sequence haven't changed (recursive)
  logic boolean cell_hasnt_changed{L1,L2}(struct node *node) =
    (\at(node,L2) == NULL && \at(node, L1) == NULL) ? \true :
       (\at(node,L2) == NULL && \at(node, L1) != NULL) ? \false :
          (\at(node,L2) != NULL && \at(node, L1) == NULL) ? \false :
             (\at(node->data,L2) == \at(node->data, L1) && \at(node->next,L2) == \at(node->next, L1)) ? (\at(node->next,L2) != NULL ? cell_hasnt_changed{L1,L2}(\at(node->next,L2)) : \true ) : \false;

  // logic function that check that a given queue hasn't changed at all
  logic boolean queue_hasnt_changed{L1,L2}(queue_t *q) =
    (\at(q,L2) == NULL && \at(q, L1) == NULL) ? \true :
       (\at(q,L2) == NULL && \at(q, L1) != NULL) ? \false :
          (\at(q,L2) != NULL && \at(q, L1) == NULL) ? \false :
            (\at(q->head,L2) == \at(q->head, L1) &&
              \at(q->tail,L2) == \at(q->tail, L1) &&
              \at(q->size,L2) == \at(q->size, L1) &&
              \at(q->max,L2) == \at(q->max, L1)) ? (\at(q->head,L2) != NULL ? cell_hasnt_changed{L1,L2}(\at(q->head,L2)) : \true) : \false;

*/
#endif

/**
 * \fn queue_create
 * \brief Create an empty queue
 *
 * \param capacity Maximum number of elements in the queue. Should be between 0 and 512.
 * \param queue    queue the queue pointer that will be updated
 *
 * \return MBED_ERROR_NONE if everything is ok. another error code in other case (see types.h)
 */
/*@
  @ assigns *queue;

  @ behavior bad_input_ptr:
  @   assumes !\valid(queue);
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior bad_capacity:
  @   assumes \valid(queue);
  @   assumes capacity == 0;
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior ok:
  @   assumes \valid(queue);
  @   assumes capacity > 0;
  @   ensures \result == MBED_ERROR_NONE ==> (
        \valid(*queue) && (*queue)->head == NULL &&
        (*queue)->tail == NULL                   &&
        (*queue)->lock == 1                      &&
        (*queue)->size == 0                      &&
        (*queue)->max  == capacity);
  @   ensures \result != MBED_ERROR_NONE ==> !\valid(*queue);

  @ disjoint behaviors;
  @ complete behaviors;
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
/*@
  @ requires \separated(q,((uint8_t*)data));
  @ assigns *q;

  @ behavior bad_input_queue:
  @   assumes !\valid(q);
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior bad_input_data:
  @   assumes \valid(q);
  @   assumes data == NULL;
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior nomem:
  @   assumes \valid(q);
  @   assumes data != NULL;
  @   assumes q->size == q->max;
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_NOMEM;

  @ behavior busy:
  @   assumes \valid(q);
  @   assumes data != NULL;
  @   assumes q->size < q->max;
  @   assumes q->lock == 0;
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_BUSY;

  @ behavior ok:
  @   assumes \valid(q);
  @   assumes data != NULL;
  @   assumes q->size < q->max;
  @   assumes q->lock > 0;
  @   assigns *q;
  @   ensures \result == MBED_ERROR_NONE ==> (
      data_in_queue(q, data) == \true &&
      \valid(q->tail)                 &&
      \valid(q->head)                 &&
      q->tail->data == data           &&
      q->size == \old(q->size)+1);
  @   ensures \result != MBED_ERROR_NONE ==> queue_hasnt_changed{Pre,Post}(q) == \true;

  @ disjoint behaviors;
  @ complete behaviors;
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

/*@
  @ requires \separated(q, data, ((uint8_t*)*data));
  @   assigns *q;
  @   assigns *data;

  @ behavior bad_input_queue:
  @   assumes !\valid(q);
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior bad_input_data:
  @   assumes \valid(q);
  @   assumes !\valid(data);
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @ behavior busy:
  @   assumes \valid(q);
  @   assumes \valid(data);
  @   assumes q->lock == 0;
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_BUSY;

  @ behavior nostorage:
  @   assumes \valid(q);
  @   assumes \valid(data);
  @   assumes q->lock > 0;
  @   assumes q->size == 0;
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_NOSTORAGE;

  @ behavior ok:
  @   assumes \valid(q);
  @   assumes data != NULL;
  @   assumes \valid(data);
  @   assumes q->lock > 0;
  @   assumes q->size > 0;
  @   ensures \result == MBED_ERROR_NONE ==> (
         \valid(((uint8_t*)(*data))+(0 .. 10))      &&
         ((uint8_t*)(*data)) == \old((uint8_t*)(q->tail->data)) &&
         q->tail == \old(q->tail->prev) &&
         q->size == \old(q->size)-1);
  @   ensures \result != MBED_ERROR_NONE ==> (*data == NULL && queue_hasnt_changed{Pre,Post}(q) == \true);

  @ disjoint behaviors;
  @ complete behaviors;
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
/*@
  @ assigns \nothing;

  @ behavior invparam:
  @    assumes !\valid(q);
  @    ensures \result == \true;

  @ behavior ok:
  @    assumes \valid(q);
  @    ensures \result == (q->size == 0);

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
