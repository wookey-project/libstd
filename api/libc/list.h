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
#ifndef LIST_H
# define LIST_H

#include "libc/types.h"
#include "libc/malloc.h"
#include "libc/queue.h"

#define MAX_LIST_DEPTH 512

struct list_node {
	struct list_node *next;
	struct list_node *prev;
	void   *data;
    uint64_t key;
};



typedef struct list {
	struct list_node *head;
    uint32_t lock;
	uint32_t size;
	uint32_t max;
} list_t;


/*
 * Create new ordered list
 */
mbed_error_t list_create(uint32_t capacity, list_t *list);

/*
 * Insert an item into the list (ordered by key)
 */
mbed_error_t list_insert(list_t *l, void *data, uint64_t key);

/*
 * Remove the first item of key 'key' from the list
 */
mbed_error_t list_remove(list_t *l, void **data, uint64_t key);

/*
 * update the first item of key 'key' with new key newkey (order preserved)
 */
mbed_error_t list_update(list_t*l, uint64_t key, uint64_t newkey);

#endif /* LIST_H_ */
