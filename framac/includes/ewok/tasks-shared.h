/* tasks-shared.h
 *
 * Copyright (C) 2018 ANSSI
 * All rights reserved.
 *
 * This software may be modified and distributed under the terms
 * of the BSD license.  See the LICENSE file for details.
 */

#ifndef TASK_SHARED_H_
#define TASK_SHARED_H_


/*
 * \brief Task table accessor naming enumerate
 */
typedef enum {
    ID_UNUSED = 0,
    ID_APP1,       /* User app 1 */
    ID_APP2,       /* User app 2 */
    ID_APP3,       /* User app 3 */
    ID_APP4,       /* User app 4 */
    ID_APP5,       /* User app 5 */
    ID_APP6,       /* User app 6 */
    ID_APP7,       /* User app 7 */
    ID_SOFTIRQ,    /* Softirq thread */
    ID_KERNEL,     /* Kernel idle task */
    ID_MAX
} e_task_id;

#endif /*!TASK_SHARED_H_ */
