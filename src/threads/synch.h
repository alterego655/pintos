#ifndef THREADS_SYNCH_H
#define THREADS_SYNCH_H

#include <list.h>
#include <stdbool.h>
#include "threads/thread.h"

/** A counting semaphore. */
struct semaphore 
  {
    unsigned value;             /**< Current value. */
    struct list waiters;        /**< List of waiting threads. */
  };

bool semaphore_priority_compare(const struct list_elem *a, const struct list_elem *b, void *aux);

void sema_init (struct semaphore *, unsigned value);
void sema_down (struct semaphore *);
bool sema_try_down (struct semaphore *);
void sema_up (struct semaphore *);
void sema_self_test (void);
void donate_priority(struct thread *t, int priority);
void reset_priority(struct thread *t);
// void update_ready_list(void);

/** Lock. */
struct lock 
  {
    struct thread *holder;      /**< Thread holding lock (for debugging). */
    struct semaphore semaphore; /**< Binary semaphore controlling access. */
    struct list_elem elem;      /**< List element for thread's locks list. */
  };

void lock_init (struct lock *);
void lock_acquire (struct lock *);
bool lock_try_acquire (struct lock *);
void lock_release (struct lock *);
bool lock_held_by_current_thread (const struct lock *);

/** Condition variable. */
struct condition 
  {
    struct list waiters;        /**< List of waiting threads. */
  };

void cond_init (struct condition *);
void cond_wait (struct condition *, struct lock *);
void cond_signal (struct condition *, struct lock *);
void cond_broadcast (struct condition *, struct lock *);

/** Optimization barrier.

   The compiler will not reorder operations across an
   optimization barrier.  See "Optimization Barriers" in the
   reference guide for more information.*/
#define barrier() asm volatile ("" : : : "memory")

#endif /**< threads/synch.h */
