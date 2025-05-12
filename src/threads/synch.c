/** This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/** Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
*/

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"

#ifndef UNUSED
#define UNUSED __attribute__ ((unused))
#endif

/* Maximum nesting depth for priority donations */
#define MAX_DONATION_DEPTH 8

/* Current nesting depth for priority donations */
static int nested_donation_depth;

/** One semaphore in a list. */
struct semaphore_elem 
  {
    struct list_elem elem;              /**< List element. */
    struct semaphore semaphore;         /**< This semaphore. */
    int priority;
  };


bool semaphore_priority_compare(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED)
{
  struct semaphore_elem *se1 = list_entry(a, struct semaphore_elem, elem);
  struct semaphore_elem *se2 = list_entry(b, struct semaphore_elem, elem);
  return se1->priority > se2->priority;
}

/** Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
     decrement it.

   - up or "V": increment the value (and wake up one waiting
     thread, if any). */
void
sema_init (struct semaphore *sema, unsigned value) 
{
  ASSERT (sema != NULL);

  sema->value = value;
  list_init (&sema->waiters);
}

/** Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. */
void
sema_down (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  while (sema->value == 0) 
    {
      
      if (thread_mlfqs) {
        list_push_back(&sema->waiters, &thread_current ()->elem);
      } else {
        list_insert_ordered(&sema->waiters, &thread_current ()->elem, thread_priority_compare, NULL);
      }
      
      thread_block ();
    }
  sema->value--;
  intr_set_level (old_level);
}

/** Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */
bool
sema_try_down (struct semaphore *sema) 
{
  enum intr_level old_level;
  bool success;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (sema->value > 0) 
    {
      sema->value--;
      success = true; 
    }
  else
    success = false;
  intr_set_level (old_level);

  return success;
}

/** Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */
void
sema_up (struct semaphore *sema) 
{
  enum intr_level old_level;
  struct thread *unblocked_thread = NULL;

  ASSERT(sema != NULL);
  old_level = intr_disable();
  
  sema->value++;

  if (!list_empty(&sema->waiters)) {
    // Unblock the highest priority waiter
    list_sort(&sema->waiters, thread_priority_compare, NULL);
    unblocked_thread = list_entry(list_pop_front(&sema->waiters), 
                                struct thread, elem);
   // printf("unblocking thread: %s, priority in up: %d\n", unblocked_thread->name, unblocked_thread->priority);
    thread_unblock(unblocked_thread);
  }

  intr_set_level(old_level);
}

static void sema_test_helper (void *sema_);

/** Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void
sema_self_test (void) 
{
  struct semaphore sema[2];
  int i;

  printf ("Testing semaphores...");
  sema_init (&sema[0], 0);
  sema_init (&sema[1], 0);
  thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
  for (i = 0; i < 10; i++) 
    {
      sema_up (&sema[0]);
      sema_down (&sema[1]);
    }
  printf ("done.\n");
}

/** Thread function used by sema_self_test(). */
static void
sema_test_helper (void *sema_) 
{
  struct semaphore *sema = sema_;
  int i;

  for (i = 0; i < 10; i++) 
    {
      sema_down (&sema[0]);
      sema_up (&sema[1]);
    }
}

/** Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void
lock_init (struct lock *lock)
{
  ASSERT (lock != NULL);

  lock->holder = NULL;
  sema_init (&lock->semaphore, 1);
}

void donate_priority(struct thread *t, int priority) {
  // Only update if the new priority is higher
  if (priority > t->priority) {
    // Keep track of original priority
    // Don't update base_priority!
    if (t->is_donating == false) {
      t->base_priority = t->priority;
      t->is_donating = true;
    }

    t->priority = priority;
      
    // Propagate donation if this thread is waiting for a lock
    // and we haven't exceeded the maximum nesting depth
    if (t->waiting_lock != NULL && t->waiting_lock->holder != NULL && 
        nested_donation_depth < MAX_DONATION_DEPTH) {
      nested_donation_depth++;
      donate_priority(t->waiting_lock->holder, priority);
      nested_donation_depth--;
    }
  }
}

void reset_priority(struct thread *t)
{
  // printf("priority reset name: %s, priority: %d, and base priority is: %d\n", t->name, t->priority, t->base_priority);
  // Reset to base priority first
  t->priority = t->base_priority;
  
  
  if (list_empty(&t->locks)) {
    return;
  }

  struct list_elem *e;
  for (e = list_begin(&t->locks); e != list_end(&t->locks); e = list_next(e)) {
    struct lock *held_lock = list_entry(e, struct lock, elem);
    if (!list_empty(&held_lock->semaphore.waiters)) {
      struct thread *waiter = list_entry(list_front(&held_lock->semaphore.waiters), 
                                       struct thread, elem);
      if (waiter->priority > t->priority) {
        t->priority = waiter->priority;
      }
    }
  }
  

  // printf("resetting priority in reset_priority\n");
  // printf("thread_name, priority, base priority in reset_priority: %s, %d, %d\n", t->name, t->priority, t->base_priority);
  // If this thread holds no more locks, we're done
}


/** Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
lock_acquire (struct lock *lock)
{
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (!lock_held_by_current_thread (lock));
  
  struct thread *current = thread_current();
  struct thread *holder = lock->holder;

  current->waiting_lock = lock;

  if (holder != NULL) {
    // If current thread has higher priority than holder, donate priority
    // printf("current thread_name, priority in acquire: %s, %d\n", current->name, current->priority);
    // printf("holder thread_name, priority in acquire: %s, %d\n", holder->name, holder->priority);
    if (current->priority > holder->priority) {
      // Donate priority to holder
      nested_donation_depth = 0;  // Initialize donation depth counter
      donate_priority(holder, current->priority);
      // printf("Yield to other process to run in acquire.\n");
      // printf("current thread_name, priority in acquire: %s, %d\n", current->name, current->priority);
      // printf("holder thread_name, priority in acquire: %s, %d\n", holder->name, holder->priority);
      thread_yield();
    }
  }
  
  // Try to acquire the lock
  sema_down(&lock->semaphore);

  // printf("thread %s, priority %d has aquired the lock successfully", current->name, current->priority);
  
  // After acquiring the lock
  current->waiting_lock = NULL;
  lock->holder = current;
  list_push_back(&current->locks, &lock->elem);
}

/** Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool
lock_try_acquire (struct lock *lock)
{
  bool success;

  ASSERT (lock != NULL);
  ASSERT (!lock_held_by_current_thread (lock));

  success = sema_try_down (&lock->semaphore);
  if (success)
    lock->holder = thread_current ();
  return success;
}

/** Releases LOCK, which must be owned by the current thread.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */
void 
lock_release(struct lock *lock) {
  ASSERT(lock != NULL);
  ASSERT(lock_held_by_current_thread(lock));

  
  // Remove this lock from thread's list of locks
  list_remove(&lock->elem);
  
  struct thread *current = thread_current();

    // Get old priority before reset
  int old_priority = current->priority;
  
  if (current->is_donating) {
    // printf("resetting priority in release\n");
    // printf("current thread_name, priority in release: %s, %d\n", current->name, current->priority);
    // printf("holder thread_name, priority in release: %s, %d\n", lock->holder->name, lock->holder->priority);
    reset_priority(current);
  }
  
  lock->holder = NULL;
  sema_up(&lock->semaphore);

      // If our priority decreased, yield to let higher priority threads run
  if (!intr_context() && current->priority < old_priority) {
    // printf("Yield to other process to run in release.\n");
    // printf("current thread_name, priority in release: %s, %d\n", current->name, current->priority);
    thread_yield();
  } 
  // printf("thread %s, priority %d has released the lock successfully", current->name, current->priority);
}

/** Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool
lock_held_by_current_thread (const struct lock *lock) 
{
  ASSERT (lock != NULL);

  return lock->holder == thread_current ();
}

/** Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
void
cond_init (struct condition *cond)
{
  ASSERT (cond != NULL);

  list_init (&cond->waiters);
}

/** Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
cond_wait (struct condition *cond, struct lock *lock) 
{
  struct semaphore_elem waiter;

  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
  
  sema_init (&waiter.semaphore, 0);
  waiter.priority = thread_get_priority();

  if (thread_mlfqs) {
    list_push_back (&cond->waiters, &waiter.elem);
  } else {
    list_insert_ordered(&cond->waiters, &waiter.elem, semaphore_priority_compare, NULL);
  }
  
  lock_release (lock);
  sema_down (&waiter.semaphore);
  lock_acquire (lock);
}

/** If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_signal (struct condition *cond, struct lock *lock UNUSED) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));

  if (!list_empty (&cond->waiters)) 
    sema_up (&list_entry (list_pop_front (&cond->waiters),
                          struct semaphore_elem, elem)->semaphore);
}

/** Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_broadcast (struct condition *cond, struct lock *lock) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);

  while (!list_empty (&cond->waiters))
    cond_signal (cond, lock);
}
