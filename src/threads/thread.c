#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "devices/timer.h"  /* Include for timer_ticks() */
#ifdef USERPROG
#include "userprog/process.h"
#endif

/** Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/** List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

/** List of all processes.  Processes are added to this list
   when they are first scheduled and removed when they exit. */
static struct list all_list;

/** Idle thread. */
static struct thread *idle_thread;

/** Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/** Lock used by allocate_tid(). */
static struct lock tid_lock;

static fp_t load_avg;  /* System load average (fixed-point) */

/* Array of 64 ready queues, one for each priority level */
static struct list ready_queues[PRI_MAX + 1];

/* Bitmap to track which queues have threads */
static unsigned ready_priorities[2];  /* 64 bits total */

/* Current highest ready priority */
static int highest_ready_priority;

static int ready_treads_count;  /* Number of threads in ready state */

/* Set bit corresponding to priority level */
#define SET_PRIORITY_BIT(priority) \
  ready_priorities[(priority) / 32] |= (1 << ((priority) % 32))
 
/* Clear bit corresponding to priority level */
#define CLEAR_PRIORITY_BIT(priority) \
  ready_priorities[(priority) / 32] &= ~(1 << ((priority) % 32))

/* Test if priority level has any threads */
#define TEST_PRIORITY_BIT(priority) \
  (ready_priorities[(priority) / 32] & (1 << ((priority) % 32)))

/** Stack frame for kernel_thread(). */
struct kernel_thread_frame 
  {
    void *eip;                  /**< Return address. */
    thread_func *function;      /**< Function to call. */
    void *aux;                  /**< Auxiliary data for function. */
  };

/** Statistics. */
static long long idle_ticks;    /**< # of timer ticks spent idle. */
static long long kernel_ticks;  /**< # of timer ticks in kernel threads. */
static long long user_ticks;    /**< # of timer ticks in user programs. */

/** Scheduling. */
#define TIME_SLICE 4            /**< # of timer ticks to give each thread. */
static unsigned thread_ticks;   /**< # of timer ticks since last yield. */

/** If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *) UNUSED;
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);
void thread_schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);

bool thread_priority_compare(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED) 
{
  struct thread *t1 = list_entry(a, struct thread, elem);
  struct thread *t2 = list_entry(b, struct thread, elem);
  return t1->priority > t2->priority;
}

static void
highest_priority_check(void *aux UNUSED)
{
  if (!thread_mlfqs) {
    return;
  }
  struct list_elem *e;
  for (e = list_begin(&all_list); e != list_end(&all_list); e = list_next(e)) {
    struct thread *t = list_entry(e, struct thread, allelem);
    if (t->status == THREAD_READY && t != idle_thread) {
      /* Assert that highest_ready_priority is at least as high as this thread's priority */
      ASSERT(t->priority <= highest_ready_priority);
    }
  }
}

/* Add a thread to its priority queue atomically */
static void
ready_queue_add(struct thread *t)
{
  list_push_back(&ready_queues[t->priority], &t->elem);
  SET_PRIORITY_BIT(t->priority);

  ready_treads_count++;
 
  /* Update highest priority atomically */
  if (t->priority > highest_ready_priority)
    highest_ready_priority = t->priority;
}

/* Remove and return highest priority thread atomically */
static struct thread *
ready_queue_remove_highest(void)
{
  struct thread *t = NULL;
  
  /* Find highest non-empty queue */
  if (highest_ready_priority >= PRI_MIN) {
    /* Use cached highest priority */
    t = list_entry(list_pop_front(&ready_queues[highest_ready_priority]), 
                  struct thread, elem);
                  
    /* If queue is now empty, clear bit and update highest */
    if (list_empty(&ready_queues[highest_ready_priority])) {
      CLEAR_PRIORITY_BIT(highest_ready_priority);
      
      /* Find new highest priority */
      int new_highest = PRI_MIN - 1;
      for (int i = highest_ready_priority - 1; i >= PRI_MIN; i--) {
        if (TEST_PRIORITY_BIT(i)) {
          new_highest = i;
          break;
        }
      }
      highest_ready_priority = new_highest;
    }
  }
  if (t) {
    ready_treads_count--;
  }
  return t ? t : idle_thread;
}

/* Change a thread's queue position atomically */
static void
ready_queue_change_priority(struct thread *t, int old_priority)
{
    /* Remove from old queue */
    list_remove(&t->elem);
    
    /* Clear the bit if queue is now empty */
    if (list_empty(&ready_queues[old_priority])) {
      /* Clear the bit for the old priority */
      /* and update highest priority if needed */
      CLEAR_PRIORITY_BIT(old_priority);
      
      /* Update highest priority if it was this queue */
      if (old_priority == highest_ready_priority) {
        int new_highest = PRI_MIN - 1;
        for (int i = highest_ready_priority - 1; i >= PRI_MIN; i--) {
          if (TEST_PRIORITY_BIT(i)) {
            new_highest = i;
            break;
          }
        }
        highest_ready_priority = new_highest;
      }
    }
    
    /* Add to new queue */
    list_push_back(&ready_queues[t->priority], &t->elem);
    SET_PRIORITY_BIT(t->priority);
    
    /* Update highest priority if needed */
    if (t->priority > highest_ready_priority)
      highest_ready_priority = t->priority;
}

static void save_old_priority(struct thread *t, void *aux UNUSED) 
{
  t->old_priority = t->priority;
}

/* Called when a thread's priority changes */
void thread_priority_changed(struct thread *t) 
{
  if (t->status == THREAD_READY) {
    ready_queue_change_priority(t, t->old_priority);
  }
}

static void check_priority_changed(struct thread *t, void *aux UNUSED) 
{
  if (t->old_priority != t->priority) {
    thread_priority_changed(t);
  }
}

/* Helper function to recalculate thread's recent_cpu value */
void
recalculate_recent_cpu (struct thread *t, void *aux UNUSED)
{
  if (t == idle_thread)
    return;
  /* recent_cpu = (2*load_avg)/(2*load_avg + 1) * recent_cpu + nice */
  fp_t load_avg_2 = MUL_FP_INT(load_avg, 2);
  fp_t coefficient = DIV_FP_FP(load_avg_2, ADD_FP_INT(load_avg_2, 1));
  
  t->recent_cpu = ADD_FP_INT(MUL_FP_FP(coefficient, t->recent_cpu), t->nice);
}

/* Helper function to recalculate thread's priority */
void
recalculate_priority (struct thread *t, void *aux UNUSED)
{
  if (t == idle_thread)
    return;
  /* priority = PRI_MAX - (recent_cpu/4) - (nice*2) */
  int priority = PRI_MAX - FP_TO_INT_TRUNC(DIV_FP_INT(t->recent_cpu, 4)) - (t->nice * 2);
  
  /* Ensure priority is within bounds */
  if (priority < PRI_MIN)
    priority = PRI_MIN;
  else if (priority > PRI_MAX)
    priority = PRI_MAX;
    
  t->priority = priority;
}

void update_cpu_usage(void) 
{
  // Count ready threads directly from all threads list
  int ready_threads =  ready_treads_count;  

  if (thread_current()->status == THREAD_RUNNING && thread_current() != idle_thread) {
    ready_threads++;
  }
  
  // Calculate load_avg with more precision
  // load_avg = (59/60) * load_avg + (1/60) * ready_threads
  fp_t coef_59_60 = DIV_FP_FP(INT_TO_FP(59), INT_TO_FP(60));
  fp_t coef_1_60 = DIV_FP_FP(INT_TO_FP(1), INT_TO_FP(60));
  
  fp_t term1 = MUL_FP_FP(coef_59_60, load_avg);
  fp_t term2 = MUL_FP_INT(coef_1_60, ready_threads);
  load_avg = ADD_FP_FP(term1, term2);

  // Update recent_cpu for all threads
  thread_foreach(recalculate_recent_cpu, NULL);
}

void update_recent_cpu(void) 
{
  struct thread *current = thread_current();
  // Every tick: Increment recent_cpu for the running thread
  // Skip if it's the idle thread
  if (current != idle_thread && current->status == THREAD_RUNNING) {
    current->recent_cpu = ADD_FP_INT(current->recent_cpu, 1);
  }
}

void update_priority(void) 
{  
  // Save old priorities and recalculate new priorities for all threads
  thread_foreach(save_old_priority, NULL);
  thread_foreach(recalculate_priority, NULL);
  
  // Instead of using check_priority_changed, directly iterate through threads
  // and use our atomic queue update function for ones that changed priority
  struct list_elem *e;
  for (e = list_begin(&all_list); e != list_end(&all_list); e = list_next(e)) {
    struct thread *t = list_entry(e, struct thread, allelem);
    if (t->old_priority != t->priority && t->status == THREAD_READY) {
      // Use our atomic priority change function
      ready_queue_change_priority(t, t->old_priority);
    }
  }
  
  // Check if current thread should yield to a higher priority thread
  struct thread *current = thread_current();
  if (current != idle_thread && highest_ready_priority > current->priority) {
    if (intr_context()) {
      intr_yield_on_return();
    } else {
      // intr_set_level(old_level); // Restore interrupts before yielding
      thread_yield();
      return; // Return early since thread_yield won't return immediately
    }
  }
}


/** Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void) 
{
  ASSERT (intr_get_level () == INTR_OFF);

  lock_init (&tid_lock);
  list_init (&ready_list);
  list_init (&all_list);

  for (int i = 0; i <= PRI_MAX; i++) {
    list_init(&ready_queues[i]);
  }

  load_avg = INT_TO_FP(0);  /* Initialize to 0 as fixed-point */
  ready_priorities[0] = 0;
  ready_priorities[1] = 0;
  highest_ready_priority = PRI_MIN - 1; 
  ready_treads_count = 0;

  /* Set up a thread structure for the running thread. */
  initial_thread = running_thread ();
  init_thread (initial_thread, "main", PRI_DEFAULT);
  initial_thread->status = THREAD_RUNNING;
  initial_thread->tid = allocate_tid ();
}

/** Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void) 
{
  /* Create the idle thread. */
  struct semaphore idle_started;
  sema_init (&idle_started, 0);
  thread_create ("idle", PRI_MIN, idle, &idle_started);

  /* Start preemptive thread scheduling. */
  intr_enable ();

  /* Wait for the idle thread to initialize idle_thread. */
  sema_down (&idle_started);
}

/** Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void) 
{
  struct thread *t = thread_current ();

  /* Update statistics. */
  if (t == idle_thread)
    idle_ticks++;
#ifdef USERPROG
  else if (t->pagedir != NULL)
    user_ticks++;
#endif
  else
    kernel_ticks++;

  /* Enforce preemption. */
  if (++thread_ticks >= TIME_SLICE)
    intr_yield_on_return ();
}

/** Prints thread statistics. */
void
thread_print_stats (void) 
{
  printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
          idle_ticks, kernel_ticks, user_ticks);
}

/** Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux) 
{
  struct thread *t;
  struct kernel_thread_frame *kf;
  struct switch_entry_frame *ef;
  struct switch_threads_frame *sf;
  tid_t tid;

  ASSERT (function != NULL);

  /* Allocate thread. */
  t = palloc_get_page (PAL_ZERO);
  if (t == NULL)
    return TID_ERROR;

  /* Initialize thread. */
  init_thread (t, name, priority);
  tid = t->tid = allocate_tid ();

  /* Stack frame for kernel_thread(). */
  kf = alloc_frame (t, sizeof *kf);
  kf->eip = NULL;
  kf->function = function;
  kf->aux = aux;

  /* Stack frame for switch_entry(). */
  ef = alloc_frame (t, sizeof *ef);
  ef->eip = (void (*) (void)) kernel_thread;

  /* Stack frame for switch_threads(). */
  sf = alloc_frame (t, sizeof *sf);
  sf->eip = switch_entry;
  sf->ebp = 0;

  /* Add to run queue. */
  thread_unblock (t);
  
  return tid;
}

/** Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void) 
{
  ASSERT (!intr_context ());
  ASSERT (intr_get_level () == INTR_OFF);

  thread_current ()->status = THREAD_BLOCKED;
  schedule ();
}

/** Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t) 
{
  enum intr_level old_level;

  ASSERT (is_thread (t));

  old_level = intr_disable ();
  ASSERT (t->status == THREAD_BLOCKED);

 /* Add to the appropriate priority queue */
  ready_queue_add(t);
  t->status = THREAD_READY;
  
  if (thread_current()->tid != t->tid && thread_current()->priority < t->priority) {
    if (intr_context()) {
      intr_yield_on_return();
    } else {
      if (thread_current() != idle_thread) {
        thread_yield();
      }
    } 
  } 
  
  intr_set_level (old_level);
}

/** Returns the name of the running thread. */
const char *
thread_name (void) 
{
  return thread_current ()->name;
}

/** Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void) 
{
  struct thread *t = running_thread ();
  
  /* Make sure T is really a thread.
     If either of these assertions fire, then your thread may
     have overflowed its stack.  Each thread has less than 4 kB
     of stack, so a few big automatic arrays or moderate
     recursion can cause stack overflow. */
  ASSERT (is_thread (t));
  ASSERT (t->status == THREAD_RUNNING);

  return t;
}

/** Returns the running thread's tid. */
tid_t
thread_tid (void) 
{
  return thread_current ()->tid;
}

/** Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void) 
{
  ASSERT (!intr_context ());

#ifdef USERPROG
  process_exit ();
#endif

  /* Remove thread from all threads list, set our status to dying,
     and schedule another process.  That process will destroy us
     when it calls thread_schedule_tail(). */
  intr_disable ();
  list_remove (&thread_current()->allelem);
  thread_current ()->status = THREAD_DYING;
  schedule ();
  NOT_REACHED ();
}

/** Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void) 
{
  struct thread *cur = thread_current ();
  enum intr_level old_level;
  
  ASSERT (!intr_context ());
  old_level = intr_disable ();
  
  if (cur != idle_thread) {
    // Add to appropriate priority queue
    ready_queue_add(cur);
  }

  cur->status = THREAD_READY;

  schedule ();
  intr_set_level (old_level);
}

/** Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
  struct list_elem *e;

  ASSERT (intr_get_level () == INTR_OFF);

  for (e = list_begin (&all_list); e != list_end (&all_list);
       e = list_next (e))
    {
      struct thread *t = list_entry (e, struct thread, allelem);
      func (t, aux);
    }
}

/* Checks if the current thread should yield to a higher-priority ready thread. */
void
check_yield(void) 
{
  /* Don't yield if we're the idle thread */
  struct thread *current = thread_current();
  if (current == idle_thread)
    return;

  /* Simply check if highest_ready_priority is greater than current priority */
  if (highest_ready_priority > current->priority) {
    
    /* Yield to the higher priority thread */
    if (intr_context()) {
      intr_yield_on_return();
    } else {
      thread_yield();
      return;
    } 
  }
}

/** Sets the current thread's priority to NEW_PRIORITY. */
void
thread_set_priority (int new_priority) 
{
  if (thread_mlfqs) {
    return;
  }

  enum intr_level old_level = intr_disable();
  struct thread *current = thread_current();
  int old_priority = current->priority;
  
  // Always update base priority
  current->base_priority = new_priority;
  
  // Only update effective priority if we're not receiving donations
  if (!current->is_donating) {
    current->priority = new_priority;
  }
  
  if (current->priority != old_priority) {
    thread_priority_changed(current);
  }

  if (current->priority < old_priority) {
    check_yield();
  }

  intr_set_level(old_level);
}

/** Returns the current thread's priority. */
int
thread_get_priority (void) 
{
  int priority = thread_current()->priority;  
  return priority;
}

/** Sets the current thread's nice value to NICE. */
void
thread_set_nice (int nice) 
{  
  struct thread *current = thread_current();
  
  /* Clamp nice value to valid range */
  if (nice < -20) {
    nice = -20;
  } else if (nice > 20) {
    nice = 20;
  }
  
  current->nice = nice;
  /* Calculate new priority based on recent_cpu and nice */
  int old_priority = current->priority;
  int new_priority = PRI_MAX - FP_TO_INT_TRUNC(DIV_FP_INT(current->recent_cpu, 4)) - 2 * nice;

  /* Ensure priority is within bounds */
  if (new_priority < PRI_MIN) {
    new_priority = PRI_MIN;
  } else if (new_priority > PRI_MAX) {
    new_priority = PRI_MAX;
  }
  
  current->priority = new_priority;
  
  /* If thread is ready and priority changed, update its position in queue */
  if (old_priority != new_priority && current->status == THREAD_READY) {
    ready_queue_change_priority(current, old_priority);
  }
  /* Check if we need to yield due to decreased priority */
  if (new_priority < old_priority) {
    thread_yield();
    return;
  }
}

/** Returns the current thread's nice value. */
int
thread_get_nice (void) 
{
  return thread_current()->nice;
}

/** Returns 100 times the system load average. */
int
thread_get_load_avg (void) 
{
  return FP_TO_INT_NEAREST(MUL_FP_INT(load_avg, 100));
}

/** Returns 100 times the current thread's recent_cpu value. */
int
thread_get_recent_cpu (void) 
{
  return FP_TO_INT_NEAREST(MUL_FP_INT(thread_current()->recent_cpu, 100));
}

/** Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED) 
{
  struct semaphore *idle_started = idle_started_;
  idle_thread = thread_current ();
  sema_up (idle_started);

  for (;;) 
    {
      /* Let someone else run. */
      intr_disable ();
      thread_block ();

      /* Re-enable interrupts and wait for the next one.

         The `sti' instruction disables interrupts until the
         completion of the next instruction, so these two
         instructions are executed atomically.  This atomicity is
         important; otherwise, an interrupt could be handled
         between re-enabling interrupts and waiting for the next
         one to occur, wasting as much as one clock tick worth of
         time.

         See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
         7.11.1 "HLT Instruction". */
      asm volatile ("sti; hlt" : : : "memory");
    }
}

/** Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux) 
{
  ASSERT (function != NULL);

  intr_enable ();       /**< The scheduler runs with interrupts off. */
  function (aux);       /**< Execute the thread function. */
  thread_exit ();       /**< If function() returns, kill the thread. */
}

/** Returns the running thread. */
struct thread *
running_thread (void) 
{
  uint32_t *esp;

  /* Copy the CPU's stack pointer into `esp', and then round that
     down to the start of a page.  Because `struct thread' is
     always at the beginning of a page and the stack pointer is
     somewhere in the middle, this locates the curent thread. */
  asm ("mov %%esp, %0" : "=g" (esp));
  return pg_round_down (esp);
}

/** Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
  return t != NULL && t->magic == THREAD_MAGIC;
}

/** Does basic initialization of T as a blocked thread named
   NAME. */
static void
init_thread (struct thread *t, const char *name, int priority)
{
  enum intr_level old_level;

  ASSERT (t != NULL);
  ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
  ASSERT (name != NULL);

  memset (t, 0, sizeof *t);
  t->status = THREAD_BLOCKED;
  strlcpy (t->name, name, sizeof t->name);
  t->stack = (uint8_t *) t + PGSIZE;
  if (!thread_mlfqs) {
    t->priority = priority;
    t->base_priority = priority;
    t->old_priority = priority;
  } else {
    if (t == initial_thread) {
      t->recent_cpu = INT_TO_FP(0);
      t->nice = 0;
    } else {
      t->recent_cpu = thread_current()->recent_cpu;
      t->nice = thread_current()->nice; 
    }
  }

  t->magic = THREAD_MAGIC;
  list_init(&t->locks);
  t->waiting_lock = NULL;
  t->wait_ticks = 0;
  t->is_donating = false;
  old_level = intr_disable ();
  list_push_back (&all_list, &t->allelem);
  intr_set_level (old_level);
}

/** Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame (struct thread *t, size_t size) 
{
  /* Stack data is always allocated in word-size units. */
  ASSERT (is_thread (t));
  ASSERT (size % sizeof (uint32_t) == 0);

  t->stack -= size;
  return t->stack;
}

/** Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void)
{
   return ready_queue_remove_highest();
}

/** Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
thread_schedule_tail (struct thread *prev)
{
  struct thread *cur = running_thread ();
  
  ASSERT (intr_get_level () == INTR_OFF);

  /* Mark us as running. */
  cur->status = THREAD_RUNNING;

  /* Start new time slice. */
  thread_ticks = 0;

#ifdef USERPROG
  /* Activate the new address space. */
  process_activate ();
#endif

  /* If the thread we switched from is dying, destroy its struct
     thread.  This must happen late so that thread_exit() doesn't
     pull out the rug under itself.  (We don't free
     initial_thread because its memory was not obtained via
     palloc().) */
  if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread) 
    {
      ASSERT (prev != cur);
      palloc_free_page (prev);
    }
}

/** Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until thread_schedule_tail()
   has completed. */
static void
schedule (void) 
{
  struct thread *cur = running_thread ();
  struct thread *next = next_thread_to_run ();
  struct thread *prev = NULL;

  ASSERT (intr_get_level () == INTR_OFF);
  ASSERT (cur->status != THREAD_RUNNING);
  ASSERT (is_thread (next));

  if (cur != next)
    prev = switch_threads (cur, next);
  thread_schedule_tail (prev);
}

/** Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void) 
{
  static tid_t next_tid = 1;
  tid_t tid;

  lock_acquire (&tid_lock);
  tid = next_tid++;
  lock_release (&tid_lock);

  return tid;
}

/** Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);


