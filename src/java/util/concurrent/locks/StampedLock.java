/*
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

/*
 *
 *
 *
 *
 *
 * Written by Doug Lea with assistance from members of JCP JSR-166
 * Expert Group and released to the public domain, as explained at
 * http://creativecommons.org/publicdomain/zero/1.0/
 */

package java.util.concurrent.locks;

import jdk.internal.vm.annotation.ReservedStackAccess;

import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;
import java.util.concurrent.TimeUnit;

/**
 * A capability-based lock with three modes for controlling read/write
 * access.  The state of a StampedLock consists of a version and mode.
 * Lock acquisition methods return a stamp that represents and
 * controls access with respect to a lock state; "try" versions of
 * these methods may instead return the special value zero to
 * represent failure to acquire access. Lock release and conversion
 * methods require stamps as arguments, and fail if they do not match
 * the state of the lock. The three modes are:
 *
 * <ul>
 *
 *  <li><b>Writing.</b> Method {@link #writeLock} possibly blocks
 *   waiting for exclusive access, returning a stamp that can be used
 *   in method {@link #unlockWrite} to release the lock. Untimed and
 *   timed versions of {@code tryWriteLock} are also provided. When
 *   the lock is held in write mode, no read locks may be obtained,
 *   and all optimistic read validations will fail.
 *
 *  <li><b>Reading.</b> Method {@link #readLock} possibly blocks
 *   waiting for non-exclusive access, returning a stamp that can be
 *   used in method {@link #unlockRead} to release the lock. Untimed
 *   and timed versions of {@code tryReadLock} are also provided.
 *
 *  <li><b>Optimistic Reading.</b> Method {@link #tryOptimisticRead}
 *   returns a non-zero stamp only if the lock is not currently held in
 *   write mode.  Method {@link #validate} returns true if the lock has not
 *   been acquired in write mode since obtaining a given stamp, in which
 *   case all actions prior to the most recent write lock release
 *   happen-before actions following the call to {@code tryOptimisticRead}.
 *   This mode can be thought of as an extremely weak version of a
 *   read-lock, that can be broken by a writer at any time.  The use of
 *   optimistic read mode for short read-only code segments often reduces
 *   contention and improves throughput.  However, its use is inherently
 *   fragile.  Optimistic read sections should only read fields and hold
 *   them in local variables for later use after validation. Fields read
 *   while in optimistic read mode may be wildly inconsistent, so usage
 *   applies only when you are familiar enough with data representations to
 *   check consistency and/or repeatedly invoke method {@code validate()}.
 *   For example, such steps are typically required when first reading an
 *   object or array reference, and then accessing one of its fields,
 *   elements or methods.
 *
 * </ul>
 *
 * <p>This class also supports methods that conditionally provide
 * conversions across the three modes. For example, method {@link
 * #tryConvertToWriteLock} attempts to "upgrade" a mode, returning
 * a valid write stamp if (1) already in writing mode (2) in reading
 * mode and there are no other readers or (3) in optimistic read mode
 * and the lock is available. The forms of these methods are designed to
 * help reduce some of the code bloat that otherwise occurs in
 * retry-based designs.
 *
 * <p>StampedLocks are designed for use as internal utilities in the
 * development of thread-safe components. Their use relies on
 * knowledge of the internal properties of the data, objects, and
 * methods they are protecting.  They are not reentrant, so locked
 * bodies should not call other unknown methods that may try to
 * re-acquire locks (although you may pass a stamp to other methods
 * that can use or convert it).  The use of read lock modes relies on
 * the associated code sections being side-effect-free.  Unvalidated
 * optimistic read sections cannot call methods that are not known to
 * tolerate potential inconsistencies.  Stamps use finite
 * representations, and are not cryptographically secure (i.e., a
 * valid stamp may be guessable). Stamp values may recycle after (no
 * sooner than) one year of continuous operation. A stamp held without
 * use or validation for longer than this period may fail to validate
 * correctly.  StampedLocks are serializable, but always deserialize
 * into initial unlocked state, so they are not useful for remote
 * locking.
 *
 * <p>Like {@link java.util.concurrent.Semaphore Semaphore}, but unlike most
 * {@link Lock} implementations, StampedLocks have no notion of ownership.
 * Locks acquired in one thread can be released or converted in another.
 *
 * <p>The scheduling policy of StampedLock does not consistently
 * prefer readers over writers or vice versa.  All "try" methods are
 * best-effort and do not necessarily conform to any scheduling or
 * fairness policy. A zero return from any "try" method for acquiring
 * or converting locks does not carry any information about the state
 * of the lock; a subsequent invocation may succeed.
 *
 * <p>Because it supports coordinated usage across multiple lock
 * modes, this class does not directly implement the {@link Lock} or
 * {@link ReadWriteLock} interfaces. However, a StampedLock may be
 * viewed {@link #asReadLock()}, {@link #asWriteLock()}, or {@link
 * #asReadWriteLock()} in applications requiring only the associated
 * set of functionality.
 *
 * <p><b>Memory Synchronization.</b> Methods with the effect of
 * successfully locking in any mode have the same memory
 * synchronization effects as a <em>Lock</em> action described in
 * <a href="https://docs.oracle.com/javase/specs/jls/se11/html/jls-17.html#jls-17.4">
 * Chapter 17 of <cite>The Java&trade; Language Specification</cite></a>.
 * Methods successfully unlocking in write mode have the same memory
 * synchronization effects as an <em>Unlock</em> action.  In optimistic
 * read usages, actions prior to the most recent write mode unlock action
 * are guaranteed to happen-before those following a tryOptimisticRead
 * only if a later validate returns true; otherwise there is no guarantee
 * that the reads between tryOptimisticRead and validate obtain a
 * consistent snapshot.
 *
 * <p><b>Sample Usage.</b> The following illustrates some usage idioms
 * in a class that maintains simple two-dimensional points. The sample
 * code illustrates some try/catch conventions even though they are
 * not strictly needed here because no exceptions can occur in their
 * bodies.
 *
 * <pre> {@code
 * class Point {
 *   private double x, y;
 *   private final StampedLock sl = new StampedLock();
 *
 *   // an exclusively locked method
 *   void move(double deltaX, double deltaY) {
 *     long stamp = sl.writeLock();
 *     try {
 *       x += deltaX;
 *       y += deltaY;
 *     } finally {
 *       sl.unlockWrite(stamp);
 *     }
 *   }
 *
 *   // a read-only method
 *   // upgrade from optimistic read to read lock
 *   double distanceFromOrigin() {
 *     long stamp = sl.tryOptimisticRead();
 *     try {
 *       retryHoldingLock: for (;; stamp = sl.readLock()) {
 *         if (stamp == 0L)
 *           continue retryHoldingLock;
 *         // possibly racy reads
 *         double currentX = x;
 *         double currentY = y;
 *         if (!sl.validate(stamp))
 *           continue retryHoldingLock;
 *         return Math.hypot(currentX, currentY);
 *       }
 *     } finally {
 *       if (StampedLock.isReadLockStamp(stamp))
 *         sl.unlockRead(stamp);
 *     }
 *   }
 *
 *   // upgrade from optimistic read to write lock
 *   void moveIfAtOrigin(double newX, double newY) {
 *     long stamp = sl.tryOptimisticRead();
 *     try {
 *       retryHoldingLock: for (;; stamp = sl.writeLock()) {
 *         if (stamp == 0L)
 *           continue retryHoldingLock;
 *         // possibly racy reads
 *         double currentX = x;
 *         double currentY = y;
 *         if (!sl.validate(stamp))
 *           continue retryHoldingLock;
 *         if (currentX != 0.0 || currentY != 0.0)
 *           break;
 *         stamp = sl.tryConvertToWriteLock(stamp);
 *         if (stamp == 0L)
 *           continue retryHoldingLock;
 *         // exclusive access
 *         x = newX;
 *         y = newY;
 *         return;
 *       }
 *     } finally {
 *       if (StampedLock.isWriteLockStamp(stamp))
 *         sl.unlockWrite(stamp);
 *     }
 *   }
 *
 *   // Upgrade read lock to write lock
 *   void moveIfAtOrigin(double newX, double newY) {
 *     long stamp = sl.readLock();
 *     try {
 *       while (x == 0.0 && y == 0.0) {
 *         long ws = sl.tryConvertToWriteLock(stamp);
 *         if (ws != 0L) {
 *           stamp = ws;
 *           x = newX;
 *           y = newY;
 *           break;
 *         }
 *         else {
 *           sl.unlockRead(stamp);
 *           stamp = sl.writeLock();
 *         }
 *       }
 *     } finally {
 *       sl.unlock(stamp);
 *     }
 *   }
 * }}</pre>
 *
 * @since 1.8
 * @author Doug Lea
 */
public class StampedLock implements java.io.Serializable {
    /*
     * Algorithmic notes:
     *
     * The design employs elements of Sequence locks
     * (as used in linux kernels; see Lameter's
     * http://www.lameter.com/gelato2005.pdf
     * and elsewhere; see
     * Boehm's http://www.hpl.hp.com/techreports/2012/HPL-2012-68.html)
     * and Ordered RW locks (see Shirako et al
     * http://dl.acm.org/citation.cfm?id=2312015)
     *
     * Conceptually, the primary state of the lock includes a sequence
     * number that is odd when write-locked and even otherwise.
     * However, this is offset by a reader count that is non-zero when
     * read-locked.  The read count is ignored when validating
     * "optimistic" seqlock-reader-style stamps.  Because we must use
     * a small finite number of bits (currently 7) for readers, a
     * supplementary reader overflow word is used when the number of
     * readers exceeds the count field. We do this by treating the max
     * reader count value (RBITS) as a spinlock protecting overflow
     * updates.
     *
     * Waiters use a modified form of CLH lock used in
     * AbstractQueuedSynchronizer (see its internal documentation for
     * a fuller account), where each node is tagged (field mode) as
     * either a reader or writer. Sets of waiting readers are grouped
     * (linked) under a common node (field cowait) so act as a single
     * node with respect to most CLH mechanics.  By virtue of the
     * queue structure, wait nodes need not actually carry sequence
     * numbers; we know each is greater than its predecessor.  This
     * simplifies the scheduling policy to a mainly-FIFO scheme that
     * incorporates elements of Phase-Fair locks (see Brandenburg &
     * Anderson, especially http://www.cs.unc.edu/~bbb/diss/).  In
     * particular, we use the phase-fair anti-barging rule: If an
     * incoming reader arrives while read lock is held but there is a
     * queued writer, this incoming reader is queued.  (This rule is
     * responsible for some of the complexity of method acquireRead,
     * but without it, the lock becomes highly unfair.) Method release
     * does not (and sometimes cannot) itself wake up cowaiters. This
     * is done by the primary thread, but helped by any other threads
     * with nothing better to do in methods acquireRead and
     * acquireWrite.
     *
     * These rules apply to threads actually queued. All tryLock forms
     * opportunistically try to acquire locks regardless of preference
     * rules, and so may "barge" their way in.  Randomized spinning is
     * used in the acquire methods to reduce (increasingly expensive)
     * context switching while also avoiding sustained memory
     * thrashing among many threads.  We limit spins to the head of
     * queue. If, upon wakening, a thread fails to obtain lock, and is
     * still (or becomes) the first waiting thread (which indicates
     * that some other thread barged and obtained lock), it escalates
     * spins (up to MAX_HEAD_SPINS) to reduce the likelihood of
     * continually losing to barging threads.
     *
     * Nearly all of these mechanics are carried out in methods
     * acquireWrite and acquireRead, that, as typical of such code,
     * sprawl out because actions and retries rely on consistent sets
     * of locally cached reads.
     *
     * As noted in Boehm's paper (above), sequence validation (mainly
     * method validate()) requires stricter ordering rules than apply
     * to normal volatile reads (of "state").  To force orderings of
     * reads before a validation and the validation itself in those
     * cases where this is not already forced, we use acquireFence.
     * Unlike in that paper, we allow writers to use plain writes.
     * One would not expect reorderings of such writes with the lock
     * acquisition CAS because there is a "control dependency", but it
     * is theoretically possible, so we additionally add a
     * storeStoreFence after lock acquisition CAS.
     *
     * ----------------------------------------------------------------
     * Here's an informal proof that plain reads by _successful_
     * readers see plain writes from preceding but not following
     * writers (following Boehm and the C++ standard [atomics.fences]):
     *
     * Because of the total synchronization order of accesses to
     * volatile long state containing the sequence number, writers and
     * _successful_ readers can be globally sequenced.
     *
     * int x, y;
     *
     * Writer 1:
     * inc sequence (odd - "locked")
     * storeStoreFence();
     * x = 1; y = 2;
     * inc sequence (even - "unlocked")
     *
     * Successful Reader:
     * read sequence (even)
     * // must see writes from Writer 1 but not Writer 2
     * r1 = x; r2 = y;
     * acquireFence();
     * read sequence (even - validated unchanged)
     * // use r1 and r2
     *
     * Writer 2:
     * inc sequence (odd - "locked")
     * storeStoreFence();
     * x = 3; y = 4;
     * inc sequence (even - "unlocked")
     *
     * Visibility of writer 1's stores is normal - reader's initial
     * read of state synchronizes with writer 1's final write to state.
     * Lack of visibility of writer 2's plain writes is less obvious.
     * If reader's read of x or y saw writer 2's write, then (assuming
     * semantics of C++ fences) the storeStoreFence would "synchronize"
     * with reader's acquireFence and reader's validation read must see
     * writer 2's initial write to state and so validation must fail.
     * But making this "proof" formal and rigorous is an open problem!
     * ----------------------------------------------------------------
     *
     * The memory layout keeps lock state and queue pointers together
     * (normally on the same cache line). This usually works well for
     * read-mostly loads. In most other cases, the natural tendency of
     * adaptive-spin CLH locks to reduce memory contention lessens
     * motivation to further spread out contended locations, but might
     * be subject to future improvements.
     */

    private static final long serialVersionUID = -6001602636862214147L;

    /** Number of processors, for spin control */
    private static final int NCPU = Runtime.getRuntime().availableProcessors();

    /** Maximum number of retries before enqueuing on acquisition; at least 1 */
    private static final int SPINS = (NCPU > 1) ? 1 << 6 : 1;

    /** Maximum number of tries before blocking at head on acquisition */
    private static final int HEAD_SPINS = (NCPU > 1) ? 1 << 10 : 1;

    /** Maximum number of retries before re-blocking */
    private static final int MAX_HEAD_SPINS = (NCPU > 1) ? 1 << 16 : 1;

    /** The period for yielding when waiting for overflow spinlock */
    private static final int OVERFLOW_YIELD_RATE = 7; // must be power 2 - 1

    /** The number of bits to use for reader count before overflowing */
    private static final int LG_READERS = 7;// 读线程的个数占有低7位

    // Values for lock state and stamp operations
    private static final long RUNIT = 1L;// 读线程个数每次增加的单位
    private static final long WBIT  = 1L << LG_READERS;// 写线程个数所在的位置
    private static final long RBITS = WBIT - 1L;// 读线程个数所在的位置
    private static final long RFULL = RBITS - 1L;// 最大读线程个数
    private static final long ABITS = RBITS | WBIT;// 读线程个数和写线程个数的掩码
    private static final long SBITS = ~RBITS; // note overlap with ABITS// 读线程个数的反数，高25位全部为1

    /*
     * 3 stamp modes can be distinguished by examining (m = stamp & ABITS):
     * write mode: m == WBIT
     * optimistic read mode: m == 0L (even when read lock is held)
     * read mode: m > 0L && m <= RFULL (the stamp is a copy of state, but the
     * read hold count in the stamp is unused other than to determine mode)
     *
     * This differs slightly from the encoding of state:
     * (state & ABITS) == 0L indicates the lock is currently unlocked.
     * (state & ABITS) == RBITS is a special transient value
     * indicating spin-locked to manipulate reader bits overflow.
     */

    /** Initial value for lock state; avoids failure value zero. */
    private static final long ORIGIN = WBIT << 1;// state的初始值：256

    // Special value from cancelled acquire methods so caller can throw IE
    private static final long INTERRUPTED = 1L;

    // Values for node status; order matters
    private static final int WAITING   = -1;
    private static final int CANCELLED =  1;

    // Modes for nodes (int not boolean to allow arithmetic)
    private static final int RMODE = 0;
    private static final int WMODE = 1;

    /** Wait nodes */
    static final class WNode {
        volatile WNode prev; // 前一个节点
        volatile WNode next;// 后一个节点
        volatile WNode cowait;    // list of linked readers// 读线程所用的链表（实际是一个栈结果）
        volatile Thread thread;   // non-null while possibly parked// 阻塞的线程
        volatile int status;      // 0, WAITING, or CANCELLED // 状态
        final int mode;           // RMODE or WMODE // 读模式还是写模式
        WNode(int m, WNode p) { mode = m; prev = p; }
    }

    /** Head of CLH queue */
    private transient volatile WNode whead;// 队列的头节点
    /** Tail (last) of CLH queue */
    private transient volatile WNode wtail;// 队列的尾节点

    // views
    transient ReadLockView readLockView;
    transient WriteLockView writeLockView;
    transient ReadWriteLockView readWriteLockView;

    /** Lock sequence/state */
    private transient volatile long state;// 存储着当前的版本号，类似于AQS的状态变量state
    /** extra reader count when state read count saturated */
    private transient int readerOverflow;

    /**
     * Creates a new lock, initially in unlocked state.
     */
    public StampedLock() {
        state = ORIGIN;
    }

    private boolean casState(long expectedValue, long newValue) {
        return STATE.compareAndSet(this, expectedValue, newValue);
    }

    private long tryWriteLock(long s) {
        // assert (s & ABITS) == 0L;
        long next;
        if (casState(s, next = s | WBIT)) {
            VarHandle.storeStoreFence();
            return next;
        }
        return 0L;
    }

    /**
     * Exclusively acquires the lock, blocking if necessary
     * until available.
     *
     * @return a write stamp that can be used to unlock or convert mode
     */
    @ReservedStackAccess
    public long writeLock() {
        long next;// ABITS = 255 = 1111 1111
        // WBITS = 128 = 1000 0000
        // state与ABITS如果等于0，尝试原子更新state的值加WBITS
        // 如果成功则返回更新的值，如果失败调用acquireWrite()方法
        return ((next = tryWriteLock()) != 0L) ? next : acquireWrite(false, 0L);
    }

    /**
     * Exclusively acquires the lock if it is immediately available.
     *
     * @return a write stamp that can be used to unlock or convert mode,
     * or zero if the lock is not available
     */
    @ReservedStackAccess
    public long tryWriteLock() {
        long s;
        return (((s = state) & ABITS) == 0L) ? tryWriteLock(s) : 0L;
    }

    /**
     * Exclusively acquires the lock if it is available within the
     * given time and the current thread has not been interrupted.
     * Behavior under timeout and interruption matches that specified
     * for method {@link Lock#tryLock(long,TimeUnit)}.
     *
     * @param time the maximum time to wait for the lock
     * @param unit the time unit of the {@code time} argument
     * @return a write stamp that can be used to unlock or convert mode,
     * or zero if the lock is not available
     * @throws InterruptedException if the current thread is interrupted
     * before acquiring the lock
     */
    public long tryWriteLock(long time, TimeUnit unit)
        throws InterruptedException {
        long nanos = unit.toNanos(time);
        if (!Thread.interrupted()) {
            long next, deadline;
            if ((next = tryWriteLock()) != 0L)
                return next;
            if (nanos <= 0L)
                return 0L;
            if ((deadline = System.nanoTime() + nanos) == 0L)
                deadline = 1L;
            if ((next = acquireWrite(true, deadline)) != INTERRUPTED)
                return next;
        }
        throw new InterruptedException();
    }

    /**
     * Exclusively acquires the lock, blocking if necessary
     * until available or the current thread is interrupted.
     * Behavior under interruption matches that specified
     * for method {@link Lock#lockInterruptibly()}.
     *
     * @return a write stamp that can be used to unlock or convert mode
     * @throws InterruptedException if the current thread is interrupted
     * before acquiring the lock
     */
    @ReservedStackAccess
    public long writeLockInterruptibly() throws InterruptedException {
        long next;
        if (!Thread.interrupted() &&
            (next = acquireWrite(true, 0L)) != INTERRUPTED)
            return next;
        throw new InterruptedException();
    }

    /**
     * Non-exclusively acquires the lock, blocking if necessary
     * until available.
     *
     * @return a read stamp that can be used to unlock or convert mode
     */
    @ReservedStackAccess
    public long readLock() {
        long s, next;
        // bypass acquireRead on common uncontended case
        // 没有写锁占用，并且读锁被获取的次数未达到最大值
        // 尝试原子更新读锁被获取的次数加1
        // 如果成功直接返回，如果失败调用acquireRead()方法
        return (whead == wtail
                && ((s = state) & ABITS) < RFULL
                && casState(s, next = s + RUNIT))
            ? next
            : acquireRead(false, 0L);
    }

    /**
     * Non-exclusively acquires the lock if it is immediately available.
     *
     * @return a read stamp that can be used to unlock or convert mode,
     * or zero if the lock is not available
     */
    @ReservedStackAccess
    public long tryReadLock() {
        long s, m, next;
        while ((m = (s = state) & ABITS) != WBIT) {
            if (m < RFULL) {
                if (casState(s, next = s + RUNIT))
                    return next;
            }
            else if ((next = tryIncReaderOverflow(s)) != 0L)
                return next;
        }
        return 0L;
    }

    /**
     * Non-exclusively acquires the lock if it is available within the
     * given time and the current thread has not been interrupted.
     * Behavior under timeout and interruption matches that specified
     * for method {@link Lock#tryLock(long,TimeUnit)}.
     *
     * @param time the maximum time to wait for the lock
     * @param unit the time unit of the {@code time} argument
     * @return a read stamp that can be used to unlock or convert mode,
     * or zero if the lock is not available
     * @throws InterruptedException if the current thread is interrupted
     * before acquiring the lock
     */
    @ReservedStackAccess
    public long tryReadLock(long time, TimeUnit unit)
        throws InterruptedException {
        long s, m, next, deadline;
        long nanos = unit.toNanos(time);
        if (!Thread.interrupted()) {
            if ((m = (s = state) & ABITS) != WBIT) {
                if (m < RFULL) {
                    if (casState(s, next = s + RUNIT))
                        return next;
                }
                else if ((next = tryIncReaderOverflow(s)) != 0L)
                    return next;
            }
            if (nanos <= 0L)
                return 0L;
            if ((deadline = System.nanoTime() + nanos) == 0L)
                deadline = 1L;
            if ((next = acquireRead(true, deadline)) != INTERRUPTED)
                return next;
        }
        throw new InterruptedException();
    }

    /**
     * Non-exclusively acquires the lock, blocking if necessary
     * until available or the current thread is interrupted.
     * Behavior under interruption matches that specified
     * for method {@link Lock#lockInterruptibly()}.
     *
     * @return a read stamp that can be used to unlock or convert mode
     * @throws InterruptedException if the current thread is interrupted
     * before acquiring the lock
     */
    @ReservedStackAccess
    public long readLockInterruptibly() throws InterruptedException {
        long s, next;
        if (!Thread.interrupted()
            // bypass acquireRead on common uncontended case
            && ((whead == wtail
                 && ((s = state) & ABITS) < RFULL
                 && casState(s, next = s + RUNIT))
                ||
                (next = acquireRead(true, 0L)) != INTERRUPTED))
            return next;
        throw new InterruptedException();
    }

    /**
     * Returns a stamp that can later be validated, or zero
     * if exclusively locked.
     *
     * @return a valid optimistic read stamp, or zero if exclusively locked
     */
    public long tryOptimisticRead() {
        long s;
        return (((s = state) & WBIT) == 0L) ? (s & SBITS) : 0L;
    }

    /**
     * Returns true if the lock has not been exclusively acquired
     * since issuance of the given stamp. Always returns false if the
     * stamp is zero. Always returns true if the stamp represents a
     * currently held lock. Invoking this method with a value not
     * obtained from {@link #tryOptimisticRead} or a locking method
     * for this lock has no defined effect or result.
     *
     * @param stamp a stamp
     * @return {@code true} if the lock has not been exclusively acquired
     * since issuance of the given stamp; else false
     */
    public boolean validate(long stamp) {
        VarHandle.acquireFence();
        return (stamp & SBITS) == (state & SBITS);
    }

    /**
     * Returns an unlocked state, incrementing the version and
     * avoiding special failure value 0L.
     *
     * @param s a write-locked state (or stamp)
     */
    private static long unlockWriteState(long s) {
        return ((s += WBIT) == 0L) ? ORIGIN : s;
    }

    private long unlockWriteInternal(long s) {
        long next; WNode h;
        STATE.setVolatile(this, next = unlockWriteState(s));
        if ((h = whead) != null && h.status != 0)
            release(h);
        return next;
    }

    /**
     * If the lock state matches the given stamp, releases the
     * exclusive lock.
     *
     * @param stamp a stamp returned by a write-lock operation
     * @throws IllegalMonitorStateException if the stamp does
     * not match the current state of this lock
     */
    @ReservedStackAccess
    public void unlockWrite(long stamp) {// 检查版本号对不对
        if (state != stamp || (stamp & WBIT) == 0L)
            throw new IllegalMonitorStateException();
        unlockWriteInternal(stamp);
    }

    /**
     * If the lock state matches the given stamp, releases the
     * non-exclusive lock.
     *
     * @param stamp a stamp returned by a read-lock operation
     * @throws IllegalMonitorStateException if the stamp does
     * not match the current state of this lock
     */
    @ReservedStackAccess
    public void unlockRead(long stamp) {
        long s, m; WNode h;
        while (((s = state) & SBITS) == (stamp & SBITS) // 检查版本号
               && (stamp & RBITS) > 0L
               && ((m = s & RBITS) > 0L)) {
            if (m < RFULL) {// 读线程个数正常
                if (casState(s, s - RUNIT)) {// 释放一次读锁
                    if (m == RUNIT && (h = whead) != null && h.status != 0)
                        release(h); // 如果读锁全部都释放了，且头节点不为空且状态不为0，唤醒它的下一个节点
                    return;
                }
            }
            else if (tryDecReaderOverflow(s) != 0L)
                return;// 读线程个数溢出检测
        }
        throw new IllegalMonitorStateException();
    }

    /**
     * If the lock state matches the given stamp, releases the
     * corresponding mode of the lock.
     *
     * @param stamp a stamp returned by a lock operation
     * @throws IllegalMonitorStateException if the stamp does
     * not match the current state of this lock
     */
    @ReservedStackAccess
    public void unlock(long stamp) {
        if ((stamp & WBIT) != 0L)
            unlockWrite(stamp);
        else
            unlockRead(stamp);
    }

    /**
     * If the lock state matches the given stamp, atomically performs one of
     * the following actions. If the stamp represents holding a write
     * lock, returns it.  Or, if a read lock, if the write lock is
     * available, releases the read lock and returns a write stamp.
     * Or, if an optimistic read, returns a write stamp only if
     * immediately available. This method returns zero in all other
     * cases.
     *
     * @param stamp a stamp
     * @return a valid write stamp, or zero on failure
     */
    public long tryConvertToWriteLock(long stamp) {
        long a = stamp & ABITS, m, s, next;
        while (((s = state) & SBITS) == (stamp & SBITS)) {
            if ((m = s & ABITS) == 0L) {
                if (a != 0L)
                    break;
                if ((next = tryWriteLock(s)) != 0L)
                    return next;
            }
            else if (m == WBIT) {
                if (a != m)
                    break;
                return stamp;
            }
            else if (m == RUNIT && a != 0L) {
                if (casState(s, next = s - RUNIT + WBIT)) {
                    VarHandle.storeStoreFence();
                    return next;
                }
            }
            else
                break;
        }
        return 0L;
    }

    /**
     * If the lock state matches the given stamp, atomically performs one of
     * the following actions. If the stamp represents holding a write
     * lock, releases it and obtains a read lock.  Or, if a read lock,
     * returns it. Or, if an optimistic read, acquires a read lock and
     * returns a read stamp only if immediately available. This method
     * returns zero in all other cases.
     *
     * @param stamp a stamp
     * @return a valid read stamp, or zero on failure
     */
    public long tryConvertToReadLock(long stamp) {
        long a, s, next; WNode h;
        while (((s = state) & SBITS) == (stamp & SBITS)) {
            if ((a = stamp & ABITS) >= WBIT) {
                // write stamp
                if (s != stamp)
                    break;
                STATE.setVolatile(this, next = unlockWriteState(s) + RUNIT);
                if ((h = whead) != null && h.status != 0)
                    release(h);
                return next;
            }
            else if (a == 0L) {
                // optimistic read stamp
                if ((s & ABITS) < RFULL) {
                    if (casState(s, next = s + RUNIT))
                        return next;
                }
                else if ((next = tryIncReaderOverflow(s)) != 0L)
                    return next;
            }
            else {
                // already a read stamp
                if ((s & ABITS) == 0L)
                    break;
                return stamp;
            }
        }
        return 0L;
    }

    /**
     * If the lock state matches the given stamp then, atomically, if the stamp
     * represents holding a lock, releases it and returns an
     * observation stamp.  Or, if an optimistic read, returns it if
     * validated. This method returns zero in all other cases, and so
     * may be useful as a form of "tryUnlock".
     *
     * @param stamp a stamp
     * @return a valid optimistic read stamp, or zero on failure
     */
    public long tryConvertToOptimisticRead(long stamp) {
        long a, m, s, next; WNode h;
        VarHandle.acquireFence();
        while (((s = state) & SBITS) == (stamp & SBITS)) {
            if ((a = stamp & ABITS) >= WBIT) {
                // write stamp
                if (s != stamp)
                    break;
                return unlockWriteInternal(s);
            }
            else if (a == 0L)
                // already an optimistic read stamp
                return stamp;
            else if ((m = s & ABITS) == 0L) // invalid read stamp
                break;
            else if (m < RFULL) {
                if (casState(s, next = s - RUNIT)) {
                    if (m == RUNIT && (h = whead) != null && h.status != 0)
                        release(h);
                    return next & SBITS;
                }
            }
            else if ((next = tryDecReaderOverflow(s)) != 0L)
                return next & SBITS;
        }
        return 0L;
    }

    /**
     * Releases the write lock if it is held, without requiring a
     * stamp value. This method may be useful for recovery after
     * errors.
     *
     * @return {@code true} if the lock was held, else false
     */
    @ReservedStackAccess
    public boolean tryUnlockWrite() {
        long s;
        if (((s = state) & WBIT) != 0L) {
            unlockWriteInternal(s);
            return true;
        }
        return false;
    }

    /**
     * Releases one hold of the read lock if it is held, without
     * requiring a stamp value. This method may be useful for recovery
     * after errors.
     *
     * @return {@code true} if the read lock was held, else false
     */
    @ReservedStackAccess
    public boolean tryUnlockRead() {
        long s, m; WNode h;
        while ((m = (s = state) & ABITS) != 0L && m < WBIT) {
            if (m < RFULL) {
                if (casState(s, s - RUNIT)) {
                    if (m == RUNIT && (h = whead) != null && h.status != 0)
                        release(h);
                    return true;
                }
            }
            else if (tryDecReaderOverflow(s) != 0L)
                return true;
        }
        return false;
    }

    // status monitoring methods

    /**
     * Returns combined state-held and overflow read count for given
     * state s.
     */
    private int getReadLockCount(long s) {
        long readers;
        if ((readers = s & RBITS) >= RFULL)
            readers = RFULL + readerOverflow;
        return (int) readers;
    }

    /**
     * Returns {@code true} if the lock is currently held exclusively.
     *
     * @return {@code true} if the lock is currently held exclusively
     */
    public boolean isWriteLocked() {
        return (state & WBIT) != 0L;
    }

    /**
     * Returns {@code true} if the lock is currently held non-exclusively.
     *
     * @return {@code true} if the lock is currently held non-exclusively
     */
    public boolean isReadLocked() {
        return (state & RBITS) != 0L;
    }

    /**
     * Tells whether a stamp represents holding a lock exclusively.
     * This method may be useful in conjunction with
     * {@link #tryConvertToWriteLock}, for example: <pre> {@code
     * long stamp = sl.tryOptimisticRead();
     * try {
     *   ...
     *   stamp = sl.tryConvertToWriteLock(stamp);
     *   ...
     * } finally {
     *   if (StampedLock.isWriteLockStamp(stamp))
     *     sl.unlockWrite(stamp);
     * }}</pre>
     *
     * @param stamp a stamp returned by a previous StampedLock operation
     * @return {@code true} if the stamp was returned by a successful
     *   write-lock operation
     * @since 10
     */
    public static boolean isWriteLockStamp(long stamp) {
        return (stamp & ABITS) == WBIT;
    }

    /**
     * Tells whether a stamp represents holding a lock non-exclusively.
     * This method may be useful in conjunction with
     * {@link #tryConvertToReadLock}, for example: <pre> {@code
     * long stamp = sl.tryOptimisticRead();
     * try {
     *   ...
     *   stamp = sl.tryConvertToReadLock(stamp);
     *   ...
     * } finally {
     *   if (StampedLock.isReadLockStamp(stamp))
     *     sl.unlockRead(stamp);
     * }}</pre>
     *
     * @param stamp a stamp returned by a previous StampedLock operation
     * @return {@code true} if the stamp was returned by a successful
     *   read-lock operation
     * @since 10
     */
    public static boolean isReadLockStamp(long stamp) {
        return (stamp & RBITS) != 0L;
    }

    /**
     * Tells whether a stamp represents holding a lock.
     * This method may be useful in conjunction with
     * {@link #tryConvertToReadLock} and {@link #tryConvertToWriteLock},
     * for example: <pre> {@code
     * long stamp = sl.tryOptimisticRead();
     * try {
     *   ...
     *   stamp = sl.tryConvertToReadLock(stamp);
     *   ...
     *   stamp = sl.tryConvertToWriteLock(stamp);
     *   ...
     * } finally {
     *   if (StampedLock.isLockStamp(stamp))
     *     sl.unlock(stamp);
     * }}</pre>
     *
     * @param stamp a stamp returned by a previous StampedLock operation
     * @return {@code true} if the stamp was returned by a successful
     *   read-lock or write-lock operation
     * @since 10
     */
    public static boolean isLockStamp(long stamp) {
        return (stamp & ABITS) != 0L;
    }

    /**
     * Tells whether a stamp represents a successful optimistic read.
     *
     * @param stamp a stamp returned by a previous StampedLock operation
     * @return {@code true} if the stamp was returned by a successful
     *   optimistic read operation, that is, a non-zero return from
     *   {@link #tryOptimisticRead()} or
     *   {@link #tryConvertToOptimisticRead(long)}
     * @since 10
     */
    public static boolean isOptimisticReadStamp(long stamp) {
        return (stamp & ABITS) == 0L && stamp != 0L;
    }

    /**
     * Queries the number of read locks held for this lock. This
     * method is designed for use in monitoring system state, not for
     * synchronization control.
     * @return the number of read locks held
     */
    public int getReadLockCount() {
        return getReadLockCount(state);
    }

    /**
     * Returns a string identifying this lock, as well as its lock
     * state.  The state, in brackets, includes the String {@code
     * "Unlocked"} or the String {@code "Write-locked"} or the String
     * {@code "Read-locks:"} followed by the current number of
     * read-locks held.
     *
     * @return a string identifying this lock, as well as its lock state
     */
    public String toString() {
        long s = state;
        return super.toString() +
            ((s & ABITS) == 0L ? "[Unlocked]" :
             (s & WBIT) != 0L ? "[Write-locked]" :
             "[Read-locks:" + getReadLockCount(s) + "]");
    }

    // views

    /**
     * Returns a plain {@link Lock} view of this StampedLock in which
     * the {@link Lock#lock} method is mapped to {@link #readLock},
     * and similarly for other methods. The returned Lock does not
     * support a {@link Condition}; method {@link Lock#newCondition()}
     * throws {@code UnsupportedOperationException}.
     *
     * @return the lock
     */
    public Lock asReadLock() {
        ReadLockView v;
        if ((v = readLockView) != null) return v;
        return readLockView = new ReadLockView();
    }

    /**
     * Returns a plain {@link Lock} view of this StampedLock in which
     * the {@link Lock#lock} method is mapped to {@link #writeLock},
     * and similarly for other methods. The returned Lock does not
     * support a {@link Condition}; method {@link Lock#newCondition()}
     * throws {@code UnsupportedOperationException}.
     *
     * @return the lock
     */
    public Lock asWriteLock() {
        WriteLockView v;
        if ((v = writeLockView) != null) return v;
        return writeLockView = new WriteLockView();
    }

    /**
     * Returns a {@link ReadWriteLock} view of this StampedLock in
     * which the {@link ReadWriteLock#readLock()} method is mapped to
     * {@link #asReadLock()}, and {@link ReadWriteLock#writeLock()} to
     * {@link #asWriteLock()}.
     *
     * @return the lock
     */
    public ReadWriteLock asReadWriteLock() {
        ReadWriteLockView v;
        if ((v = readWriteLockView) != null) return v;
        return readWriteLockView = new ReadWriteLockView();
    }

    // view classes

    final class ReadLockView implements Lock {
        public void lock() { readLock(); }
        public void lockInterruptibly() throws InterruptedException {
            readLockInterruptibly();
        }
        public boolean tryLock() { return tryReadLock() != 0L; }
        public boolean tryLock(long time, TimeUnit unit)
            throws InterruptedException {
            return tryReadLock(time, unit) != 0L;
        }
        public void unlock() { unstampedUnlockRead(); }
        public Condition newCondition() {
            throw new UnsupportedOperationException();
        }
    }

    final class WriteLockView implements Lock {
        public void lock() { writeLock(); }
        public void lockInterruptibly() throws InterruptedException {
            writeLockInterruptibly();
        }
        public boolean tryLock() { return tryWriteLock() != 0L; }
        public boolean tryLock(long time, TimeUnit unit)
            throws InterruptedException {
            return tryWriteLock(time, unit) != 0L;
        }
        public void unlock() { unstampedUnlockWrite(); }
        public Condition newCondition() {
            throw new UnsupportedOperationException();
        }
    }

    final class ReadWriteLockView implements ReadWriteLock {
        public Lock readLock() { return asReadLock(); }
        public Lock writeLock() { return asWriteLock(); }
    }

    // Unlock methods without stamp argument checks for view classes.
    // Needed because view-class lock methods throw away stamps.

    final void unstampedUnlockWrite() {
        long s;
        if (((s = state) & WBIT) == 0L)
            throw new IllegalMonitorStateException();
        unlockWriteInternal(s);
    }

    final void unstampedUnlockRead() {
        long s, m; WNode h;
        while ((m = (s = state) & RBITS) > 0L) {
            if (m < RFULL) {
                if (casState(s, s - RUNIT)) {
                    if (m == RUNIT && (h = whead) != null && h.status != 0)
                        release(h);
                    return;
                }
            }
            else if (tryDecReaderOverflow(s) != 0L)
                return;
        }
        throw new IllegalMonitorStateException();
    }

    private void readObject(java.io.ObjectInputStream s)
        throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        STATE.setVolatile(this, ORIGIN); // reset to unlocked state
    }

    // internals

    /**
     * Tries to increment readerOverflow by first setting state
     * access bits value to RBITS, indicating hold of spinlock,
     * then updating, then releasing.
     *
     * @param s a reader overflow stamp: (s & ABITS) >= RFULL
     * @return new stamp on success, else zero
     */
    private long tryIncReaderOverflow(long s) {
        // assert (s & ABITS) >= RFULL;
        if ((s & ABITS) == RFULL) {
            if (casState(s, s | RBITS)) {
                ++readerOverflow;
                STATE.setVolatile(this, s);
                return s;
            }
        }
        else if ((LockSupport.nextSecondarySeed() & OVERFLOW_YIELD_RATE) == 0)
            Thread.yield();
        else
            Thread.onSpinWait();
        return 0L;
    }

    /**
     * Tries to decrement readerOverflow.
     *
     * @param s a reader overflow stamp: (s & ABITS) >= RFULL
     * @return new stamp on success, else zero
     */
    private long tryDecReaderOverflow(long s) {
        // assert (s & ABITS) >= RFULL;
        if ((s & ABITS) == RFULL) {
            if (casState(s, s | RBITS)) {
                int r; long next;
                if ((r = readerOverflow) > 0) {
                    readerOverflow = r - 1;
                    next = s;
                }
                else
                    next = s - RUNIT;
                STATE.setVolatile(this, next);
                return next;
            }
        }
        else if ((LockSupport.nextSecondarySeed() & OVERFLOW_YIELD_RATE) == 0)
            Thread.yield();
        else
            Thread.onSpinWait();
        return 0L;
    }

    /**
     * Wakes up the successor of h (normally whead). This is normally
     * just h.next, but may require traversal from wtail if next
     * pointers are lagging. This may fail to wake up an acquiring
     * thread when one or more have been cancelled, but the cancel
     * methods themselves provide extra safeguards to ensure liveness.
     */
    private void release(WNode h) {
        if (h != null) {
            WNode q; Thread w;// 将其状态改为0
            WSTATUS.compareAndSet(h, WAITING, 0);
            if ((q = h.next) == null || q.status == CANCELLED) {// 如果头节点的下一个节点为空或者其状态为已取消
                for (WNode t = wtail; t != null && t != h; t = t.prev)// 从尾节点向前遍历找到一个可用的节点
                    if (t.status <= 0)
                        q = t;
            }
            if (q != null && (w = q.thread) != null)// 唤醒q节点所在的线程
                LockSupport.unpark(w);
        }
    }

    /**
     * See above for explanation.
     *
     * @param interruptible true if should check interrupts and if so
     * return INTERRUPTED
     * @param deadline if nonzero, the System.nanoTime value to timeout
     * at (and return zero)
     * @return next state, or INTERRUPTED
     */
    private long acquireWrite(boolean interruptible, long deadline) {
        WNode node = null, p;// node为新增节点，p为尾节点（即将成为node的前置节点）
        for (int spins = -1;;) { // spin while enqueuing   // 第一次自旋——入队
            long m, s, ns;
            if ((m = (s = state) & ABITS) == 0L) {// 再次尝试获取写锁
                if ((ns = tryWriteLock(s)) != 0L)
                    return ns;
            }
            else if (spins < 0)// 如果自旋次数小于0，则计算自旋的次数
                // 如果当前有写锁独占且队列无元素，说明快轮到自己了
                // 就自旋就行了，如果自旋完了还没轮到自己才入队
                // 则自旋次数为SPINS常量
                // 否则自旋次数为0
                spins = (m == WBIT && wtail == whead) ? SPINS : 0;
            else if (spins > 0) {
                --spins;// 当自旋次数大于0时，当前这次自旋随机减一次自旋次数
                Thread.onSpinWait();
            }
            else if ((p = wtail) == null) { // initialize queue // 如果队列未初始化，新建一个空节点并初始化头节点和尾节点
                WNode hd = new WNode(WMODE, null);
                if (WHEAD.weakCompareAndSet(this, null, hd))
                    wtail = hd;
            }
            else if (node == null)// 如果新增节点还未初始化，则新建之，并赋值其前置节点为尾节点
                node = new WNode(WMODE, p);
            else if (node.prev != p)// 如果尾节点有变化，则更新新增节点的前置节点为新的尾节点
                node.prev = p;
            else if (WTAIL.weakCompareAndSet(this, p, node)) {// 尝试更新新增节点为新的尾节点成功，则退出循环
                p.next = node;
                break;
            }
        }

        boolean wasInterrupted = false;// 第二次自旋——阻塞并等待唤醒
        for (int spins = -1;;) {
            WNode h, np, pp; int ps; // h为头节点，np为新增节点的前置节点，pp为前前置节点，ps为前置节点的状态
            if ((h = whead) == p) {// 如果头节点等于前置节点，说明快轮到自己了
                if (spins < 0)
                    spins = HEAD_SPINS;// 初始化自旋次数
                else if (spins < MAX_HEAD_SPINS)
                    spins <<= 1;// 增加自旋次数
                for (int k = spins; k > 0; --k) { // spin at head// 第三次自旋，不断尝试获取写锁
                    long s, ns;
                    if (((s = state) & ABITS) == 0L) {
                        if ((ns = tryWriteLock(s)) != 0L) {
                            whead = node;// 尝试获取写锁成功，将node设置为新头节点并清除其前置节点(gc)
                            node.prev = null;
                            if (wasInterrupted)
                                Thread.currentThread().interrupt();
                            return ns;
                        }
                    }
                    else
                        Thread.onSpinWait();
                }
            }
            else if (h != null) { // help release stale waiters// 这段代码很难进来，是用于协助唤醒读节点的
                // 我是这么调试进来的：
                // 起三个写线程，两个读线程
                // 写线程1获取锁不要释放
                // 读线程1获取锁，读线程2获取锁（会阻塞）
                // 写线程2获取锁（会阻塞）
                // 写线程1释放锁，此时会唤醒读线程1
                // 在读线程1里面先不要唤醒读线程2
                // 写线程3获取锁，此时就会走到这里来了
                WNode c; Thread w;
                while ((c = h.cowait) != null) {// 如果头节点的cowait链表（栈）不为空，唤醒里面的所有节点
                    if (WCOWAIT.weakCompareAndSet(h, c, c.cowait) &&
                        (w = c.thread) != null)
                        LockSupport.unpark(w);
                }
            }
            if (whead == h) {// 如果头节点没有变化
                if ((np = node.prev) != p) {// 如果尾节点有变化，则更新
                    if (np != null)
                        (p = np).next = node;   // stale
                }
                else if ((ps = p.status) == 0)// 如果尾节点状态为0，则更新成WAITING
                    WSTATUS.compareAndSet(p, 0, WAITING);
                else if (ps == CANCELLED) {
                    if ((pp = p.prev) != null) {// 如果尾节点状态为取消，则把它从链表中删除
                        node.prev = pp;
                        pp.next = node;
                    }
                }
                else { // 有超时时间的处理
                    long time; // 0 argument to park means no timeout
                    if (deadline == 0L)
                        time = 0L;
                    else if ((time = deadline - System.nanoTime()) <= 0L)
                        return cancelWaiter(node, node, false);// 已超时，剔除当前节点
                    Thread wt = Thread.currentThread();// 当前线程
                    node.thread = wt;// 把node的线程指向当前线程
                    if (p.status < 0 && (p != h || (state & ABITS) != 0L) &&
                        whead == h && node.prev == p) { // 阻塞当前线程
                        if (time == 0L)
                            LockSupport.park(this);
                        else
                            LockSupport.parkNanos(this, time);
                    }
                    node.thread = null;// 当前节点被唤醒后，清除线程
                    if (Thread.interrupted()) {
                        if (interruptible)// 如果中断了，取消当前节点
                            return cancelWaiter(node, node, true);
                        wasInterrupted = true;
                    }
                }
            }
        }
    }

    /**
     * See above for explanation.
     *
     * @param interruptible true if should check interrupts and if so
     * return INTERRUPTED
     * @param deadline if nonzero, the System.nanoTime value to timeout
     * at (and return zero)
     * @return next state, or INTERRUPTED
     */
    private long acquireRead(boolean interruptible, long deadline) {
        boolean wasInterrupted = false;
        WNode node = null, p;// node为新增节点，p为尾节点
        for (int spins = -1;;) { // 第一段自旋——入队
            WNode h;// 头节点
            if ((h = whead) == (p = wtail)) {// 如果头节点等于尾节点
                // 说明没有排队的线程了，快轮到自己了，直接自旋不断尝试获取读锁
                for (long m, s, ns;;) {// 第二段自旋——不断尝试获取读锁
                    if ((m = (s = state) & ABITS) < RFULL ? // 尝试获取读锁，如果成功了直接返回版本号
                        casState(s, ns = s + RUNIT) :
                        (m < WBIT && (ns = tryIncReaderOverflow(s)) != 0L)) {
                        if (wasInterrupted)
                            Thread.currentThread().interrupt();
                        return ns;// 如果读线程个数达到了最大值，会溢出，返回的是0
                    }
                    else if (m >= WBIT) { // m >= WBIT表示有其它线程先一步获取了写锁
                        if (spins > 0) {// 随机立减自旋次数
                            --spins;
                            Thread.onSpinWait();
                        }
                        else {
                            if (spins == 0) { // 如果自旋次数为0了，看看是否要跳出循环
                                WNode nh = whead, np = wtail;
                                if ((nh == h && np == p) || (h = nh) != (p = np))
                                    break;
                            }
                            spins = SPINS;// 设置自旋次数
                        }
                    }
                }
            }
            if (p == null) { // initialize queue// 如果尾节点为空，初始化头节点和尾节点
                WNode hd = new WNode(WMODE, null);
                if (WHEAD.weakCompareAndSet(this, null, hd))
                    wtail = hd;
            }
            else if (node == null)// 如果新增节点为空，初始化之
                node = new WNode(RMODE, p);
            else if (h == p || p.mode != RMODE) {// 如果头节点等于尾节点或者尾节点不是读模式
                // 当前节点入队
                if (node.prev != p)
                    node.prev = p;
                else if (WTAIL.weakCompareAndSet(this, p, node)) {
                    p.next = node;
                    break;
                }
            }
            else if (!WCOWAIT.compareAndSet(p, node.cowait = p.cowait, node))
                node.cowait = null;// 接着上一个elseif，这里肯定是尾节点为读模式了
                // 将当前节点加入到尾节点的cowait中，这是一个栈
                // 上面的CAS成功了是不会进入到这里来的
            else {
                for (;;) { // 第三段自旋——阻塞当前线程并等待被唤醒
                    WNode pp, c; Thread w;
                    // 如果头节点不为空且其cowait不为空，协助唤醒其中等待的读线程
                    if ((h = whead) != null && (c = h.cowait) != null &&
                        WCOWAIT.compareAndSet(h, c, c.cowait) &&
                        (w = c.thread) != null) // help release
                        LockSupport.unpark(w);
                    if (Thread.interrupted()) {
                        if (interruptible)
                            return cancelWaiter(node, p, true);
                        wasInterrupted = true;
                    }// 如果头节点等待前前置节点或者等于前置节点或者前前置节点为空
                    // 这同样说明快轮到自己了
                    if (h == (pp = p.prev) || h == p || pp == null) {
                        long m, s, ns;
                        do {// 第四段自旋——又是不断尝试获取锁
                            if ((m = (s = state) & ABITS) < RFULL ?
                                casState(s, ns = s + RUNIT) :
                                (m < WBIT &&
                                 (ns = tryIncReaderOverflow(s)) != 0L)) {
                                if (wasInterrupted)
                                    Thread.currentThread().interrupt();
                                return ns;
                            }
                        } while (m < WBIT);// 只有当前时刻没有其它线程占有写锁就不断尝试
                    }// 如果头节点未曾改变且前前置节点也未曾改
                    // 阻塞当前线程
                    if (whead == h && p.prev == pp) {
                        long time;// 如果前前置节点为空，或者头节点等于前置节点，或者前置节点已取消
                        // 从第一个for自旋开始重试
                        if (pp == null || h == p || p.status > 0) {
                            node = null; // throw away
                            break;
                        }
                        if (deadline == 0L)// 超时检测
                            time = 0L;
                        else if ((time = deadline - System.nanoTime()) <= 0L) {
                            if (wasInterrupted)
                                Thread.currentThread().interrupt();
                            return cancelWaiter(node, p, false);// 如果超时了，取消当前节点
                        }
                        Thread wt = Thread.currentThread();// 当前线程
                        node.thread = wt;// 设置进node中
                        if ((h != pp || (state & ABITS) == WBIT) &&// 检测之前的条件未曾改变
                            whead == h && p.prev == pp) {
                            if (time == 0L)
                                LockSupport.park(this);// 阻塞当前线程并等待被唤醒
                            else
                                LockSupport.parkNanos(this, time);
                        }
                        node.thread = null;// 唤醒之后清除线程
                    }
                }
            }
        }
// 只有第一个读线程会走到下面的for循环处，参考上面第一段自旋中有一个break，当第一个读线程入队的时候break出来的

        // 第五段自旋——跟上面的逻辑差不多，只不过这里单独搞一个自旋针对第一个读线程
        for (int spins = -1;;) {
            WNode h, np, pp; int ps;
            if ((h = whead) == p) {// 如果头节点等于尾节点，说明快轮到自己了
                // 不断尝试获取读锁
                if (spins < 0)// 设置自旋次数
                    spins = HEAD_SPINS;
                else if (spins < MAX_HEAD_SPINS)
                    spins <<= 1;
                for (int k = spins;;) { // spin at head// 第六段自旋——不断尝试获取读锁
                    long m, s, ns;// 不断尝试获取读锁
                    if ((m = (s = state) & ABITS) < RFULL ?
                        casState(s, ns = s + RUNIT) :
                        (m < WBIT && (ns = tryIncReaderOverflow(s)) != 0L)) {
                        WNode c; Thread w;// 获取到了读锁
                        whead = node;
                        node.prev = null;
                        while ((c = node.cowait) != null) {// 唤醒当前节点中所有等待着的读线程
                            // 因为当前节点是第一个读节点，所以它是在队列中的，其它读节点都是挂这个节点的cowait栈中的
                            if (WCOWAIT.compareAndSet(node, c, c.cowait) &&
                                (w = c.thread) != null)
                                LockSupport.unpark(w);
                        }
                        if (wasInterrupted)
                            Thread.currentThread().interrupt();
                        return ns; // 返回版本号
                    }// 如果当前有其它线程占有着写锁，并且没有自旋次数了，跳出当前循环
                    else if (m >= WBIT && --k <= 0)
                        break;
                    else
                        Thread.onSpinWait();
                }
            }
            else if (h != null) {
                WNode c; Thread w;// 如果头节点不等待尾节点且不为空且其为读模式，协助唤醒里面的读线程
                while ((c = h.cowait) != null) {
                    if (WCOWAIT.compareAndSet(h, c, c.cowait) &&
                        (w = c.thread) != null)
                        LockSupport.unpark(w);
                }
            }
            if (whead == h) {// 如果头节点未曾变化
                if ((np = node.prev) != p) {// 更新前置节点及其状态等
                    if (np != null)
                        (p = np).next = node;   // stale
                }
                else if ((ps = p.status) == 0)
                    WSTATUS.compareAndSet(p, 0, WAITING);
                else if (ps == CANCELLED) {
                    if ((pp = p.prev) != null) {
                        node.prev = pp;
                        pp.next = node;
                    }
                }
                else { // 第一个读节点即将进入阻塞
                    long time;
                    if (deadline == 0L) // 超时设置
                        time = 0L;
                    else if ((time = deadline - System.nanoTime()) <= 0L)
                        return cancelWaiter(node, node, false);// 如果超时了取消当前节点
                    Thread wt = Thread.currentThread();
                    node.thread = wt;
                    if (p.status < 0 &&
                        (p != h || (state & ABITS) == WBIT) &&
                        whead == h && node.prev == p) {
                            if (time == 0L)
                                LockSupport.park(this); //阻塞第一个读节点并等待被唤醒
                            else
                                LockSupport.parkNanos(this, time);
                    }
                    node.thread = null;
                    if (Thread.interrupted()) {
                        if (interruptible)
                            return cancelWaiter(node, node, true);
                        wasInterrupted = true;
                    }
                }
            }
        }
    }

    /**
     * If node non-null, forces cancel status and unsplices it from
     * queue if possible and wakes up any cowaiters (of the node, or
     * group, as applicable), and in any case helps release current
     * first waiter if lock is free. (Calling with null arguments
     * serves as a conditional form of release, which is not currently
     * needed but may be needed under possible future cancellation
     * policies). This is a variant of cancellation methods in
     * AbstractQueuedSynchronizer (see its detailed explanation in AQS
     * internal documentation).
     *
     * @param node if non-null, the waiter
     * @param group either node or the group node is cowaiting with
     * @param interrupted if already interrupted
     * @return INTERRUPTED if interrupted or Thread.interrupted, else zero
     */
    private long cancelWaiter(WNode node, WNode group, boolean interrupted) {
        if (node != null && group != null) {
            Thread w;
            node.status = CANCELLED;
            // unsplice cancelled nodes from group
            for (WNode p = group, q; (q = p.cowait) != null;) {
                if (q.status == CANCELLED) {
                    WCOWAIT.compareAndSet(p, q, q.cowait);
                    p = group; // restart
                }
                else
                    p = q;
            }
            if (group == node) {
                for (WNode r = group.cowait; r != null; r = r.cowait) {
                    if ((w = r.thread) != null)
                        LockSupport.unpark(w); // wake up uncancelled co-waiters
                }
                for (WNode pred = node.prev; pred != null; ) { // unsplice
                    WNode succ, pp;        // find valid successor
                    while ((succ = node.next) == null ||
                           succ.status == CANCELLED) {
                        WNode q = null;    // find successor the slow way
                        for (WNode t = wtail; t != null && t != node; t = t.prev)
                            if (t.status != CANCELLED)
                                q = t;     // don't link if succ cancelled
                        if (succ == q ||   // ensure accurate successor
                            WNEXT.compareAndSet(node, succ, succ = q)) {
                            if (succ == null && node == wtail)
                                WTAIL.compareAndSet(this, node, pred);
                            break;
                        }
                    }
                    if (pred.next == node) // unsplice pred link
                        WNEXT.compareAndSet(pred, node, succ);
                    if (succ != null && (w = succ.thread) != null) {
                        // wake up succ to observe new pred
                        succ.thread = null;
                        LockSupport.unpark(w);
                    }
                    if (pred.status != CANCELLED || (pp = pred.prev) == null)
                        break;
                    node.prev = pp;        // repeat if new pred wrong/cancelled
                    WNEXT.compareAndSet(pp, pred, succ);
                    pred = pp;
                }
            }
        }
        WNode h; // Possibly release first waiter
        while ((h = whead) != null) {
            long s; WNode q; // similar to release() but check eligibility
            if ((q = h.next) == null || q.status == CANCELLED) {
                for (WNode t = wtail; t != null && t != h; t = t.prev)
                    if (t.status <= 0)
                        q = t;
            }
            if (h == whead) {
                if (q != null && h.status == 0 &&
                    ((s = state) & ABITS) != WBIT && // waiter is eligible
                    (s == 0L || q.mode == RMODE))
                    release(h);
                break;
            }
        }
        return (interrupted || Thread.interrupted()) ? INTERRUPTED : 0L;
    }

    // VarHandle mechanics
    private static final VarHandle STATE;
    private static final VarHandle WHEAD;
    private static final VarHandle WTAIL;
    private static final VarHandle WNEXT;
    private static final VarHandle WSTATUS;
    private static final VarHandle WCOWAIT;
    static {
        try {
            MethodHandles.Lookup l = MethodHandles.lookup();
            STATE = l.findVarHandle(StampedLock.class, "state", long.class);
            WHEAD = l.findVarHandle(StampedLock.class, "whead", WNode.class);
            WTAIL = l.findVarHandle(StampedLock.class, "wtail", WNode.class);
            WSTATUS = l.findVarHandle(WNode.class, "status", int.class);
            WNEXT = l.findVarHandle(WNode.class, "next", WNode.class);
            WCOWAIT = l.findVarHandle(WNode.class, "cowait", WNode.class);
        } catch (ReflectiveOperationException e) {
            throw new ExceptionInInitializerError(e);
        }
    }
}
