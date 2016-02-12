/** $lic$
 * Copyright (C) 2012-2015 by Massachusetts Institute of Technology
 * Copyright (C) 2010-2013 by The Board of Trustees of Stanford University
 *
 * This file is part of zsim.
 *
 * zsim is free software; you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, version 2.
 *
 * If you use this software in your research, we request that you reference
 * the zsim paper ("ZSim: Fast and Accurate Microarchitectural Simulation of
 * Thousand-Core Systems", Sanchez and Kozyrakis, ISCA-40, June 2013) as the
 * source of the simulator in any publications that use this software, and that
 * you send us a citation of your work.
 *
 * zsim is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program. If not, see <http://www.gnu.org/licenses/>.
 */

#include <syscall.h>
#include "constants.h"
#include "log.h"
#include "scheduler.h"
#include "process_tree.h"
#include "virt/common.h"
#include "virt/syscall_name.h"
#include "virt/time_conv.h"
#include "zsim.h"

static bool inFakeTimeoutMode[MAX_THREADS];

struct TimeoutRetVals {
    int retValue;
    Scheduler::FutexInfo fi;
    bool switchToJoin;
    bool prePatchMode;
};
static struct TimeoutRetVals threadBlockingInfo[MAX_THREADS] = {0, {0}, false, false};

static bool SkipTimeoutVirt(PrePatchArgs args) {
    // having both conditions ensures that we don't virtualize in the interim of toggling ff ON
    return args.isNopThread || zinfo->procArray[procIdx]->isInFastForward();
}

static int getTimeoutArg(int syscallNum) {
    if (syscallNum == SYS_poll) return 2;
    return 3;  // futex, epoll_wait, epoll_pwait
}

//int futex(int *uaddr, int futex_op, int val,
//          const struct timespec *timeout,   /* or: uint32_t val2 */
//          int *uaddr2, int val3);
static Scheduler::FutexInfo getFilledInFutex(uint32_t tid, CONTEXT* ctxt, SYSCALL_STANDARD std) {
    Scheduler::FutexInfo fi;
    fi.uaddr = (int*) PIN_GetSyscallArgument(ctxt, std, 0);
    fi.op = (int) PIN_GetSyscallArgument(ctxt, std, 1);
    fi.val = (int) PIN_GetSyscallArgument(ctxt, std, 2);
    fi.uaddr2 = (int*) PIN_GetSyscallArgument(ctxt, std, 4);
    fi.val3 = (uint32_t) PIN_GetSyscallArgument(ctxt, std, 5);
    switch (fi.op & FUTEX_CMD_MASK) {
        case FUTEX_REQUEUE:
            info("FUTEX_REQUE");
            break;
        case FUTEX_CMP_REQUEUE:
            info("FUTEX_CMP_REQUEUE");
            break;
        case FUTEX_CMP_REQUEUE_PI:
            info("FUTEX_CMP_REQUEUE_PI");
            break;
        case FUTEX_WAKE_BITSET:
            info("FUTEX_WAKE_BITSET");
            break;
        case FUTEX_WAKE:
            info("FUTEX_WAKE");
            break;
        case FUTEX_WAKE_OP:
            info("FUTEX_WAKE_OP");
            break;
        case FUTEX_WAIT:
            info("FUTEX_WAIT");
            break;
        case FUTEX_WAIT_BITSET:
            info("FUTEX_WAIT_BITSET");
            break;
        case FUTEX_LOCK_PI:
            info("FUTEX_LOCK_PI");
            break;
        case FUTEX_WAIT_REQUEUE_PI:
            info("FUTEX_WAIT_REQUEUE_PI");
            break;
    }
    switch (fi.op & FUTEX_CMD_MASK) {
        case FUTEX_REQUEUE:
        case FUTEX_CMP_REQUEUE:
        case FUTEX_CMP_REQUEUE_PI:
        case FUTEX_WAKE_BITSET:
        case FUTEX_WAKE:
        case FUTEX_WAKE_OP:
            fi.val2 = (uint32_t) PIN_GetSyscallArgument(ctxt, std, 3);
            fi.timeout = {0,0};
            break;
        case FUTEX_WAIT:
        case FUTEX_WAIT_BITSET:
        case FUTEX_LOCK_PI:
        case FUTEX_WAIT_REQUEUE_PI:
            fi.val2 = 0;
            const struct timespec* timeout = (const struct timespec*) PIN_GetSyscallArgument(ctxt, std, 3);
            if(timeout) {
              fi.timeout = *timeout;
            }
            break;
    }
    info("val2: %u", fi.val2);
    info("timeout: %li %li", fi.timeout.tv_sec, fi.timeout.tv_nsec);
    return fi;
}

//This has now been refactored so that it is only called for non futex syscallNums.
// Per-syscallNum manipulation. This code either succeeds, fakes timeout value and sets waitNsec, or returns false
static bool PrePatchTimeoutSyscall(uint32_t tid, CONTEXT* ctxt, SYSCALL_STANDARD std, int syscallNum) {
    warn("We took a non futex path in timeout");
    int64_t waitNsec = 0;
    int timeoutArg = getTimeoutArg(syscallNum);
    int timeout = (int) PIN_GetSyscallArgument(ctxt, std, timeoutArg);
    if (timeout <= 0)
    {  return false; }
    PIN_SetSyscallArgument(ctxt, std, timeoutArg, 20); // 20ms timeout
    waitNsec = ((uint64_t)timeout)*1000*1000;  // timeout is in ms
    uint64_t waitCycles = waitNsec*zinfo->freqMHz/1000;
    uint64_t waitPhases = waitCycles/zinfo->phaseLength;
    if (waitPhases < 2) { waitPhases = 2; }
    uint64_t wakeupPhase = zinfo->numPhases + waitPhases;
    zinfo->sched->markForSleep(procIdx, tid, wakeupPhase);
    inFakeTimeoutMode[tid] = true;
    return true;
}

//This function generically figures out what kind of InstrFuncPtrs we should use.
static bool PostPatchTimeoutSyscall(uint32_t tid, CONTEXT* ctxt, SYSCALL_STANDARD std, int syscallNum, ADDRINT prevIp, ADDRINT timeoutArgVal) {
    warn("We took a non futex path in timeout");
    assert(inFakeTimeoutMode[tid]);
    int res = (int)PIN_GetSyscallNumber(ctxt, std);
    bool timedOut = (res == 0);
    bool isSleeping = zinfo->sched->isSleeping(procIdx, tid);
    bool retrySyscall;
    if (!timedOut) {
        if (isSleeping) {
           zinfo->sched->notifySleepEnd(procIdx, tid);
        }
        retrySyscall = false;
    } else {
        retrySyscall = isSleeping;
    }
    if (retrySyscall && zinfo->procArray[procIdx]->isInFastForward()) {
        warn("[%d] Fast-forwarding started, not retrying timeout syscallNum (%s)", tid, GetSyscallName(syscallNum));
        retrySyscall = false;
        assert(isSleeping);
        zinfo->sched->notifySleepEnd(procIdx, tid);
    }
    if (retrySyscall) {
        ADDRINT curIp = PIN_GetContextReg(ctxt, REG_INST_PTR);
        info("[%d] post-patch, retrying, IP: 0x%lx -> 0x%lx", tid, curIp, prevIp);
        PIN_SetContextReg(ctxt, REG_INST_PTR, prevIp);
        PIN_SetSyscallNumber(ctxt, std, syscallNum);
    } else {
        PIN_SetSyscallArgument(ctxt, std, getTimeoutArg(syscallNum), timeoutArgVal);
        inFakeTimeoutMode[tid] = false;
    }
    info("[%d] post-patch %s (%d), timedOut %d, sleeping (orig) %d, retrying %d, orig res %d, patched res %d", tid, GetSyscallName(syscallNum), syscallNum, timedOut, isSleeping, retrySyscall, res, (int)PIN_GetSyscallNumber(ctxt, std));
    return retrySyscall;
}

PostPatchFn PatchTimeoutSyscall(PrePatchArgs args) {
    if (SkipTimeoutVirt(args)) {
        return NullPostPatch;  //We reach this path if we aren't simulating threads or are fast-forwarding
    }
    int syscallNum = PIN_GetSyscallNumber(args.ctxt, args.std);
    Scheduler::FutexInfo fi;
    ADDRINT prevIp = PIN_GetContextReg(args.ctxt, REG_INST_PTR);
    ADDRINT timeoutArgVal = PIN_GetSyscallArgument(args.ctxt, args.std, getTimeoutArg(syscallNum));
    assert_msg(syscallNum == SYS_futex || syscallNum == SYS_epoll_wait || syscallNum == SYS_epoll_pwait || syscallNum == SYS_poll,
      "Invalid timeout syscallNum %d", syscallNum);
    threadBlockingInfo[args.tid].prePatchMode = !threadBlockingInfo[args.tid].prePatchMode; //Toggle
    if(threadBlockingInfo[args.tid].prePatchMode) {
      if (syscallNum == SYS_futex) {
        // zinfo->usingFutex[args.tid] = true;
        info("Pre Patch Futex tid %u", args.tid);
        fi = getFilledInFutex(args.tid, args.ctxt, args.std);
        switch (fi.op & FUTEX_CMD_MASK) {
            case FUTEX_WAIT:
                //  If uaddr contains val then sleeps waiting for FUTEX_WAKE.
                //  Ordered. If val does not match uaddr then fails with EAGAIN.
                //  If timeout is null, block indefinitely. Else wait according
                //  to CLOCK_MONOTONIC. Round up if necessary.
                if(!zinfo->sched->futexWait(false, false, procIdx, args.tid, fi, args.ctxt, args.std)) {
                  fi.retValue = EAGAIN;
                } else {
                  fi.retValue = 0;
                }
                break;
            case FUTEX_WAIT_BITSET:
                //  Like FUTEX_WAIT except val3 specifies a bit wise & mask for the
                //  waiters. Bitwise and Also can use FUTEX_CLOCK_REALTIME.
                if(!zinfo->sched->futexWait(true, false, procIdx, args.tid, fi, args.ctxt, args.std)) {
                    fi.retValue = EAGAIN;
                } else {
                    fi.retValue = 0;
                }
                break;
            case FUTEX_TRYLOCK_PI:
            case FUTEX_LOCK_PI:
            case FUTEX_WAIT_REQUEUE_PI:
                if(!zinfo->sched->futexWait(false, true, procIdx, args.tid, fi, args.ctxt, args.std)) {
                    fi.retValue = EAGAIN;
                } else {
                    fi.retValue = 0;
                }
                break;
        }
        info("Finished futex syscall with return value: %i", fi.retValue);
        threadBlockingInfo[args.tid].retValue = fi.retValue;
        threadBlockingInfo[args.tid].fi = fi;
      } else {
        PrePatchTimeoutSyscall(args.tid, args.ctxt, args.std, syscallNum); //TODO this has a return value
      }
      return NullPostPatch;
    } else {
      if (syscallNum == SYS_futex) {
          switch (threadBlockingInfo[args.tid].fi.op & FUTEX_CMD_MASK) {
              case FUTEX_WAIT:
              case FUTEX_WAIT_BITSET:
              case FUTEX_LOCK_PI:
              case FUTEX_WAIT_REQUEUE_PI:
                  if(PIN_GetSyscallReturn(args.ctxt, args.std) == 0) {  //We suceeded
                      info("Thread tid %d saw a matching actual wake", args.tid);
                      zinfo->sched->futexSynchronized(procIdx, args.tid, threadBlockingInfo[args.tid].fi);
                      info("Wait finished futex synch");
                  } else {
                      info("Thread tid %d failed", args.tid);
                  }
                  break;
              case FUTEX_WAKE:
                //  Wakes at most val of waiters on uaddr. No guarantee on priority.
                // Returns the number of waiters that were woken up.
                fi.retValue = zinfo->sched->futexWake(false, false, procIdx, args.tid, fi);
                break;
              case FUTEX_FD: //  definitely panic. This operation hasn't been supported since Linux 2.6.something
                panic("We don't support FUTEX_FD.");
              case FUTEX_REQUEUE: //  Same as FUTEX_CMP_REQUEUE without the comparison.
                fi.retValue = zinfo->sched->futexReque(procIdx, args.tid, fi);
                break;
              case FUTEX_CMP_REQUEUE:
                //  Checks that uaddr still contains val3. If not return EAGAIN.
                //  Otherwise wake up at most val waiters. If waiters > val, then
                //  at most val2 of the remaining waiters are removed from
                //  uaddr's queue and placed in uaddr2's queue.
                fi.retValue = zinfo->sched->futexCmpReque(false, procIdx, args.tid, fi);
                break;
              case FUTEX_WAKE_OP:
                zinfo->sched->futexWakeOp(procIdx, args.tid, fi);
                break;
              case FUTEX_WAKE_BITSET:
                //  Like FUTEX_WAKE except val3 is used as a bitwise & of the values
                //  stored from FUTEX_WAIT_BITSET. Normal WAIT and WAKE functions have
                //  bit masks of all 1s.
                fi.retValue = zinfo->sched->futexWake(true, false, procIdx, args.tid, fi);
                break;
              case FUTEX_UNLOCK_PI:
                // This operation wakes the top priority waiter that is waiting
                // in FUTEX_LOCK_PI on the futex address provided by the uaddr argument.
                fi.retValue = zinfo->sched->futexUnlock(false, true, procIdx, args.tid, fi);
                break;
              case FUTEX_CMP_REQUEUE_PI:
                // This operation is a PI-aware variant of FUTEX_CMP_REQUEUE.
                fi.retValue = zinfo->sched->futexCmpReque(true, procIdx, args.tid, fi);
                break;
              default:
                panic("We are missing a case for futex.");
          }
          return NullPostPatch;
      }
      else if(PostPatchTimeoutSyscall(args.tid, args.ctxt, args.std, syscallNum, prevIp, timeoutArgVal))
      {
        return [syscallNum, prevIp, fi](PostPatchArgs args) {
          return PPA_USE_RETRY_PTRS; //TODO check correctness.
        };
      }
      else
      {
        return [syscallNum, prevIp, fi](PostPatchArgs args) {
          return PPA_USE_JOIN_PTRS;
        };
      }
    }
    return NullPostPatch;
}
