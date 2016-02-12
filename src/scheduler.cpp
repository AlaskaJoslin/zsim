/** $glic$
 * Copyright (C) 2012-2015 by Massachusetts Institute of Technology
 * Copyright (C) 2010-2013 by The Board of Trustees of Stanford University
 * Copyright (C) 2011 Google Inc.
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

#include "scheduler.h"
#include <fstream>
#include <regex>
#include <sys/stat.h>
#include "config.h" // for ParseList
#include "pin.H"
#include "process_tree.h"
#include "profile_stats.h"
#include "str.h"
#include "virt/syscall_name.h"
#include "virt/time_conv.h"

//The scheduler class started simple, but at some point having it all in the header is too ridiculous. Migrate non perf-intensive calls here! (all but sync, really)

#define WATCHDOG_INTERVAL_USEC (50)
#define WATCHDOG_MAX_MULTIPLER (40) //50us-2ms waits
#define WATCHDOG_STALL_THRESHOLD (100)

//#define DEBUG_FL(args...) info(args)
#define DEBUG_FL(args...)

#define DEBUG_FUTEX(args...) info(args)
// #define DEBUG_FUTEX(args...)

// Unlike glibc's sleep functions suck, this ensures guaranteed minimum sleep time
static void TrueSleep(uint32_t usecs) {
    struct timespec req;
    struct timespec rem;

    req.tv_sec = usecs/1000000;
    req.tv_nsec = (usecs*1000) % 1000000000;

    while (req.tv_sec != 0 || req.tv_nsec != 0) {
        int res = syscall(SYS_nanosleep, &req, &rem); //we don't call glibc's nanosleep because errno is not thread-safe in pintools.
        if (res == 0) break;
        req = rem;
        if (res != -EINTR && res != 0) panic("nanosleep() returned an unexpected error code %d", res);
        //info("nanosleep() interrupted!");
    }
}

/* Hacky way to figure out if a thread is sleeping on a certain futex.
 *
 * Uses /proc/<pid>/task/<tid>/syscall, which is only set when the process is
 * actually sleeping on the syscall, not just in the kernel (see Linux kernel
 * docs). This interface has been available since ~2008.
 */
bool IsSleepingInFutex(uint32_t linuxPid, uint32_t linuxTid, uintptr_t futexAddr) {
    std::string fname = "/proc/" + Str(linuxPid) + "/task/" + Str(linuxTid) + "/syscall";
    std::ifstream fs(fname);
    if (!fs.is_open()) {
        warn("Could not open %s", fname.c_str());
        return false;
    }

    std::stringstream ss;
    ss << fs.rdbuf();
    fs.close();

    std::vector<std::string> argList = ParseList<std::string>(ss.str());
    bool match = argList.size() >= 2 &&
        strtoul(argList[0].c_str(), nullptr, 0) == SYS_futex &&
        (uintptr_t)strtoul(argList[1].c_str(), nullptr, 0) == futexAddr;
    //info("%s | %s | SYS_futex = %d futexAddr = 0x%lx | match = %d ", ss.str().c_str(), Str(argList).c_str(), SYS_futex, futexAddr, match);
    return match;
}


void Scheduler::watchdogThreadFunc() {
    info("Started scheduler watchdog thread");
    uint64_t lastPhase = 0;
    int multiplier = 1;
    uint64_t lastMs = 0;
    uint64_t fakeLeaveStalls = 0;
    while (true) {
        TrueSleep(multiplier*WATCHDOG_INTERVAL_USEC);

        if (zinfo->terminationConditionMet) {
            // Synchronize to avoid racing with EndOfPhaseActions code
            // (zinfo->terminationConditionMet is set on EndOfPhaseActions,
            // which has schedLock held, we must let it finish)
            futex_lock(&schedLock);
            info("Terminating scheduler watchdog thread");
            futex_unlock(&schedLock);
            SimEnd();
        }

        //Fastpath (unlocked, benign read races, only modifies local state)
        if (lastPhase != curPhase && pendingPidCleanups.size() == 0) {
            lastPhase = curPhase;
            fakeLeaveStalls = 0;
            if (multiplier < WATCHDOG_MAX_MULTIPLER) multiplier++;
            continue;
        }

        //if (lastPhase == curPhase && scheduledThreads == outQueue.size() && !sleepQueue.empty()) info("Mult %d curPhase %ld", multiplier, curPhase);

        futex_lock(&schedLock);

        if (lastPhase == curPhase && !fakeLeaves.empty() && (fakeLeaves.front()->th->futexJoin.action != FJA_WAKE)) {
            if (++fakeLeaveStalls >= WATCHDOG_STALL_THRESHOLD) {
                info("Detected possible stall due to fake leaves (%ld current)", fakeLeaves.size());
                // Uncomment to print all leaves
                FakeLeaveInfo* pfl = fakeLeaves.front();
                while (pfl) {
                    info(" [%d/%d] %s (%d) @ 0x%lx", getPid(pfl->th->gid), getTid(pfl->th->gid), GetSyscallName(pfl->syscallNumber), pfl->syscallNumber, pfl->pc);
                    pfl = pfl->next;
                }

                // Trigger a leave() on the first process, if the process's blacklist regex allows it
                FakeLeaveInfo* fl = fakeLeaves.front();
                ThreadInfo* th = fl->th;
                uint32_t pid = getPid(th->gid);
                uint32_t tid = getTid(th->gid);
                uint32_t cid = th->cid;

                const g_string& sbRegexStr = zinfo->procArray[pid]->getSyscallBlacklistRegex();
                std::regex sbRegex(sbRegexStr.c_str());
                if (std::regex_match(GetSyscallName(fl->syscallNumber), sbRegex)) {
                    // If this is the last leave we catch, it is the culprit for sure -> blacklist it
                    // Over time, this will blacklist every blocking syscall
                    // The root reason for being conservative though is that we don't have a sure-fire
                    // way to distinguish IO waits from truly blocking syscalls (TODO)
                    if (fakeLeaves.size() == 1) {
                        info("Blacklisting from future fake leaves: [%d] %s @ 0x%lx | arg0 0x%lx arg1 0x%lx", pid, GetSyscallName(fl->syscallNumber), fl->pc, fl->arg0, fl->arg1);
                        blockingSyscalls[pid].insert(fl->pc);
                    }

                    uint64_t pc = fl->pc;
                    do {
                        finishFakeLeave(th);

                        futex_unlock(&schedLock);
                        leave(pid, tid, cid);
                        futex_lock(&schedLock);

                        // also do real leave for other threads blocked at the same pc ...
                        fl = fakeLeaves.front();
                        if (fl == nullptr || getPid(th->gid) != pid || fl->pc != pc)
                            break;
                        th = fl->th;
                        tid = getTid(th->gid);
                        cid = th->cid;
                        // ... until a lower bound on queue size, in order to make blacklist work
                    } while (fakeLeaves.size() > 8);
                } else {
                    info("Skipping, [%d] %s @ 0x%lx | arg0 0x%lx arg1 0x%lx does not match blacklist regex (%s)",
                            pid, GetSyscallName(fl->syscallNumber), fl->pc, fl->arg0, fl->arg1, sbRegexStr.c_str());
                }
                fakeLeaveStalls = 0;
            }
        } else {
            fakeLeaveStalls = 0;
        }

        if (lastPhase == curPhase && scheduledThreads == outQueue.size() && !sleepQueue.empty()) {
            //info("Watchdog Thread: Sleep dep detected...")
            int64_t wakeupPhase = sleepQueue.front()->wakeupPhase;
            int64_t wakeupCycles = (wakeupPhase - curPhase)*zinfo->phaseLength;
            int64_t wakeupUsec = (wakeupCycles > 0)? wakeupCycles/zinfo->freqMHz : 0;

            //info("Additional usecs of sleep %ld", wakeupUsec);
            if (wakeupUsec > 10*1000*1000) warn("Watchdog sleeping for a long time due to long sleep, %ld secs", wakeupUsec/1000/1000);

            futex_unlock(&schedLock);
            TrueSleep(WATCHDOG_INTERVAL_USEC + wakeupUsec);
            futex_lock(&schedLock);

            if (lastPhase == curPhase && scheduledThreads == outQueue.size() && !sleepQueue.empty()) {
                ThreadInfo* sth = sleepQueue.front();
                uint64_t curMs = curPhase*zinfo->phaseLength/zinfo->freqMHz/1000;
                uint64_t endMs = sth->wakeupPhase*zinfo->phaseLength/zinfo->freqMHz/1000;
                (void)curMs; (void)endMs; //make gcc happy
                if (curMs > lastMs + 1000) {
                    info("Watchdog Thread: Driving time forward to avoid deadlock on sleep (%ld -> %ld ms)", curMs, endMs);
                    lastMs += 1000;
                }
                while (sth->state == SLEEPING) {
                    idlePhases.inc();
                    callback(); //sth will eventually get woken up

                    if (futex_haswaiters(&schedLock)) {
                        //happens commonly with multiple sleepers and very contended I/O...
                        //info("Sched: Threads waiting on advance, startPhase %ld curPhase %ld", lastPhase, curPhase);
                        break;
                    }

                    if (zinfo->terminationConditionMet) {
                        info("Termination condition met inside watchdog thread loop, exiting");
                        break;
                    }
                }
                idlePeriods.inc();
                multiplier = 0;
            }
        }

        if (multiplier < WATCHDOG_MAX_MULTIPLER) {
            multiplier++;
        }

        lastPhase = curPhase;

        //Lazily clean state of processes that terminated abruptly
        //NOTE: For now, we rely on the process explicitly telling us that it's going to terminate.
        //We could make this self-checking by periodically checking for liveness of the processes we're supposedly running.
        //The bigger problem is that if we get SIGKILL'd, we may not even leave a consistent zsim state behind.
        while (pendingPidCleanups.size()) {
            std::pair<uint32_t, uint32_t> p = pendingPidCleanups.back();
            uint32_t pid = p.first; //the procIdx pid
            uint32_t osPid = p.second;

            std::stringstream ss;
            ss << "/proc/" << osPid;
            struct stat dummy;
            if (stat(ss.str().c_str(), &dummy) == 0) {
                info("[watchdog] Deferring cleanup of pid %d (%d), not finished yet", pid, osPid);
                break;
            }

            pendingPidCleanups.pop_back(); //must happen while we have the lock

            futex_unlock(&schedLock);
            processCleanup(pid);
            futex_lock(&schedLock);
        }

        if (terminateWatchdogThread) {
            futex_unlock(&schedLock);
            break;
        } else {
            futex_unlock(&schedLock);
        }
    }
    info("Finished scheduler watchdog thread");
}

void Scheduler::threadTrampoline(void* arg) {
    Scheduler* sched = static_cast<Scheduler*>(arg);
    sched->watchdogThreadFunc();
}

void Scheduler::startWatchdogThread() {
    PIN_SpawnInternalThread(threadTrampoline, this, 64*1024, nullptr);
}


// Accurate join-leave implementation
void Scheduler::syscallLeave(uint32_t pid, uint32_t tid, uint32_t cid, uint64_t pc, int syscallNumber, uint64_t arg0, uint64_t arg1) {
    futex_lock(&schedLock);
    uint32_t gid = getGid(pid, tid);
    ThreadInfo* th = contexts[cid].curThread;
    assert(th->gid == gid);
    assert_msg(th->cid == cid, "%d != %d", th->cid, cid);
    assert(th->state == RUNNING);
    assert_msg(pid < blockingSyscalls.size(), "%d >= %ld?", pid, blockingSyscalls.size());

    bool blacklisted = blockingSyscalls[pid].find(pc) != blockingSyscalls[pid].end();
    if (blacklisted || th->markedForSleep) {
        DEBUG_FL("%s @ 0x%lx calling leave(), reason: %s", GetSyscallName(syscallNumber), pc, blacklisted? "blacklist" : "sleep");
        futex_unlock(&schedLock);
        leave(pid, tid, cid);
    } else {
        DEBUG_FL("%s @ 0x%lx skipping leave()", GetSyscallName(syscallNumber), pc);
        FakeLeaveInfo* si = new FakeLeaveInfo(pc, th, syscallNumber, arg0, arg1);
        fakeLeaves.push_back(si);
        // FIXME(dsm): zsim.cpp's SyscallEnter may be checking whether we are in a syscall and not calling us.
        // If that's the case, this would be stale, which may lead to some false positives/negatives
        futex_unlock(&schedLock);
    }
}

uint64_t Scheduler::getFutexWakePhase(bool realtime, FutexInfo fi, CONTEXT* ctxt, SYSCALL_STANDARD std) {
    int64_t waitNsec = 0;
    uint64_t wakeupPhase = 0;
    waitNsec = fi.timeout.tv_sec*1000000000L + fi.timeout.tv_nsec;
    if (fi.op & FUTEX_CLOCK_REALTIME || realtime) {
        uint32_t domain = zinfo->procArray[procIdx]->getClockDomain();
        uint64_t simNs = cyclesToNs(zinfo->globPhaseCycles);
        uint64_t offsetNs = simNs + zinfo->clockDomainInfo[domain].realtimeOffsetNs;
        warn(" REALTIME FUTEX: %ld %ld %ld %ld", waitNsec, simNs, offsetNs, waitNsec-offsetNs);
        waitNsec = (waitNsec > (int64_t)offsetNs)? (waitNsec - offsetNs) : 0;
    }
    if (waitNsec > 0) {
        struct timespec fakeTimeouts = (struct timespec){0}; //Never timeout.
        PIN_SetSyscallArgument(ctxt, std, 3, (ADDRINT)&fakeTimeouts);
        uint64_t waitCycles = waitNsec*zinfo->freqMHz/1000;
        uint64_t waitPhases = waitCycles/zinfo->phaseLength;
        wakeupPhase = zinfo->numPhases + waitPhases;
    }
    return wakeupPhase;
}

bool Scheduler::futexSynchronized(uint32_t pid, uint32_t tid, FutexInfo fi) {
    futex_lock(&schedLock);
    uint32_t gid = getGid(pid, tid);
    ThreadInfo* th = gidMap[gid];
    futex_unlock(&schedLock);
    while (true) {
        int futex_res = syscall(SYS_futex, th->futexWord, FUTEX_WAIT, 1 /*a racing thread waking us up will change value to 0, and we won't block*/, nullptr, nullptr, 0);
        if (futex_res == 0 || th->futexWord != 1) break;
    }
    join(pid, tid);
    return true;
}

bool Scheduler::futexWait(bool bitmask, bool pi_waiter, uint32_t pid, uint32_t tid, FutexInfo fi, CONTEXT* ctxt, SYSCALL_STANDARD std) {
    DEBUG_FUTEX("Scheduler: FUTEX WAIT called with bitmask %d pi %d pid %u tid %u", bitmask, pi_waiter, pid, tid);
    uint64_t wakeUpPhases = getFutexWakePhase(pi_waiter, fi, ctxt, std);  //pi versions all interpret as realtime
    futex_lock(&schedLock);
    uint32_t cid = gidMap[getGid(pid, tid)]->cid;
    futex_unlock(&schedLock);
    if(wakeUpPhases == 0) {
      wakeUpPhases = 0xffffffff;
    }
    FutexWaiter tempWaiter; tempWaiter.pid = pid; tempWaiter.tid = tid;   tempWaiter.pi_waiter = pi_waiter;
    tempWaiter.mask = 0xffffffff; tempWaiter.val = fi.val; tempWaiter.fi = fi; tempWaiter.allow_requeue = !pi_waiter;
    if(!pi_waiter) { //Normal cases
        if(fi.val != *fi.uaddr) {
            DEBUG_FUTEX("Cur val didn't match val in futex wait");
            return false;
        }
        DEBUG_FUTEX("WAIT took normal path");
        if(bitmask) {
            tempWaiter.mask = fi.val3;
        }
        futexTable[fi.uaddr].push_back(tempWaiter);
        markForSleep(pid, tid, wakeUpPhases);
        leave(pid, tid, cid);
    } else {    //if pi_waiter
        switch (fi.op & FUTEX_CMD_MASK) {
            case FUTEX_LOCK_PI:
                DEBUG_FUTEX("WAIT took lock path");
                if(futexTable[fi.uaddr].size() == 0) // Check that no one else is in line.
                {
                    DEBUG_FUTEX("FUTEX_LOCK_PI successfully locked");
                    futexTable[fi.uaddr].push_back(tempWaiter); //Notice we don't deschedule
                    return true;
                } else {
                  DEBUG_FUTEX("LOCK delayed");
                  if(bitmask) {
                      tempWaiter.mask = fi.val3;
                  }
                  futexTable[fi.uaddr].push_back(tempWaiter);
                  markForSleep(pid, tid, wakeUpPhases);
                  leave(pid, tid, cid);
                }
                break;
            case FUTEX_WAIT_REQUEUE_PI:
                DEBUG_FUTEX("WAIT took reque pi path");
                if(fi.val != *fi.uaddr) {
                    DEBUG_FUTEX("Cur val didn't match val in futex wait");
                    return false;
                }
                tempWaiter.allow_requeue = true;
                if(bitmask) {
                    tempWaiter.mask = fi.val3;
                }
                markForSleep(pid, tid, wakeUpPhases);
                leave(pid, tid, cid);
                futexTable[fi.uaddr].push_back(tempWaiter);
                break;
            case FUTEX_TRYLOCK_PI:
                DEBUG_FUTEX("WAIT took trylock path");
                if(futexTable[fi.uaddr].size() == 0) {
                    DEBUG_FUTEX("FUTEX_LOCK_PI successfully locked");
                    futexTable[fi.uaddr].push_back(tempWaiter); //Notice we don't deschedule
                    return true;
                } else {
                    return false;
                }
                break;
            default:
                panic("We missed something in futex wait.");
        }
    }
    return true;
}

int Scheduler::futexWake(bool bitmask, bool pi_wake, uint32_t pid, uint32_t tid, FutexInfo fi) {
    DEBUG_FUTEX("Scheduler: FUTEX WAKE called with bitmask %d pi %d pid %u tid %u", bitmask, pi_wake, pid, tid);
    int bitmaskValue = 0xffffffff;
    if(bitmask) {
        bitmaskValue = fi.val3;
    }
    int waitersToWake = futexWakeNWaiters(bitmaskValue, pi_wake, fi.uaddr, fi.val);
    return waitersToWake;
}

int Scheduler::futexUnlock(bool bitmask, bool pi_wake, uint32_t pid, uint32_t tid, FutexInfo fi) {
    DEBUG_FUTEX("Scheduler: FUTEX UNLOCK called with bitmask %d pi %d pid %u tid %u", bitmask, pi_wake, pid, tid);
    //We are responsible for removing the owner. Then we go back to wake.
    if(futexTable[fi.uaddr].size() > 0 && futexTable[fi.uaddr].front().pi_waiter
        && futexTable[fi.uaddr].front().tid == tid  && futexTable[fi.uaddr].front().pid == pid )
    {
        futexTable[fi.uaddr].pop_front(); //We were already awake
        assert(!isSleeping(pid, tid));
        return futexWake(bitmask, pi_wake, pid, tid, fi);
    }
    else {
      warn("something is screwy in unlock");
    }
    return 0;
}

int Scheduler::futexReque(uint32_t pid, uint32_t tid, FutexInfo fi) {
    DEBUG_FUTEX("Scheduler: FUTEX REQUE called with pid %u tid %u", pid, tid);
    bool extraWaiters = futexTable[fi.uaddr].size() > (uint32_t)fi.val;
    int waitersToWake = futexWakeNWaiters(0xffffffff, false, fi.uaddr, fi.val);
    int extraWaitersToWake = 0;
    if(extraWaiters) {
        extraWaitersToWake = futexMoveNWaiters(false, fi.uaddr, fi.uaddr2, fi.val2);
    }
    return waitersToWake + extraWaitersToWake;
}

int Scheduler::futexCmpReque(bool pi_wake, uint32_t pid, uint32_t tid, FutexInfo fi) {
    DEBUG_FUTEX("Scheduler: FUTEX CMP REQUE called with pi %d pid %u tid %u", pi_wake, pid, tid);
    int *curVal = 0;
    if(!safeCopy(fi.uaddr, curVal)) {
        panic("Futex Wait wasn't able to copy the data.");
    }
    if(fi.val3 != *curVal) {
        DEBUG_FUTEX("Cur val didn't match val in futex wait");
        return 0;
    }
    bool extraWaiters = futexTable[fi.uaddr].size() > (uint32_t)fi.val;
    int waitersToWake = 0;
    if(!pi_wake) {
        futexWakeNWaiters(pi_wake, 0xffffffff, fi.uaddr, fi.val);
    }
    int extraWaitersToWake = 0;
    if(extraWaiters) {
        extraWaitersToWake = futexMoveNWaiters(pi_wake, fi.uaddr, fi.uaddr2, fi.val2);
    }
    return waitersToWake + extraWaitersToWake;
}
//Must be called without lock. Returns # waiters.
int Scheduler::futexWakeNWaiters(int bitmask, bool p_waiter, int *uaddr, int val) {
  DEBUG_FUTEX("Scheduler: FUTEX WAKE N WAITERS called with bitmask %d pi %d uaddr %p val %d", bitmask, p_waiter, uaddr, val);
  futex_lock(&schedLock);
  int waitersToWake = 0;
  int waitersFailed = 0;
  bool piWakeInUserSpace = ((futexTable[uaddr].size() == 1) && futexTable[uaddr].front().pi_waiter);
  assert(!piWakeInUserSpace)
  if(p_waiter) {
      for(int i = 1; (uint32_t)i < futexTable[uaddr].size(); i++) {
          if(futexTable[uaddr][i].pi_waiter) {
            FutexWaiter tempWaiter = futexTable[uaddr][i];
            futexTable[uaddr].erase(futexTable[uaddr].begin() + waitersFailed);
            futexTable[uaddr].push_front(tempWaiter);
            DEBUG_FUTEX("we had a pi requestor jump to front of line");
            uint32_t gid = getGid(tempWaiter.pid, tempWaiter.tid);
            ThreadInfo* th = gidMap[gid];
            assert(th->state == SLEEPING);
            notifySleepEnd(tempWaiter.pid, tempWaiter.tid);
            wakeup(th, true);
            futex_unlock(&schedLock);
            return 1;
          }
      }
  }
  while((uint32_t)waitersToWake < futexTable[uaddr].size() && waitersToWake < val) {
      FutexWaiter tempWaiter = futexTable[uaddr][waitersFailed];
      if(bitmask && tempWaiter.mask & ~bitmask) {
          waitersFailed++;
      } else {
          waitersToWake++;
          futexTable[uaddr].erase(futexTable[uaddr].begin() + waitersFailed);
      }
      uint32_t gid = getGid(tempWaiter.pid, tempWaiter.tid);
      ThreadInfo* th = gidMap[gid];
      assert(th->state == SLEEPING);
      notifySleepEnd(tempWaiter.pid, tempWaiter.tid);
      DEBUG_FUTEX("WAKE N finished sleep end");
      wakeup(th, true);
      DEBUG_FUTEX("WAKE N finished wakeup");
  }
  DEBUG_FUTEX("WAKE N WAITERS Looped %d times", waitersFailed + waitersToWake);
  futex_unlock(&schedLock);
  return waitersToWake;
}

//Must be called with lock held. Will not release. Returns # waiters moved.
int Scheduler::futexMoveNWaiters(bool pi_wake, int *srcUaddr, int *targetUaddr, int val) {
  DEBUG_FUTEX("Scheduler: FUTEX MOVE N WAITERS called with pi %d src %p targ %p val %d", pi_wake, srcUaddr, targetUaddr, val);
  int waitersToMove = 0;
  int waitersFailed = 0;
  while((uint32_t)waitersToMove < futexTable[srcUaddr].size() && waitersToMove < val) {
      FutexWaiter tempWaiter = futexTable[srcUaddr][waitersFailed];
      if(pi_wake) {
        if(tempWaiter.pi_waiter) {
            waitersToMove++;
            futexTable[srcUaddr].erase(futexTable[srcUaddr].begin() + waitersFailed);
            futexTable[tempWaiter.fi.uaddr2].push_back(tempWaiter);
        } else {
            waitersFailed++;
        }
      } else {
        waitersToMove++;
        futexTable[srcUaddr].erase(futexTable[srcUaddr].begin() + waitersFailed);
        futexTable[targetUaddr].push_back(tempWaiter);
      }
  }
  return waitersToMove;
}

int Scheduler::futexWakeOp(uint32_t pid, uint32_t tid, FutexInfo fi) {
    DEBUG_FUTEX("Scheduler: FUTEX WAKE OP called with pid %u tid %u", pid, tid);
    int *oldVal = 0; //  int oldval = *(int *) uaddr2;
    if(!safeCopy(fi.uaddr2, oldVal)) {
        panic("Futex Wake Op wasn't able to copy the data.");
    }
    // |op |cmp|   oparg   |  cmparg   |
    //   4   4       12          12    <== # of bits
    int op = (fi.val3 & 0xf) >> 28;      // (((op & 0xf) << 28) |
    int cmp = (fi.val3 & 0xf) >> 24;     // ((cmp & 0xf) << 24) |
    int oparg = (fi.val3 & 0xfff) >> 12; // ((oparg & 0xfff) << 12) |
    int cmparg = (fi.val3 & 0xfff);      // (cmparg & 0xfff))
    // Bit-wise ORing the following value into op causes
    // (1 << oparg) to be used as the operand: FUTEX_OP_ARG_SHIFT  8
    if(op & 8) { oparg = 1 << oparg; }
    int *newVal; *newVal = 0; //  *(int *) uaddr2 = oldval op oparg;
    switch (op) { //Op is defined as:
      case 0: // FUTEX_OP_SET        0  /* uaddr2 = oparg; */
          *newVal = oparg;
      case 1: // FUTEX_OP_ADD        1  /* uaddr2 += oparg; */
          *newVal = *(fi.uaddr2) + oparg;
      case 2: // FUTEX_OP_OR         2  /* uaddr2 |= oparg; */
          *newVal = *(fi.uaddr2) | oparg;
      case 3: // FUTEX_OP_ANDN       3  /* uaddr2 &= ~oparg; */
          *newVal = *(fi.uaddr2) & ~oparg;
      case 4: // FUTEX_OP_XOR        4  /* uaddr2 ^= oparg; */
          *newVal = *(fi.uaddr2) ^ oparg;
      default:
          panic("We are missing an op type in sched wake op");
    }
    int waitersToWake = futexWakeNWaiters(false, 0xffffffff, fi.uaddr, fi.val);
    bool cmpResult = false;
    switch (cmp) { // The cmp field is one of the following:
      case 0: //   FUTEX_OP_CMP_EQ     0  /* if (oldval == cmparg) wake */
          cmpResult = (*oldVal == cmparg);
      case 1: //   FUTEX_OP_CMP_NE     1  /* if (oldval != cmparg) wake */
          cmpResult = (*oldVal != cmparg);
      case 2: //   FUTEX_OP_CMP_LT     2  /* if (oldval < cmparg) wake */
          cmpResult = (*oldVal < cmparg);
      case 3: //   FUTEX_OP_CMP_LE     3  /* if (oldval <= cmparg) wake */
          cmpResult = (*oldVal <= cmparg);
      case 4: //   FUTEX_OP_CMP_GT     4  /* if (oldval > cmparg) wake */
          cmpResult = (*oldVal > cmparg);
      case 5: //   FUTEX_OP_CMP_GE     5  /* if (oldval >= cmparg) wake */
          cmpResult = (*oldVal >= cmparg);
      default:
          panic("We are missing a case for cmp");
    }
    int extraWaitersToWake = 0;
    if(cmpResult) { //  if (oldval cmp cmparg)
      //    futex(uaddr2, FUTEX_WAKE, val2, 0, 0, 0);
      extraWaitersToWake = futexWakeNWaiters(false, 0xffffffff, newVal, fi.val2);
    }
    return waitersToWake + extraWaitersToWake;
}

void Scheduler::finishFakeLeave(ThreadInfo* th) {
    assert(th->fakeLeave);
    DEBUG_FL("%s (%d)  @ 0x%lx finishFakeLeave()", GetSyscallName(th->fakeLeave->syscallNumber), th->fakeLeave->syscallNumber, th->fakeLeave->pc);
    assert_msg(th->state == RUNNING, "gid 0x%x invalid state %d", th->gid, th->state);
    FakeLeaveInfo* si = th->fakeLeave;
    fakeLeaves.remove(si);
    delete si;
    assert(th->fakeLeave == nullptr);
}

void Scheduler::waitUntilQueued(ThreadInfo* th) {
    uint64_t startNs = getNs();
    uint32_t sleepUs = 1;
    while(!IsSleepingInFutex(th->linuxPid, th->linuxTid, (uintptr_t)&schedLock)) {
        TrueSleep(sleepUs++); // linear backoff, start small but avoid overwhelming the OS with short sleeps
        uint64_t curNs = getNs();
        if (curNs - startNs > (2L<<31L) /* ~2s */) {
            warn("waitUntilQueued for pid %d tid %d timed out", getPid(th->gid), getTid(th->gid));
            return;
        }
    }
}
