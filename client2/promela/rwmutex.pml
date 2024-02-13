
typedef RWLock {
  chan writeComplete = [0] of {bit};
  chan allowWrite = [0] of {bit};
  int readers;
  bit writing;
  int writeWaiters;
  int readWaiters
}

/* RWLock actions */

inline acquire_read(lock) {
  do
    :: atomic {
      if
        :: lock.writing == 1 || lock.writeWaiters > 0 ->
	   lock.readWaiters++;
	   lock.writeComplete?0;
	   lock.readWaiters--;
	   break
        :: else ->
	   lock.readers++;
	   break
      fi
    }
  od
}

inline release_read(lock) {
    atomic {
      lock.readers--;
      lock.readers == 0 ->
end:   lock.writeComplete!0
    }
}

inline acquire_write(lock) {
  do
    :: atomic {
      if
	:: lock.writing == 0 && lock.readers == 0 ->
	   lock.writing = 1;
	   break;
	:: else ->
	   lock.writeWaiters++;
	   lock.allowWrite?0;
	   lock.writeWaiters--
      fi
    }
  od
}

inline release_write(lock) {
  atomic {
    assert(lock.writing == 1);
    lock.writing = 0
    if
    :: lock.writeWaiters > 0 ->
        lock.allowWrite!0
    :: else ->
        skip
    fi
    if
    :: lock.readWaiters > 0 ->
        lock.writeComplete!0;
    :: else ->
        skip
    fi
  }
}