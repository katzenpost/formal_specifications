
typedef WaitGroup {
  chan doneSignal = [0] of {bit};
  int state
}

inline add_one(waitgroup) {
  d_step {
    waitgroup.state++
  }
}

inline done(waitgroup) {
  atomic {
    waitgroup.state--;
    if
      :: waitgroup.state == 0 ->
end:	 waitgroup.doneSignal!0
      :: else ->
	  skip
    fi
  }
}

inline wait(waitgroup) {
  waitgroup.doneSignal?0 -> skip
}
