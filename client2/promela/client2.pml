
#include "wait_group.pml"
#include "rwmutex.pml"

inline lock(x) {
	d_step { x == 0; x = 1 }
}

inline unlock(x) {
	d_step { assert x == 1; x = 0 }
}

#define N 10 /* max ARQ window size */

chan netIn = [0] of { bit };
chan netOut = [0] of { bit };


/* ARQ state */

chan arq_resend_chan = [2] of { int };
chan arq_send_chan = [2] of { int };
byte arq_surb_id_map[N];
RWLock arq_lock;
chan priority_queue = [N] of { int }


/* simulate the network */

proctype network_link() {
  bit readBuf
end: do
    :: netOut?readBuf ->
progress: netIn!readBuf
  od
}


/* connection type  */

proctype net_reader() {
  bit readBuf
end: do
    :: netIn?readBuf ->
progress: skip
  od
}

inline start_connection(netIn) {
  run net_reader(netIn)
}



/* ARQ */

inline start_arq() {
  run arq_worker()
}

proctype arq_worker() {
  ARQMessage message;
  do
    :: timeout ->
       priority_queue?message;
       do_resend(message)
    :: arq_send_chan?message -> do_send(message)
  od
}

inline do_resend(int message) {

}

inline do_send(int message) {

}

inline send_arq_message(int surb_id) {
  priority_queue!surb_id;
  arq_send_chan!surb_id
}



/* daemon */

inline start_daemon() {
  do
    :: printf("hi\n");
  od
}


/* startup */

init {

  run network_link();
  start_daemon();
  start_connection()
  
  
  /* send a message */
  do
    :: netOut!0
  od
end:
}
