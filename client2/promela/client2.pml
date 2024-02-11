
#define N 3 /* max ARQ window size */

typedef ARQMessage {
  int SURBID = 0;
}

typedef RWLock {
    chan writeComplete = [0] of {bit}; // Channel for signaling writing completion to readers
    int readers;                       // Counter for active readers
    bit writing;                       // Flag indicating if writing is in progress
}

/* ARQ state */

chan arq_resend_chan = [2] of { ARQMessage };
chan arq_send_chan = [2] of { ARQMessage };
byte arq_surb_id_map[N];
RWLock arq_lock;





/* simulate the network */

proctype network_link(chan netIn, netOut) {
  bit readBuf
end: do
    :: netOut?readBuf ->
progress: netIn!readBuf
  od
}


/* connection type  */

proctype net_reader(chan netIn) {
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
    :: arq_resend_chan?message -> do_resend(message)
    :: arq_send_chan?message -> do_send(message)
  od
}

inline do_resend(ARQMessage message) {
}

inline do_send(ARQMessage message) {
}

inline send_arq_message(int surb_id) {
  acquire_write(arq_lock);
  
  assert(arq_surb_id_map[surb_id] == 0);
  arq_surb_id_map[surb_id] = 1;

  release_write(arq_lock);

  ARQMessage message;
  message.SURBID = surb_id;
  sendCh!message
}



/* daemon */

inline start_daemon() {
  do
    :: printf("hi\n");
  od
}


/* startup */

init {
  chan netIn = [0] of { bit };
  chan netOut = [0] of { bit };

  run network_link(netIn, netOut);


  start_daemon();
  start_connection(netIn)
  
  
  /* send a message */
  do
    :: netOut!0
  od
end:
}
