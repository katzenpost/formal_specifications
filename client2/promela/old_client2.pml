
#include "wait_group.pml"
#include "rwmutex.pml"

inline lock(x) {
	d_step { x == 0; x = 1 }
}

inline unlock(x) {
	d_step { assert x == 1; x = 0 }
}

#define N 10 /* max ARQ window size */

/* network link state */
chan netIn = [0] of { bit };
chan netOut = [0] of { bit };

/* daemon state */
chan daemon_reply_ch = [0] of { bit };

/* listener state */
chan listener_ingress_ch = [0] of { bit };
chan listener_update_pki_doc_ch = [0] of { bit };
chan listener_update_status_ch = [0] of { bit };
chan listener_conn_ch = [0] of { bit };
bit listener_conn_status;

/* incoming conn state */
incoming_socket_ch = [0] of { bit };
incoming_request_ch = [0] of { bit };
incoming_send_to_client_ch = [0] of { bit };

/* connection state */
chan connection_cmd_ch = [0] of { bit };
chan connection_get_consensus_ch = [1] of { bit };
bool connection_is_connected;
RWLock connection_is_connected_lock;

typedef getConsensusCtx {
        chan reply_ch = [0] of { bit };
        int epoch;
        chan is_err_ch = [0] of { bool };
};

chan get_consensus_ch = [1] of { getConsensusCtx };


/* network link */

proctype network_link_out() {
  bit readBuf
end: do
    :: netOut?readBuf
  od
}

proctype network_link_in() {
  bit readBuf
end: do
    :: netIn!readBuf
  od
}




/* connection */

proctype net_reader() {
  bit readBuf
end: do
    :: netIn?readBuf ->
progress: connection_cmd_ch!readBuf
  od
}

proctype connection_worker() {
  bit reply;
  bit message
  do
    :: connection_cmd_ch?reply ->
       daemon_reply_ch!reply
    :: send_ch?message -> 
       
  od
}


/* listener */

proctype listener_worker() {
  bit newConn;
  bit status;
  listener_conn_ch?newConn -> /* modeling behavior of func (l *listener) onNewConn(conn *net.UnixConn) */
    lock(listener_conn_status_lock);
    status = listener_conn_status;
    unlock(listener_conn_status_lock);
    incoming_send_to_client_ch!status;
    /* XXX FIXME ... wait for current pki doc etc. */
}

/* incoming conn */

proctype incoming_receive_worker() {
/* simulate receiving from the client socket */
  bit request;
  do
    :: incoming_socket_ch?request ->
        incoming_request_ch!request
  od
}

proctype incoming_response_worker() {
  bit response;
  do
    :: incoming_send_to_client_ch?response ->
        incoming_socket_ch!response
  od
}

proctype incoming_worker() {
  run incoming_receive_worker();
  run incoming_response_worker();

  bit request;
  do
    :: incoming_request_ch?request ->
          skip; /* TODO FIXME send to listener ingress channel */
  od
}


/* daemon */

proctype daemon_ingress_worker() {
  bit reply;
  do
    :: daemon_reply_ch?reply ->
    /* TODO: send reply to listener, here... */
  od
}


