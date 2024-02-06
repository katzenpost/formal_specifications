---- MODULE client2 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ClientThreads, SenderThreads, MAX_CHANNEL_SIZE

VARIABLES channels, is_connected, client_mutex, client_thread_state, connection_thread_state, pc
vars == <<channels, is_connected, client_mutex, client_thread_state, connection_thread_state, pc>>

Init ==
    /\ is_connected = FALSE
    /\ client_mutex = 0
    /\ client_thread_state = [t \in ClientThreads |-> "Idle"]
    /\ connection_thread_state = [t \in SenderThreads |-> "Idle"]
    /\ channels = [chan \in {"sendChan", "receiveChan"} |-> <<>>]
    /\ pc = [t \in {"wire_receiver"} |-> "Idle"]


(* reusable primitives *)

ChannelSend(channelName, message) ==
    /\ Len(channels[channelName]) < MAX_CHANNEL_SIZE
    /\ channels' = [channels EXCEPT ![channelName] = Append(@, message)]

ChannelReceive(channelName) ==
    /\ Len(channels[channelName]) > 0
    /\ Len(channels[channelName]) < MAX_CHANNEL_SIZE
    /\ channels' = [channels EXCEPT ![channelName] = Tail(channels[channelName])]

AcquireMutex(t) ==
    /\ client_mutex = 0
    /\ client_mutex' = t

ReleaseMutex(t) ==
    /\ client_mutex = t
    /\ client_mutex' = 0

(* client main *)

DialStart(t) ==
    /\ client_thread_state[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = FALSE
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Dialing"]
    /\ UNCHANGED <<channels, is_connected, connection_thread_state, pc>>

DialFinish(t) ==
    /\ client_thread_state[t] = "Dialing"
    /\ is_connected = FALSE
    /\ is_connected' = TRUE
    /\ ReleaseMutex(t)
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels, connection_thread_state, pc>>

HangupStart(t) ==
    /\ client_thread_state[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = TRUE
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "HangingUp"]
    /\ UNCHANGED <<channels, is_connected, connection_thread_state, pc>>

HangupFinish(t) ==
    /\ client_thread_state[t] = "HangingUp"
    /\ is_connected = TRUE
    /\ is_connected' = FALSE
    /\ ReleaseMutex(t)
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels, connection_thread_state, pc>>

SendMessageStart(t) ==
    /\ client_thread_state[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = TRUE
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "SendingMessage"]
    /\ UNCHANGED <<channels, is_connected, connection_thread_state, pc>>

SendMessageFinish(t) ==
    /\ client_thread_state[t] = "SendingMessage"
    /\ ReleaseMutex(t)
    /\ ChannelSend("sendChan", "message")
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<connection_thread_state, is_connected, pc>>

(* connection *)

SenderReceiveStart(t) ==
    /\ Len(channels["sendChan"]) > 0
    /\ connection_thread_state[t] = "Idle"
    /\ connection_thread_state' = [connection_thread_state EXCEPT ![t] = "ProcessingMessage"]
    /\ ChannelReceive("sendChan")
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, pc>>

SenderReceiveFinish(t) ==
    /\ connection_thread_state[t] = "ProcessingMessage"
    /\ connection_thread_state' = [connection_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, channels, pc>>

ReceiveCommand(t) ==
    /\ connection_thread_state[t] = "Idle"
    /\ Len(channels["receiveChan"]) > 0
    /\ connection_thread_state' = [connection_thread_state EXCEPT ![t] = "ProcessingCommand"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, pc, channels>>

ProcessingCommand(t) ==
    /\ connection_thread_state[t] = "ProcessingCommand"
    /\ ChannelReceive("receiveChan")
    /\ connection_thread_state' = [connection_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, pc>>

(* wire receiver *)

WireReceiverSend(t, s) ==
    /\ pc[t] = "Idle"
    /\ connection_thread_state[s] = "ProcessingCommand"
    /\ pc' = [pc EXCEPT ![t] = "SentToConnection"]
    /\ UNCHANGED <<is_connected, client_thread_state, channels, client_mutex, connection_thread_state>>

WireReceiverReset(t) ==
    /\ pc[t] = "SentToConnection"
    /\ ChannelSend("receiveChan", "message")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, connection_thread_state>>

Next ==
    \/ \E t \in ClientThreads: (DialStart(t) \/ DialFinish(t))
    \/ \E t \in ClientThreads: (HangupStart(t) \/ HangupFinish(t))
    \/ \E t \in ClientThreads: (SendMessageStart(t) \/ SendMessageFinish(t))
    \/ \E s \in SenderThreads: (SenderReceiveStart(s) \/ SenderReceiveFinish(s))
    \/ \E s \in SenderThreads: (ReceiveCommand(s) \/ ProcessingCommand(s))
    \/ WireReceiverReset("wire_receiver")
    \/ \E s \in SenderThreads: WireReceiverSend("wire_receiver", s)

WireReceiverInteraction ==
    \E t \in SenderThreads: 
        WireReceiverSend("wire_receiver", t) \/ WireReceiverReset("wire_receiver")

Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(WireReceiverInteraction)
    /\ WF_vars(\A t \in SenderThreads: ReceiveCommand(t))


====
