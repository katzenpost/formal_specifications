---- MODULE client2 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ClientThreads, SenderThreads, MAX_CHANNEL_SIZE

VARIABLES channels, is_connected, client_mutex, client_thread_state, sender_thread_state, wire_receiver_state
vars == <<channels, is_connected, client_mutex, client_thread_state, sender_thread_state, wire_receiver_state>>

Init ==
    /\ is_connected = FALSE
    /\ client_mutex = 0
    /\ client_thread_state = [t \in ClientThreads |-> "Idle"]
    /\ sender_thread_state = [t \in SenderThreads |-> "Idle"]
    /\ wire_receiver_state = "Idle"
    /\ channels = [chan \in {"sendChan", "getConsensusChan", "receiveChan"} |-> <<>>]


(* various reusable primitive actions *)

ChannelSend(channelName, message) ==
    /\ Len(channels[channelName]) < MAX_CHANNEL_SIZE
    /\ channels' = [channels EXCEPT ![channelName] = Append(@, message)]

ChannelReceive(channelName) ==
    /\ Len(channels[channelName]) > 0
    /\ channels' = [channels EXCEPT ![channelName] = Tail(channels[channelName])]

AcquireMutex(t) ==
    /\ client_mutex = 0
    /\ client_mutex' = t

ReleaseMutex(t) ==
    /\ client_mutex = t
    /\ client_mutex' = 0

(* client actions *)

DialStart(t) ==
    /\ client_thread_state[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = FALSE
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Dialing"]
    /\ UNCHANGED <<channels, is_connected, sender_thread_state, wire_receiver_state>>

DialFinish(t) ==
    /\ client_thread_state[t] = "Dialing"
    /\ is_connected = FALSE
    /\ is_connected' = TRUE
    /\ ReleaseMutex(t)
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels, sender_thread_state, wire_receiver_state>>

HangupStart(t) ==
    /\ client_thread_state[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = TRUE
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "HangingUp"]
    /\ UNCHANGED <<channels, is_connected, sender_thread_state, wire_receiver_state>>

HangupFinish(t) ==
    /\ client_thread_state[t] = "HangingUp"
    /\ is_connected = TRUE
    /\ is_connected' = FALSE
    /\ ReleaseMutex(t)
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels, sender_thread_state, wire_receiver_state>>

SendMessageStart(t) ==
    /\ client_thread_state[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = TRUE
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "SendingMessage"]
    /\ UNCHANGED <<channels, is_connected, sender_thread_state, wire_receiver_state>>

SendMessageFinish(t) ==
    /\ client_thread_state[t] = "SendingMessage"
    /\ ReleaseMutex(t)
    /\ ChannelSend("sendChan", "message")
    /\ client_thread_state' = [client_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<sender_thread_state, is_connected, wire_receiver_state>>

(* connection actions *)

SenderReceiveStart(t) ==
    /\ Len(channels["sendChan"]) > 0
    /\ sender_thread_state[t] = "Idle"
    /\ sender_thread_state' = [sender_thread_state EXCEPT ![t] = "ProcessingMessage"]
    /\ ChannelReceive("sendChan")
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, wire_receiver_state>>

SenderReceiveFinish(t) ==
    /\ sender_thread_state[t] = "ProcessingMessage"
    /\ sender_thread_state' = [sender_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, channels, wire_receiver_state>>

ReceivedGetConsensus(t) ==
    /\ sender_thread_state[t] = "Idle"
    /\ sender_thread_state' = [sender_thread_state EXCEPT ![t] = "ProcessingGetConsensus"]
    /\ ChannelReceive("getConsensusChan")
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, wire_receiver_state>>

ReceivedGetConsensusFinish(t) ==
    /\ sender_thread_state[t] = "ProcessingGetConsensus"
    /\ sender_thread_state' = [sender_thread_state EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, channels, wire_receiver_state>>

ReceiveCommand(t) ==
    /\ sender_thread_state[t] = "Idle"
    /\ ChannelReceive("receiveChan")
    /\ sender_thread_state' = [sender_thread_state EXCEPT ![t] = "ProcessingCommand"]
    /\ UNCHANGED <<is_connected, client_thread_state, client_mutex, wire_receiver_state>>

WireReceiverSend ==
    /\ wire_receiver_state = "Idle"
    /\ ChannelSend("receiveChan", "message")
    /\ wire_receiver_state' = "SentToConnection"
    /\ UNCHANGED <<is_connected, client_thread_state, sender_thread_state, client_mutex>>

WireReceiverReset ==
    /\ wire_receiver_state = "SentToConnection"
    /\ wire_receiver_state' = "Idle"
    /\ UNCHANGED <<channels, is_connected, client_thread_state, sender_thread_state, client_mutex>>

Next ==
    \/ \E t \in ClientThreads: (DialStart(t) \/ DialFinish(t))
    \/ \E t \in ClientThreads: (HangupStart(t) \/ HangupFinish(t))
    \/ \E t \in ClientThreads: (SendMessageStart(t) \/ SendMessageFinish(t))
    \/ \E s \in SenderThreads: (SenderReceiveStart(s) \/ SenderReceiveFinish(s))
    \/ \E s \in SenderThreads: (ReceivedGetConsensus(s) \/ ReceivedGetConsensusFinish(s))
    \/ \E s \in SenderThreads: WireReceiverReset \/ WireReceiverSend

Spec ==
    Init /\ [][Next]_vars

====
