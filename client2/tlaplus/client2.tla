---- MODULE client2 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MAX_CHANNEL_SIZE

VARIABLES channels, is_connected, client_mutex, pc
vars == <<channels, is_connected, client_mutex, pc>>

Init ==
    /\ is_connected = FALSE
    /\ client_mutex = 0
    /\ channels = [chan \in {"sendChan", "receiveChan"} |-> <<>>]
    /\ pc = [t \in {"wire_receiver", "connection", "client"} |-> "Idle"]


(* reusable actions *)

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
    /\ pc[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = FALSE
    /\ pc' = [pc EXCEPT ![t] = "Dialing"]
    /\ UNCHANGED <<channels, is_connected>>

DialFinish(t) ==
    /\ pc[t] = "Dialing"
    /\ is_connected = FALSE
    /\ is_connected' = TRUE
    /\ ReleaseMutex(t)
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels>>

HangupStart(t) ==
    /\ pc[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = TRUE
    /\ pc' = [pc EXCEPT ![t] = "HangingUp"]
    /\ UNCHANGED <<channels, is_connected>>

HangupFinish(t) ==
    /\ pc[t] = "HangingUp"
    /\ is_connected = TRUE
    /\ is_connected' = FALSE
    /\ ReleaseMutex(t)
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels>>

SendMessageStart(t) ==
    /\ pc[t] = "Idle"
    /\ AcquireMutex(t)
    /\ is_connected = TRUE
    /\ pc' = [pc EXCEPT ![t] = "SendingMessage"]
    /\ UNCHANGED <<channels, is_connected>>

SendMessageFinish(t, s) ==
    /\ pc[t] = "SendingMessage"
    /\ pc[s] = "Idle"
    /\ ReleaseMutex(t)
    /\ ChannelSend("sendChan", "message")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected>>

(* connection *)

SenderReceiveStart(t, s) ==
    /\ Len(channels["sendChan"]) > 0
    /\ pc[t] = "Idle"
    /\ pc[s] = "SendingMessage"
    /\ pc' = [pc EXCEPT ![t] = "ProcessingMessage"]
    /\ ChannelReceive("sendChan")
    /\ UNCHANGED <<is_connected, client_mutex>>

SenderReceiveFinish(t) ==
    /\ pc[t] = "ProcessingMessage"
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_mutex, channels>>

ReceiveCommand(t, s) ==
    /\ pc[t] = "Idle"
    /\ pc[s] = "Idle"
    /\ Len(channels["receiveChan"]) > 0
    /\ pc' = [pc EXCEPT ![t] = "ProcessingCommand"]
    /\ UNCHANGED <<is_connected, client_mutex, channels>>

ProcessingCommand(t, s) ==
    /\ pc[t] = "ProcessingCommand"
    /\ pc[s] = "SentToConnection"
    /\ ChannelReceive("receiveChan")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_mutex>>

(* wire receiver *)

WireReceiverSend(t, s) ==
    /\ pc[t] = "Idle"
    /\ pc[s] = "ProcessingCommand"
    /\ pc' = [pc EXCEPT ![t] = "SentToConnection"]
    /\ UNCHANGED <<is_connected, channels, client_mutex>>

WireReceiverReset(t) ==
    /\ pc[t] = "SentToConnection"
    /\ ChannelSend("receiveChan", "message")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_mutex>>

Next ==
    \/ DialStart("client")
    \/ DialFinish("client")
    \/ HangupStart("client")
    \/ HangupFinish("client")
    \/ SendMessageStart("client")
    \/ SendMessageFinish("client", "connection")
    \/ SenderReceiveStart("connection", "client")
    \/ SenderReceiveFinish("connection")
    \/ ReceiveCommand("connection", "wire_receiver")
    \/ ProcessingCommand("connection", "wire_receiver")
    \/ WireReceiverReset("wire_receiver")
    \/ WireReceiverSend("wire_receiver", "connection")


WireReceiverInteraction ==
    WireReceiverSend("wire_receiver", "connection") \/ WireReceiverReset("wire_receiver")

Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(WireReceiverInteraction)
    /\ WF_vars(ReceiveCommand("connection", "wire_receiver"))


====
