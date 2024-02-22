---- MODULE client2 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MAX_CHANNEL_SIZE

VARIABLES channels, is_connected, client_mutex, pc
vars == <<channels, is_connected, client_mutex, pc>>

Init ==
    /\ is_connected = FALSE
    /\ client_mutex = 0
    /\ channels = [chan \in {"sendChan", "wire_in_ch", "wire_out_ch", "wire_bridge_ch"} |-> <<>>]
    /\ pc = [t \in {"wire_in", "wire_out", "connection", "client"} |-> "Idle"]


\* reusable actions

ChannelSend(channelName, message) ==
    /\ Len(channels[channelName]) < IF channelName = "wire_bridge_ch" THEN MAX_CHANNEL_SIZE + 1 ELSE MAX_CHANNEL_SIZE
    /\ channels' = [channels EXCEPT ![channelName] = Append(@, message)]

ChannelReceive(channelName) ==
    /\ Len(channels[channelName]) > 0
    /\ channels' = [channels EXCEPT ![channelName] = Tail(channels[channelName])]

AcquireMutex(t, lock) ==
    /\ lock = 0
    /\ lock' = t

ReleaseMutex(t, lock) ==
    /\ lock = t
    /\ lock' = 0

\* client main

DialStart(t) ==
    /\ pc[t] = "Idle"
    /\ AcquireMutex(t, client_mutex)
    /\ is_connected = FALSE
    /\ pc' = [pc EXCEPT ![t] = "Dialing"]
    /\ UNCHANGED <<channels, is_connected>>

DialFinish(t) ==
    /\ pc[t] = "Dialing"
    /\ is_connected = FALSE
    /\ is_connected' = TRUE
    /\ ReleaseMutex(t, client_mutex)
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels>>

HangupStart(t) ==
    /\ pc[t] = "Idle"
    /\ AcquireMutex(t, client_mutex)
    /\ is_connected = TRUE
    /\ pc' = [pc EXCEPT ![t] = "HangingUp"]
    /\ UNCHANGED <<channels, is_connected>>

HangupFinish(t) ==
    /\ pc[t] = "HangingUp"
    /\ is_connected = TRUE
    /\ is_connected' = FALSE
    /\ ReleaseMutex(t, client_mutex)
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<channels>>

SendMessageStart(t) ==
    /\ pc[t] = "Idle"
    /\ AcquireMutex(t, client_mutex)
    /\ is_connected = TRUE
    /\ pc' = [pc EXCEPT ![t] = "PrepareSendingMessage1"]
    /\ UNCHANGED <<channels, is_connected>>

PrepareSendingMessage1(t) ==
    /\ pc[t] = "PrepareSendingMessage1"
    /\ ReleaseMutex(t, client_mutex)
    /\ pc' = [pc EXCEPT ![t] = "PrepareSendingMessage2"]
    /\ UNCHANGED <<is_connected, channels>>

PrepareSendingMessage2(t) ==
    /\ pc[t] = "PrepareSendingMessage2"
    /\ ChannelSend("sendChan", "message")
    /\ pc' = [pc EXCEPT ![t] = "FinishSendingMessage"]
    /\ UNCHANGED <<is_connected, client_mutex>>

FinishSendingMessage(t) ==
    /\ pc[t] = "FinishSendingMessage"
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, channels, client_mutex>>


\* connection

SenderReceiveStart(t) ==
    /\ pc[t] = "Idle"
    /\ ChannelReceive("sendChan")
    /\ pc' = [pc EXCEPT ![t] = "ProcessingMessage"]
    /\ UNCHANGED <<is_connected, client_mutex>>

SenderReceiveFinish(t) ==
    /\ pc[t] = "ProcessingMessage"
    /\ ChannelSend("wire_out_ch", "message")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_mutex>>

ReceiveCommand(t) ==
    /\ pc[t] = "Idle"
    /\ ChannelReceive("wire_in_ch")
    /\ pc' = [pc EXCEPT ![t] = "ProcessingCommand"]
    /\ UNCHANGED <<is_connected, client_mutex>>

ProcessingCommand(t) ==
    /\ pc[t] = "ProcessingCommand"
    /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<is_connected, client_mutex, channels>>

\* wire receiver

WireIn(t) ==
    /\ pc[t] = "Idle"
    /\ ChannelReceive("wire_out_ch")
    /\  \/ pc' = [pc EXCEPT ![t] = "ProxyingIn"]
        \/ pc' = [pc EXCEPT ![t] = "Idle"] \* lossy network drops packets

WireInReset(t) ==
    /\ pc[t] = "ProxyingIn"
    /\ ChannelSend("wire_bridge_ch", "message")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]

WireOut(t) == 
    /\ pc[t] = "Idle"
    /\ ChannelReceive("wire_bridge_ch")
    /\ pc' = [pc EXCEPT ![t] = "ProxyingOut"]

WireProxying(t) ==
    /\ pc[t] = "ProxyingOut"
    /\ ChannelSend("wire_in_ch", "message")
    /\ pc' = [pc EXCEPT ![t] = "Idle"]

WireReceiverInteraction ==
    /\  \/ WireIn("wire_in")
        \/ WireInReset("wire_in")
        \/ WireOut("wire_out")
        \/ WireProxying("wire_out")
    /\ UNCHANGED <<is_connected, client_mutex>>


Next ==
    \/ DialStart("client")
    \/ DialFinish("client")
    \/ HangupStart("client")
    \/ HangupFinish("client")
    \/ SendMessageStart("client")
    \/ PrepareSendingMessage1("client")
    \/ PrepareSendingMessage2("client")
    \/ FinishSendingMessage("client")
    \/ SenderReceiveStart("connection")
    \/ SenderReceiveFinish("connection")
    \/ ReceiveCommand("connection")
    \/ ProcessingCommand("connection")
    \/ WireReceiverInteraction

Fairness ==
    /\ WF_vars(Next)
    /\ SF_vars(WireReceiverInteraction)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

====
