------------------------------- MODULE client -------------------------------

EXTENDS TLC

VARIABLES state

vars == <<state>>

Init == /\ state = "unstarted"

Start == /\ state = "unstarted"
         /\ state' = "connecting"

Connect == /\ state = "connecting"
           /\  \/ state' = "connected"
               \/ state' = "disconnected"

ConnectionFailure ==
          /\ state = "disconnected"
          /\ state' = "connecting"

FinalizeConnection ==
         /\ state = "connected"
         /\ state' = "idle"

Idle ==   /\ state = "idle"
          /\   \/ state' = "sending message"
               \/ state' = "receiving message"
               \/ state' = "get new pki doc"
               \/ state' = "idle"

Recv == /\ state = "receiving message"
        /\ state' = "idle"

Send ==  /\ state = "sending message"
         /\ state' = "idle"

UpdatePKIDoc ==
         /\ state = "get new pki doc"
         /\ state' = "update timers"

UpdateTimers ==
         /\ state = "update timers"
         /\ state' = "idle"

Next == \/ Start
        \/ Connect
        \/ ConnectionFailure
        \/ FinalizeConnection
        \/ Idle
        \/ Recv
        \/ Send
        \/ UpdatePKIDoc
        \/ UpdateTimers

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

StateTypeOK == /\ state \in {
                    "unstarted",
                    "idle",
                    "connecting",
                    "connected",
                    "disconnected",
                    "sending message",
                    "receiving message",
                    "get new pki doc",
                    "update timers"}

=============================================================================
