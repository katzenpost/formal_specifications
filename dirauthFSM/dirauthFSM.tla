
attempt at modeling:
directory authority server finite state machine,
in katzenpost/authority/voting/server/state.go

states:

bootstrap
accept descriptor
accept vote
accept reveal
accept cert
accept signature
sleep between epochs

---- MODULE dirauthFSM ----
EXTENDS Integers
VARIABLES state, next_state, mutex, mutex_rcount

vars == <<state, next_state, mutex, mutex_rcount>>

LockRead ==
    /\ mutex \in {"unlocked", "read_locked"}
    /\ mutex' = "read_locked"
    /\ mutex_rcount' = mutex_rcount + 1

UnlockRead ==
    /\ mutex = "read_locked"
    /\ mutex' = "unlocked"
    /\ mutex_rcount > 0
    /\ mutex_rcount' = mutex_rcount - 1
    /\ IF mutex_rcount' = 0 THEN mutex' = "unlocked" ELSE mutex' = "read_locked"

LockWrite ==
    /\ mutex = "unlocked"
    /\ mutex_rcount = 0
    /\ mutex' = "wlocked"
    /\ UNCHANGED mutex_rcount

UnlockWrite ==
    /\ mutex = "wlocked"
    /\ mutex' = "unlocked"
    /\ UNCHANGED mutex_rcount

Bootstrap == /\ state = "bootstrap"
             /\ mutex = "wlocked"
             /\ next_state = ""
             /\ UNCHANGED <<mutex, mutex_rcount>>
             /\ \/ /\ state' = "sleep"
                   /\ next_state' = "accept descriptor"
                \/ /\ state' = "sleep" \* Too late to vote this round, sleep until next round.
                   /\ next_state' = "bootstrap"

AcceptDescriptor == /\ state = "accept descriptor"
                    /\ mutex = "wlocked"
                    /\ UNCHANGED <<mutex, mutex_rcount>>
                    /\ \/ /\ state' = "sleep"
                          /\ next_state' = "accept vote"
                       \/ /\ state' = "sleep" \* Not voting because insufficient descriptors uploaded for epoch
                          /\ next_state' = "bootstrap"

AcceptVote == /\ state = "accept vote"
              /\ mutex = "wlocked"
              /\ state' = "sleep"
              /\ next_state' = "accept reveal"
              /\ UNCHANGED <<mutex, mutex_rcount>>

AcceptReveal == /\ state = "accept reveal"
                /\ mutex = "wlocked"
                /\ state' = "sleep"
                /\ next_state' = "accept cert"
                /\ UNCHANGED <<mutex, mutex_rcount>>

AcceptCert == /\ state = "accept cert"
              /\ mutex = "wlocked"
              /\ state' = "sleep"
              /\ next_state' = "accept signature"
              /\ UNCHANGED <<mutex, mutex_rcount>>

AcceptSignature == /\ state = "accept signature"
                   /\ mutex = "wlocked"
                   /\ state' = "sleep"
                   /\ next_state' = "accept descriptor"
                   /\ UNCHANGED <<mutex, mutex_rcount>>

Wake == /\ state = "wake"
        /\ mutex = "unlocked"
        /\ mutex' = "wlocked"
        /\ state' = next_state
        /\ next_state' = ""
        /\ UNCHANGED <<mutex_rcount>>

Sleep == /\ state = "sleep"
         /\ state' = "wake"
         /\ UNCHANGED next_state
         /\ mutex' = "unlocked"
         /\ mutex_rcount' = 0

Next == \/ Sleep
        \/ Wake
        \/ Bootstrap
        \/ AcceptDescriptor
        \/ AcceptVote
        \/ AcceptReveal
        \/ AcceptCert
        \/ AcceptSignature

Init == /\ state = "bootstrap"
        /\ next_state = ""
        /\ mutex = "wlocked"
        /\ mutex_rcount = 0

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


MutexInvariant ==
    /\ mutex \in {"unlocked", "wlocked", "rlocked"}

MutexRcountInvariant ==
    /\ mutex_rcount \in 0..6

NextStateInvariant == 
    /\ next_state \in {"", "bootstrap",
                  "accept descriptor",
                  "accept vote",
                  "accept reveal",
                  "accept cert",
                  "accept signature",
                  "sleep",
                  "wake"}

StateInvariant == 
    /\ state \in {"bootstrap",
                  "accept descriptor",
                  "accept vote",
                  "accept reveal",
                  "accept cert",
                  "accept signature",
                  "sleep",
                  "wake"}

TypeInvariant == /\ StateInvariant
                 /\ NextStateInvariant
                 /\ MutexInvariant
                 /\ MutexRcountInvariant
====

