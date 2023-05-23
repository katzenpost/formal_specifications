------------------------------- MODULE client -------------------------------

EXTENDS TLC

VARIABLES state, eventChan

vars == <<state, eventChan>>

Init == /\ state = "unstarted"
    	/\ eventChan = "run"

Switch == /\ eventChan = "run"
          /\ state = "unstarted"
          /\ state' = "connecting"
          /\ eventChan' = ""
      \/  /\ eventChan = "send message"
          /\ state = "connected"
          /\ state' = "sending message"
          /\ eventChan' = ""          
Next == Switch          

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

TypeOK == /\ state \in {"unstarted", "connecting", "connected", "disconnected", "sending message", "receiving message"}
          /\ eventChan \in {"run", "stop", "connect", "disconnect"}

=============================================================================
