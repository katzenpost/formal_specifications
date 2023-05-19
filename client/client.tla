------------------------------- MODULE client -------------------------------

EXTENDS Integers, TLC

VARIABLES state, connected, 

vars == <<red, yellow, green>>

Init == /\ red = 1
        /\ yellow = 0
        /\ green = 0

Switch == /\ red = 1
          /\ red' = 0
          /\ green' = 1
          /\ yellow' = yellow
       \/ /\ green = 1
          /\ green' = 0
          /\ yellow' = 1
          /\ red' = red
       \/ /\ yellow = 1
          /\ yellow' = 0
          /\ red' = 1
          /\ green' = green
          
Next == Switch          

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

TypeOK == /\ red \in {0,1}
          /\ green \in {0,1}
          /\ yellow \in {0,1} 

OneLightOnly == red + yellow + green = 1


=============================================================================
\* Modification History
\* Last modified Thu May 18 19:23:12 EDT 2023 by human
\* Created Thu May 18 18:48:50 EDT 2023 by human
