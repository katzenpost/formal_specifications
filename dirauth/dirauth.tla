
This specification attempts to model the Katzenpost Directory Authority protocol.
However we do so at a high enough level of abstraction that it most likely
also models the Tor Directory Authority protocol as they are quite similar.

The Katzenpost dirauth protocol spec is found here:
https://github.com/katzenpost/katzenpost/blob/main/docs/specs/pki.rst

Tor dirauth spec is here:
https://gitlab.torproject.org/tpo/core/torspec/-/blob/main/dir-spec.txt

Here's a summary:

The protocol repeats itself like a traffic light.

Relays generate new keys.
Relays upload their descriptors to the dirauth nodes.
Dirauth nodes exchange descriptors.
Dirauth nodes vote, which is to say that they
exchange sets of descriptors that they know about.
Next vote tabulation is done where if multiple nodes
vote on the same set of descriptors this counts towards
a consensus. And consensus is reached if the number of votes
is equal or greater than the threshold. The threshold is defined
to be the number of participating nodes divided by two plus one.
If one or more dirauth nodes becomes a bad actor they can
cause the voting process to go to the failed consensus state.

The protocol is not a BFT and thus cannot prevent these kinds of
bad actors from causing the vote to fail.

Ultimately I'd like to make theorems about the protocol boundaries
for different parameters, namely number of dirauth nodes.

Model checking it:

dirauth_min_num needs to be set to 3 for the model to work

here's some example params:

dirauth_nodes <-{"a1", "a2", "a3"}
relays <- {"r1", "r2","r3"}
dirauth_min_num <- 3

------------------------------ MODULE dirauth ------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT dirauth_nodes, bad_actors, relays, dirauth_min_num

VARIABLES phase, descriptors, votes
vars == <<phase, descriptors, votes>>

ProtocolPhaseInvariant == phase \in {"Relay Key Generation",
                                     "Descriptor Collection",
                                     "Descriptor Exchange",
                                     "Vote",
                                     "Consensus",
                                     "Tabulate Votes",
                                     "Failed Consensus"}

Threshold == (Cardinality(dirauth_nodes) \div 2) + 1

ConsensusFailureWithBadActor ==
    /\ LET N == {Cardinality(dirauth_nodes)}:
        /\ Cardinality(bad_actors) = N-3
    => <>[] (phase = "Failed Consensus")

Init ==
    /\ phase = "Relay Key Generation"
    /\ descriptors = [n \in dirauth_nodes |-> {}]
    /\ votes = [n \in dirauth_nodes |-> {}]

RelayKeyGeneration ==
    /\ phase = "Relay Key Generation"
    /\ phase' = "Descriptor Collection"
    /\ votes' = [n \in dirauth_nodes |-> {}]
    /\ descriptors' = [n \in dirauth_nodes |-> {}]
    /\ UNCHANGED <<>>

DescriptorCollection ==
    /\ phase = "Descriptor Collection"
    /\ \E n \in dirauth_nodes:
         \E m \in relays: 
            descriptors' = [descriptors EXCEPT ![n] = @ \union {m}]
    /\ phase' = IF \E n \in dirauth_nodes: \E m \in relays: m \notin descriptors[n]
                THEN "Descriptor Collection"
                ELSE "Descriptor Exchange"
    /\ UNCHANGED <<votes>>

DescriptorExchange ==
    /\ phase = "Descriptor Exchange"
    /\ \E n1 \in dirauth_nodes: 
         \E n2 \in dirauth_nodes: 
            descriptors' = [descriptors EXCEPT ![n1] = @ \union descriptors[n2]]
    /\ phase' = IF \A n \in dirauth_nodes: descriptors[n] # {}
                THEN "Descriptor Exchange"
                ELSE "Vote"
    /\ UNCHANGED <<votes>>

NormalVote ==
    /\ phase = "Vote"
    /\ \E n1 \in dirauth_nodes:
         \E n2 \in dirauth_nodes:
         /\ n1 /= n2
         /\ votes' = [votes EXCEPT ![n1] = @ \union descriptors[n2]]
    /\ phase' = IF \A n \in dirauth_nodes: votes[n] # {}
                THEN "Tabulate Votes"
                ELSE "Vote"
    /\ UNCHANGED <<descriptors>>

ByzantineVote ==
    /\ phase = "Vote"
    /\ \E n1 \in dirauth_nodes:
        /\ \E n2 \in dirauth_nodes:
            /\ n1 /= n2
            /\ \E descriptor_set1, descriptor_set2 \in SUBSET descriptors[n2]:
                /\ descriptor_set1 /= descriptor_set2
                /\ descriptor_set1 \subseteq descriptor_set2
                /\ (votes' = [votes EXCEPT ![n1] = @ \union {descriptor_set1}]
                    \/ votes' = [votes EXCEPT ![n1] = @ \union {descriptor_set2}])
    /\ phase' = IF \A n \in dirauth_nodes: votes[n] # {}
                THEN "Vote"
                ELSE "Tabulate Votes"
    /\ UNCHANGED <<descriptors>>

Vote ==
    \/ NormalVote
    \/ ByzantineVote

TabulateVotes ==
    /\ phase = "Tabulate Votes"
    /\ LET VoteSets == {votes[m]: m \in dirauth_nodes}
           PossibleConsensus == {D \in VoteSets : Cardinality({m \in dirauth_nodes : votes[m] = D}) >= Threshold}
       IN IF PossibleConsensus /= {} 
          THEN phase' = "Consensus"
          ELSE phase' = "Failed Consensus"
    /\ UNCHANGED <<descriptors, votes>>

Consensus ==
    /\ phase = "Consensus"
    /\ phase' = "Relay Key Generation"
    /\ UNCHANGED <<votes, descriptors>>

FailedConsensus ==
    /\ phase = "Failed Consensus"
    /\ phase' = "Relay Key Generation"
    /\ UNCHANGED <<votes, descriptors>>

ProtocolPhases ==
    /\  \/ RelayKeyGeneration
        \/ DescriptorCollection
        \/ DescriptorExchange
        \/ Vote
        \/ TabulateVotes
        \/ Consensus
        \/ FailedConsensus

Next == ProtocolPhases

Liveness == []<>(phase = "Consensus")
Progress == []<>(phase = "Consensus") ~> []<>(phase = "Relay Key Generation")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Liveness /\ Progress

=============================================================================
