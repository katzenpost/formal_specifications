
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
max_epoch <- 5
dirauth_min_num <- 3

------------------------------ MODULE dirauth ------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT dirauth_nodes, relays, max_epoch, dirauth_min_num

VARIABLES phase, epoch, descriptors, votes, unreliable_actors, bad_actors
vars == <<phase, epoch, descriptors, votes, unreliable_actors, bad_actors>>

ProtocolPhaseInvariant == phase \in {"Relay Key Generation",
                                     "Descriptor Collection",
                                     "Descriptor Exchange",
                                     "Vote",
                                     "Consensus",
                                     "Tabulate Votes",
                                     "Failed Consensus"}

EpochInit  == epoch = 0
EpochNext  ==  epoch' = IF epoch # max_epoch THEN epoch + 1 ELSE 0
EpochClock  ==  EpochInit /\ [][EpochNext]_epoch

Threshold == (Cardinality(dirauth_nodes \ unreliable_actors) \div 2) + 1

Init ==
    /\ EpochInit
    /\ phase = "Relay Key Generation"
    /\ descriptors = [n \in dirauth_nodes |-> {}]
    /\ votes = [n \in dirauth_nodes |-> {}]
    /\ unreliable_actors = {}
    /\ bad_actors = {}

RelayKeyGeneration ==
    /\ phase = "Relay Key Generation"
    /\ phase' = "Descriptor Collection"
    /\ unreliable_actors' = {}
    /\ bad_actors' = {}
    /\ votes' = [n \in dirauth_nodes |-> {}]
    /\ descriptors' = [n \in dirauth_nodes |-> {}]
    /\ UNCHANGED <<epoch>>

(* All dirauth nodes (excluding unreliable actors) collect descriptors *)
DescriptorCollection ==
    /\ phase = "Descriptor Collection"
    /\ \E n \in dirauth_nodes \ unreliable_actors:
         \E m \in relays: 
            descriptors' = [descriptors EXCEPT ![n] = @ \union {m}]
    /\ phase' = IF \E n \in dirauth_nodes \ unreliable_actors: \E m \in relays: m \notin descriptors[n]
                THEN "Descriptor Collection"
                ELSE "Descriptor Exchange"
    /\ UNCHANGED <<epoch, votes, unreliable_actors, bad_actors>>

DescriptorExchange ==
    /\ phase = "Descriptor Exchange"
    /\ \E n1 \in dirauth_nodes \ unreliable_actors: 
         \E n2 \in dirauth_nodes \ unreliable_actors: 
            descriptors' = [descriptors EXCEPT ![n1] = @ \union descriptors[n2]]
    /\ phase' = IF \E n \in dirauth_nodes \ unreliable_actors: 
                    \E m \in dirauth_nodes \ unreliable_actors: 
                        \E d \in descriptors[m]:
                            d \notin descriptors[n]
                THEN "Descriptor Exchange"
                ELSE "Vote"
    /\ UNCHANGED <<epoch, votes, unreliable_actors, bad_actors>>

NormalVote ==
    /\ phase = "Vote"
    /\ \E n \in dirauth_nodes \ unreliable_actors:
         \E m \in relays: 
            votes' = [votes EXCEPT ![n] = @ \union {m}]
    /\ phase' = IF \E n \in dirauth_nodes \ unreliable_actors: votes[n] # {}
                THEN "Vote"
                ELSE "Tabulate Votes"
    /\ UNCHANGED <<epoch, descriptors, unreliable_actors, bad_actors>>


Vote ==
    /\ phase = "Vote"
    /\ IF \E n \in bad_actors
       THEN ByzantineVote
       ELSE NormalVote
    /\ LET n == CHOOSE n \in dirauth_nodes \ unreliable_actors: TRUE
       IN IF exists (x : votes[n] | x # {})
          THEN phase' = "Vote"
          ELSE phase' = "Tabulate Votes"
    /\ UNCHANGED <<epoch, descriptors, unreliable_actors, bad_actors>> 


TabulateVotes ==
    /\ phase = "Tabulate Votes"
    /\ LET VoteSets == {votes[m]: m \in dirauth_nodes}
           PossibleConsensus == {D \in VoteSets : Cardinality({m \in dirauth_nodes : votes[m] = D}) >= Threshold}
       IN IF PossibleConsensus /= {} 
          THEN phase' = "Consensus"
          ELSE phase' = "Failed Consensus"
    /\ UNCHANGED <<epoch, descriptors, votes, unreliable_actors, bad_actors>>

Consensus ==
    /\ phase = "Consensus"
    /\ phase' = "Relay Key Generation"
    /\ EpochNext
    /\ UNCHANGED <<votes, descriptors, unreliable_actors, bad_actors>>

FailedConsensus ==
    /\ phase = "Failed Consensus"
    /\ phase' = "Relay Key Generation"
    /\ EpochNext
    /\ UNCHANGED <<votes, descriptors, unreliable_actors, bad_actors>>

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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Liveness /\ Progress /\ EpochClock

=============================================================================
