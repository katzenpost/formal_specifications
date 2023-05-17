
Authors: ChatGPT4 and David Stainton

Goal: Model the high level abstraction of the Katzenpost directory authority
(also known as dirauth and PKI) protocol.

------------------------------ MODULE dirauth ------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT DirAuthNodes, Relays

VARIABLES consensus, votes, keys, phase, descriptors, UnreliableActors, epoch

vars == <<consensus, votes, keys, phase, descriptors, UnreliableActors, epoch>>

Init ==
    /\ epoch = 0
    /\ consensus = <<>>
    /\ votes = [n \in DirAuthNodes |-> {}]
    /\ keys = [n \in DirAuthNodes |-> "none"]
    /\ descriptors = [n \in DirAuthNodes |-> {}]
    /\ phase = "KeyGeneration"
    /\ UnreliableActors = {}

Threshold == (Cardinality(DirAuthNodes \ UnreliableActors) \div 2) + 1

BecomeUnreliableActor(n) ==
    /\ phase \in {"KeyGeneration", "DescriptorCollection", "DescriptorExchange", "Vote"}
    /\ n \notin UnreliableActors
    /\ UnreliableActors' = UnreliableActors \union {n}
    /\ UNCHANGED <<votes, consensus, keys, descriptors, phase, epoch>>

FailedProtocolRound ==
    /\ Cardinality(DirAuthNodes \ UnreliableActors) < 3
    /\ phase' = "KeyGeneration"
    /\ UnreliableActors' = {}
    /\ votes' = [n \in DirAuthNodes |-> <<>>]
    /\ keys' = [n \in DirAuthNodes |-> "none"]
    /\ consensus' = <<>>
    /\ descriptors' = [n \in DirAuthNodes |-> {}]
    /\ UNCHANGED <<epoch>>

FailedConsensus ==
    /\ phase = "FailedConsensus"
    /\ phase' = "KeyGeneration"
    /\ UnreliableActors' = {}
    /\ votes' = [n \in DirAuthNodes |-> <<>>]
    /\ keys' = [n \in DirAuthNodes |-> "none"]
    /\ consensus' = <<>>
    /\ descriptors' = [n \in DirAuthNodes |-> {}]

KeyGeneration(n) ==
    /\ phase = "KeyGeneration"
    /\ IF Cardinality({m \in DirAuthNodes : keys[m] /= "none"}) < 3
        THEN
            /\ UNCHANGED <<votes, consensus, descriptors, UnreliableActors, epoch, keys>>
            /\ phase' = "FailedConsensus"
        ELSE
            /\ UNCHANGED <<votes, consensus, descriptors, UnreliableActors, epoch>>
            /\ keys' = [keys EXCEPT ![n] = "key"]
            /\ phase' = "DescriptorCollection"

DescriptorCollection(n, m) ==
    /\ phase = "DescriptorCollection"
    /\ keys[n] /= "none"
    /\ m \in Relays
    /\ UNCHANGED <<votes, consensus, keys, UnreliableActors, epoch>>
    /\ descriptors' = [descriptors EXCEPT ![n] = @ \union {m}]
    /\ phase' = "DescriptorExchange"

DescriptorExchange(n, m) ==
    /\ phase = "DescriptorExchange"
    /\ keys[n] /= "none"
    /\ keys[m] /= "none"
    /\ m /= n
    /\ UNCHANGED <<votes, consensus, keys, epoch>>
    /\ descriptors' = [descriptors EXCEPT ![n] = IF n \in UnreliableActors THEN @ \ {RandomElement(@)} ELSE @ \union descriptors[m]]
    /\ phase' = "Vote"
    
Consensus ==
    /\ phase = "Consensus"
    /\ UNCHANGED <<votes, keys, descriptors>>
    /\ LET Ups == {n \in DirAuthNodes: Len(votes[n]) > 0 /\ votes[n][Len(votes[n])] = "up"}
       IN Cardinality(Ups) >= Threshold
    /\ consensus' = Append(consensus, <<epoch, "up">>)
    /\ phase' = "KeyGeneration"
    /\ UnreliableActors' = {}
  
VoteOnDescriptorSet(n, D) ==
    /\ phase = "Vote"
    /\ keys[n] /= "none"
    /\ descriptors \subseteq Relays
    /\ UNCHANGED <<consensus, keys, epoch>>
    /\ votes' = [votes EXCEPT ![n] = @ \union {D}]
    /\ LET MatchingVotes == {x \in DirAuthNodes : \E d \in votes'[x] : d = D}
       IN IF Cardinality(MatchingVotes) >= Threshold
          THEN phase' = "Consensus"
          ELSE UNCHANGED phase

ByzantineVote(dirauth_node, descriptor_set) ==
    /\ phase = "Vote"
    /\ keys[dirauth_node] /= "none"
    /\ descriptor_set \subseteq Relays
    /\ \E descriptor_set1, descriptor_set2 \in SUBSET descriptor_set:
        /\ descriptor_set1 \subseteq descriptor_set
        /\ descriptor_set2 \subseteq descriptor_set
        /\ descriptor_set1 /= descriptor_set2
        /\ \E m1, m2 \in DirAuthNodes \ {dirauth_node}:
            /\ m1 /= m2
            /\ votes' = [votes EXCEPT ![dirauth_node] = @ \union descriptor_set1, ![m1] = @ \union descriptor_set1, ![m2] = @ \union descriptor_set2]
    /\ UNCHANGED <<consensus, keys, epoch, phase>>

Vote(dirauth_node, descriptor_set) ==
    \/ VoteOnDescriptorSet(dirauth_node, descriptor_set)
    \/ ByzantineVote(dirauth_node, descriptor_set)

IncreaseEpoch ==
    /\ \/ Consensus
       \/ FailedProtocolRound
       \/ FailedConsensus
    /\ epoch' = epoch + 1

OtherActions ==
    /\ \/ \E N \in SUBSET DirAuthNodes : N /= {} /\ \A n \in N : KeyGeneration(n)
       \/ \E N \in SUBSET DirAuthNodes, M \in SUBSET Relays : N /= {} /\ M /= {} /\ \A n \in N, m \in M : DescriptorCollection(n, m)
       \/ \E N \in SUBSET DirAuthNodes : N /= {} /\ \A n, m \in N : DescriptorExchange(n, m)
       \/ \E N \in SUBSET DirAuthNodes : N /= {} /\ \A n, m \in N : Vote(n, m)
       \/ \E n \in DirAuthNodes : BecomeUnreliableActor(n)

Next ==
    /\ \/ IncreaseEpoch
       \/ OtherActions

PhaseInvariant == phase \in {"KeyGeneration", "DescriptorCollection", "DescriptorExchange", "Vote", "Consensus"}
KeysInvariant == \A n \in DirAuthNodes : keys[n] \in {"none", "key"}
DescriptorsInvariant == \A n \in DirAuthNodes : descriptors[n] \subseteq Relays
ConsensusAgreement ==
    /\ phase = "Consensus"
    => Cardinality({n \in DirAuthNodes : votes[n] = consensus}) >= Threshold
    
ReliabilityInvariant ==
    /\ phase = "Consensus"
    => consensus = [n \in DirAuthNodes |-> IF Len(votes[n]) > 0 THEN Head(votes[n]) ELSE "none"]

DecentralizationInvariant ==
    /\ phase = "Consensus"
    => \A n \in DirAuthNodes : votes[n] = consensus

AllKeyGenerationBeforeDescriptorCollection == 
    [](\A n \in DirAuthNodes : phase[n] = "KeyGeneration") => <>(\A m \in DirAuthNodes : phase[m] = "DescriptorCollection")
AllDescriptorCollectionBeforeDescriptorExchange == 
    [](\A n \in DirAuthNodes : phase[n] = "DescriptorCollection") => <>(\A m \in DirAuthNodes : phase[m] = "DescriptorExchange")
AllDescriptorExchangeBeforeVote == 
    [](\A n \in DirAuthNodes : phase[n] = "DescriptorExchange") => <>(\A m \in DirAuthNodes : phase[m] = "Vote")
AllVoteBeforeConsensus == 
    [](\A n \in DirAuthNodes : phase[n] = "Vote") => <>(\A m \in DirAuthNodes : phase[m] = "Consensus")

NoSybilAttack ==
    \A n \in DirAuthNodes : Len(descriptors[n]) <= Threshold

Liveness == []<>(phase = "Consensus")
Progress == []<>(phase = "Consensus") ~> []<>(phase = "KeyGeneration")

EventuallyReachConsensus == <>[](phase = "Consensus")
AlwaysReturnToKeyGeneration == []<>(phase = "KeyGeneration")
ConsensusLeadsToKeyGeneration == [](phase = "Consensus" ~> phase = "KeyGeneration")
EpochIncreaseInvariant == [][IncreaseEpoch]_epoch

NoStarvation == \A n, m \in DirAuthNodes : WF_vars(Vote(n, m))

VotesInvariant == \A n \in DirAuthNodes : \A v \in votes[n] : v \subseteq Relays

NoLying1 ==
    \A n \in DirAuthNodes : 
        \A D1, D2 \in SUBSET Relays :
            \A sets \in votes[n] :
            sets /= {} /\ ~((D1 \in votes[n] /\ D2 \in votes[n]) /\ D1 /= D2)
    
NoLying2 ==
    \A n \in DirAuthNodes :
    \A D \in SUBSET Relays :
    ~ByzantineVote(n, D)
    
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
         /\ Liveness
         /\ Progress
         /\ PhaseInvariant
         /\ KeysInvariant
         /\ VotesInvariant
         /\ DescriptorsInvariant
         /\ ConsensusAgreement
         /\ ReliabilityInvariant
         /\ DecentralizationInvariant
         /\ AllKeyGenerationBeforeDescriptorCollection
         /\ AllDescriptorCollectionBeforeDescriptorExchange
         /\ AllDescriptorExchangeBeforeVote
         /\ AllVoteBeforeConsensus
         /\ EpochIncreaseInvariant
         /\ EventuallyReachConsensus
         /\ AlwaysReturnToKeyGeneration
         /\ ConsensusLeadsToKeyGeneration
         /\ EpochIncreaseInvariant

=============================================================================
