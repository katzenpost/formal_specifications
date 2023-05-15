
Authors: ChatGPT4 and David Stainton

Goal: Model the high level abstraction of the Katzenpost directory authority
(also known as dirauth and PKI) protocol.

------------------------------ MODULE dirauth ------------------------------

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT DirAuthNodes, Relays

VARIABLES consensus, votes, keys, phase, descriptors, threshold, BadActors

vars == <<consensus, votes, keys, phase, descriptors, threshold, BadActors>>

Init ==
    /\ consensus = <<>>
    /\ votes = [n \in DirAuthNodes |-> <<>>]
    /\ keys = [n \in DirAuthNodes |-> "none"]
    /\ descriptors = [n \in DirAuthNodes |-> {}]
    /\ phase = "KeyGeneration"
    /\ threshold = (Cardinality(DirAuthNodes) \div 2) + 1
    /\ BadActors = {}

BecomeBadActor(n) ==
    /\ phase \in {"KeyGeneration", "DescriptorCollection", "DescriptorExchange", "Vote"}
    /\ n \notin BadActors
    /\ BadActors' = BadActors \union {n}
    /\ UNCHANGED <<votes, consensus, keys, descriptors, phase>>

FailedProtocolRound ==
    /\ Cardinality(DirAuthNodes \ BadActors) < 3
    /\ phase' = "KeyGeneration"
    /\ BadActors' = {}
    /\ votes' = [n \in DirAuthNodes |-> <<>>]
    /\ keys' = [n \in DirAuthNodes |-> "none"]
    /\ consensus' = <<>>
    /\ descriptors' = [n \in DirAuthNodes |-> {}]

KeyGeneration(n) ==
    /\ phase = "KeyGeneration"
    /\ UNCHANGED <<votes, consensus, descriptors, BadActors>>
    /\ keys' = [keys EXCEPT ![n] = "key"]
    /\ phase' = "DescriptorCollection"

DescriptorCollection(n, m) ==
    /\ phase = "DescriptorCollection"
    /\ keys[n] /= "none"
    /\ m \in Relays
    /\ UNCHANGED <<votes, consensus, keys, BadActors>>
    /\ descriptors' = [descriptors EXCEPT ![n] = @ \union {m}]
    /\ phase' = "DescriptorExchange"

DescriptorExchange(n, m) ==
    /\ phase = "DescriptorExchange"
    /\ keys[n] /= "none"
    /\ keys[m] /= "none"
    /\ m /= n
    /\ UNCHANGED <<votes, consensus, keys>>
    /\ descriptors' = [descriptors EXCEPT ![n] = IF n \in BadActors THEN @ \ {RandomElement(@)} ELSE @ \union descriptors[m]]
    /\ phase' = "Vote"

Consensus ==
    /\ phase = "Consensus"
    /\ UNCHANGED <<votes, keys, descriptors>>
    /\ LET Ups == {n \in DirAuthNodes: Len(votes[n]) > 0 /\ votes[n][Len(votes[n])] = "up"}
       IN Cardinality(Ups) >= threshold
    /\ consensus' = Append(consensus, "up")
    /\ phase' = "KeyGeneration"
    /\ BadActors' = {}
 
VoteGood(n, m) ==
    /\ phase = "Vote"
    /\ keys[n] /= "none"
    /\ keys[m] /= "none"
    /\ m /= n
    /\ UNCHANGED <<consensus, keys, descriptors>>
    /\ votes' = [votes EXCEPT ![n] = Append(@, "up")]
    /\ IF \A x \in DirAuthNodes : Len(votes'[x]) > 0 \/ votes'[x][Len(votes'[x])] = "no-vote" 
        THEN phase' = "Consensus"
        ELSE UNCHANGED phase 

VoteBad(n, m) ==
    /\ phase = "Vote"
    /\ keys[n] /= "none"
    /\ keys[m] /= "none"
    /\ m /= n
    /\ n \in BadActors
    /\ UNCHANGED <<consensus, keys, descriptors>>
    /\ votes' = [votes EXCEPT ![n] = Append(@, "down")]
    /\ IF \A x \in DirAuthNodes : Len(votes'[x]) > 0 \/ votes'[x][Len(votes'[x])] = "no-vote"
        THEN phase' = "Consensus"
        ELSE UNCHANGED phase

NoVote(n) ==
    /\ phase = "Vote"
    /\ keys[n] /= "none"
    /\ UNCHANGED <<consensus, keys, descriptors>>
    /\ votes' = [votes EXCEPT ![n] = Append(@, "no-vote")]
    /\ IF \A x \in DirAuthNodes : Len(votes'[x]) > 0 \/ votes'[x][Len(votes'[x])] = "no-vote"
        THEN phase' = "Consensus"
        ELSE UNCHANGED phase

Vote(n, m) ==
    /\ VoteGood(n, m)
    /\ VoteBad(n, m)
    /\ NoVote(n)

Next ==
    /\ threshold' = (Cardinality(DirAuthNodes \ BadActors) \div 2) + 1
    /\ \/ \E N \in SUBSET DirAuthNodes : N /= {} /\ \A n \in N : KeyGeneration(n)
       \/ \E N \in SUBSET DirAuthNodes, M \in SUBSET Relays : N /= {} /\ M /= {} /\ \A n \in N, m \in M : DescriptorCollection(n, m)
       \/ \E N \in SUBSET DirAuthNodes : N /= {} /\ \A n, m \in N : DescriptorExchange(n, m)
       \/ \E N \in SUBSET DirAuthNodes : N /= {} /\ \A n, m \in N : Vote(n, m)
       \/ Consensus
       \/ FailedProtocolRound
       \/ \E n \in DirAuthNodes : BecomeBadActor(n)


PhaseInvariant == phase \in {"KeyGeneration", "DescriptorCollection", "DescriptorExchange", "Vote", "Consensus"}
KeysInvariant == \A n \in DirAuthNodes : keys[n] \in {"none", "key"}
VotesInvariant == \A n \in DirAuthNodes : \A v \in Seq({"up", "down"}) : v \subseteq votes[n]
ConsensusInvariant == \A v \in Seq({"up", "down"}) : v \subseteq consensus
DescriptorsInvariant == \A n \in DirAuthNodes : descriptors[n] \subseteq Relays
NoDoubleVoting == \A n \in DirAuthNodes : Len(votes[n]) <= 1
ConsensusAgreement ==
    /\ phase = "Consensus"
    => Cardinality({n \in DirAuthNodes : votes[n] = consensus}) >= threshold
BadActorsCorrect ==
    \A n \in BadActors : \E m \in DirAuthNodes \ {n} : \E v \in votes[n] : v = "down"
    
ReliabilityInvariant ==
    /\ phase = "Consensus"
    => consensus = [n \in DirAuthNodes |-> IF Len(votes[n]) > 0 THEN Head(votes[n]) ELSE "none"]

IntegrityInvariant ==
    /\ phase \in {"Vote", "Consensus"}
    => \A n \in DirAuthNodes :
        \A v \in votes[n] :
            v \in {"up", "down"} /\ v \in UNION {descriptors[m] : m \in DirAuthNodes}

DecentralizationInvariant ==
    /\ phase = "Consensus"
    => \A n \in DirAuthNodes : votes[n] = consensus


AllKeyGenerationBeforeDescriptorCollection == 
    <>[](\A n \in DirAuthNodes : phase[n] = "KeyGeneration") => <>(\A m \in DirAuthNodes : phase[m] = "DescriptorCollection")
AllDescriptorCollectionBeforeDescriptorExchange == 
    <>[](\A n \in DirAuthNodes : phase[n] = "DescriptorCollection") => <>(\A m \in DirAuthNodes : phase[m] = "DescriptorExchange")
AllDescriptorExchangeBeforeVote == 
    <>[](\A n \in DirAuthNodes : phase[n] = "DescriptorExchange") => <>(\A m \in DirAuthNodes : phase[m] = "Vote")
AllVoteBeforeConsensus == 
    <>[](\A n \in DirAuthNodes : phase[n] = "Vote") => <>(\A m \in DirAuthNodes : phase[m] = "Consensus")

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
         /\ PhaseInvariant
         /\ KeysInvariant
         /\ VotesInvariant
         /\ ConsensusInvariant
         /\ DescriptorsInvariant
         /\ NoDoubleVoting
         /\ ConsensusAgreement
         /\ BadActorsCorrect
         /\ ReliabilityInvariant
         /\ IntegrityInvariant
         /\ DecentralizationInvariant
         /\ AllKeyGenerationBeforeDescriptorCollection
         /\ AllDescriptorCollectionBeforeDescriptorExchange
         /\ AllDescriptorExchangeBeforeVote
         /\ AllVoteBeforeConsensus
         

=============================================================================