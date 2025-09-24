------------------------------ MODULE PartitionRecovery ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Define constants directly in the spec (following your existing pattern)
Nodes == {"n1", "n2", "n3", "n4"}
TotalStake == 100
MaxSlots == 5
Stake == [n \in Nodes |-> 25]

\* Base consensus variables
VARIABLES
    finalized,
    leader,
    blocks,
    votes,
    notarized,
    fastFinalized,
    slowFinalized

\* Partition-specific variables
VARIABLES
    partitioned,     \* set of nodes that are partitioned
    networkHealed,   \* TRUE when partition is healed
    partitionStart   \* slot when partition started

vars == << finalized, leader, blocks, votes, notarized, fastFinalized, 
           slowFinalized, partitioned, networkHealed, partitionStart >>

\* Threshold calculations
ThresholdFast == (TotalStake * 4) \div 5  \* 80%
ThresholdSlow == (TotalStake * 3) \div 5  \* 60%

\* Stake calculation function
RECURSIVE StakeOf(_)
StakeOf(S) == IF S = {} THEN 0 ELSE
    LET x == CHOOSE y \in S : TRUE IN
    Stake[x] + StakeOf(S \ {x})

\* Available nodes (non-partitioned)
AvailableNodes == Nodes \ partitioned

\* Check if we have enough stake to proceed
HasSufficientStake(threshold) == 
    StakeOf(AvailableNodes) >= threshold

\* Initial state
Init ==
    /\ finalized = <<>>
    /\ leader = [s \in 1..MaxSlots |-> CHOOSE n \in Nodes: TRUE]
    /\ blocks = [s \in 1..MaxSlots |-> "NULL"]
    /\ votes = [s \in 1..MaxSlots |-> [n \in Nodes |-> "NULL"]]
    /\ notarized = [s \in 1..MaxSlots |-> "NULL"]
    /\ fastFinalized = [s \in 1..MaxSlots |-> "NULL"]
    /\ slowFinalized = [s \in 1..MaxSlots |-> "NULL"]
        /\ partitioned \in { S \in SUBSET Nodes : StakeOf(S) <= (TotalStake \div 3) }
    /\ networkHealed = FALSE
    /\ partitionStart = 1

\* Block proposal (leader must be available)
ProposeBlock(s) ==
    /\ blocks[s] = "NULL"
    /\ leader[s] \in AvailableNodes
    /\ blocks' = [blocks EXCEPT ![s] = "Block_" \o ToString(s)]
    /\ UNCHANGED <<finalized, leader, votes, notarized, fastFinalized, 
                   slowFinalized, partitioned, networkHealed, partitionStart>>

\* Vote casting (only available nodes can vote)
CastNotarVote(s, n) ==
    /\ blocks[s] # "NULL"
    /\ n \in AvailableNodes
    /\ votes[s][n] = "NULL"
    /\ votes' = [votes EXCEPT ![s][n] = blocks[s]]
    /\ UNCHANGED <<finalized, leader, blocks, notarized, fastFinalized,
                   slowFinalized, partitioned, networkHealed, partitionStart>>

\* Form notarization certificate (considering only available nodes)
FormNotarCert(s) ==
    /\ notarized[s] = "NULL"
    /\ blocks[s] # "NULL"
    /\ LET BlockHash == blocks[s]
           Voters == {node \in AvailableNodes : votes[s][node] = BlockHash}
       IN /\ StakeOf(Voters) >= ThresholdSlow
          /\ HasSufficientStake(ThresholdSlow)
    /\ notarized' = [notarized EXCEPT ![s] = blocks[s]]
    /\ UNCHANGED <<finalized, leader, blocks, votes, fastFinalized, 
                   slowFinalized, partitioned, networkHealed, partitionStart>>

\* Form fast finalization certificate
FormFastFinalCert(s) ==
    /\ fastFinalized[s] = "NULL"
    /\ blocks[s] # "NULL"
    /\ LET BlockHash == blocks[s]
           Voters == {node \in AvailableNodes : votes[s][node] = BlockHash}
       IN /\ StakeOf(Voters) >= ThresholdFast
          /\ HasSufficientStake(ThresholdFast)
    /\ fastFinalized' = [fastFinalized EXCEPT ![s] = blocks[s]]
    /\ UNCHANGED <<finalized, leader, blocks, votes, notarized, 
                   slowFinalized, partitioned, networkHealed, partitionStart>>

\* Form slow finalization certificate
FormSlowFinalCert(s) ==
    /\ slowFinalized[s] = "NULL"
    /\ notarized[s] # "NULL"
    /\ LET NotarizedHash == notarized[s]
           Voters == {node \in AvailableNodes : votes[s][node] = NotarizedHash}
       IN /\ StakeOf(Voters) >= ThresholdSlow
          /\ HasSufficientStake(ThresholdSlow)
    /\ slowFinalized' = [slowFinalized EXCEPT ![s] = notarized[s]]
    /\ UNCHANGED <<finalized, leader, blocks, votes, notarized, 
                   fastFinalized, partitioned, networkHealed, partitionStart>>

\* Network partition healing
HealPartition ==
    /\ ~networkHealed
    /\ networkHealed' = TRUE
    /\ partitioned' = {}
    /\ UNCHANGED <<finalized, leader, blocks, votes, notarized, 
                   fastFinalized, slowFinalized, partitionStart>>

\* Update finalized chain
UpdateFinalizedChain ==
    /\ \E s \in 1..MaxSlots :
        LET FinalBlockHash == IF fastFinalized[s] # "NULL" 
                             THEN fastFinalized[s] 
                             ELSE slowFinalized[s]
        IN /\ FinalBlockHash # "NULL"
           /\ \A i \in 1..Len(finalized) : finalized[i] # FinalBlockHash
           /\ finalized' = Append(finalized, FinalBlockHash)
    /\ UNCHANGED <<leader, blocks, votes, notarized, fastFinalized, 
                   slowFinalized, partitioned, networkHealed, partitionStart>>

\* Next state relation
Next ==
    \/ HealPartition
    \/ \E s \in 1..MaxSlots:
        \/ ProposeBlock(s)
        \/ \E n \in Nodes: CastNotarVote(s, n)
        \/ FormNotarCert(s)
        \/ FormFastFinalCert(s)
        \/ FormSlowFinalCert(s)
    \/ UpdateFinalizedChain

\* Specification
Spec == Init /\ [][Next]_vars

\* THEOREM 9: Safety invariants during and after partition
PartitionSafety ==
    \A s \in 1..MaxSlots:
        (fastFinalized[s] # "NULL" /\ slowFinalized[s] # "NULL") => 
        (fastFinalized[s] = slowFinalized[s])

\* THEOREM 9: Liveness property - eventual progress after healing
EventualProgress ==
    networkHealed => <>(\E s \in 1..MaxSlots : 
        fastFinalized[s] # "NULL" \/ slowFinalized[s] # "NULL")

\* Additional safety property: no progress with insufficient stake
NoProgressWithoutStake ==
    (~HasSufficientStake(ThresholdSlow)) => 
    (\A s \in 1..MaxSlots : fastFinalized[s] = "NULL" /\ slowFinalized[s] = "NULL")

=============================================================================