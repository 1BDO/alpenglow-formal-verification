-------------------------------- MODULE Votor --------------------------------
EXTENDS Naturals, Sequences

\* This module defines the actions of Votor.
\* All variables and constants are passed as parameters from the main module.

CONSTANTS Nodes, TotalStake, MaxSlots, Stake
VARIABLES finalized, leader, blocks, votes, notarized, fastFinalized, slowFinalized

RECURSIVE StakeOf(_)
StakeOf(S) == IF S = {} THEN 0 ELSE
    LET x == CHOOSE y \in S : TRUE IN
    Stake[x] + StakeOf(S \ {x})

\* Define the thresholds based on TotalStake
ThresholdFast == (TotalStake * 4) \div 5  \* 80% threshold
ThresholdSlow == (TotalStake * 3) \div 5  \* 60% threshold

CastNotarVote(s, n) ==
    /\ blocks[s] # "NULL"
    /\ votes[s][n] = "NULL"
    /\ votes' = [votes EXCEPT ![s][n] = blocks[s]]
    /\ UNCHANGED <<finalized, leader, blocks, notarized, fastFinalized, slowFinalized>>

FormNotarCert(s) ==
    /\ notarized[s] = "NULL"
    /\ LET BlockHash == blocks[s]
       IN LET Voters == {node \in Nodes : votes[s][node] = BlockHash}
          IN StakeOf(Voters) >= ThresholdSlow
    /\ notarized' = [notarized EXCEPT ![s] = blocks[s]]
    /\ UNCHANGED <<finalized, leader, blocks, votes, fastFinalized, slowFinalized>>

FormFastFinalCert(s) ==
    /\ fastFinalized[s] = "NULL"
    /\ LET BlockHash == blocks[s]
       IN LET Voters == {node \in Nodes : votes[s][node] = BlockHash}
          IN StakeOf(Voters) >= ThresholdFast
    /\ fastFinalized' = [fastFinalized EXCEPT ![s] = blocks[s]]
    /\ UNCHANGED <<finalized, leader, blocks, votes, notarized, slowFinalized>>

FormSlowFinalCert(s) ==
    /\ slowFinalized[s] = "NULL"
    /\ notarized[s] # "NULL"
    /\ LET NotarizedHash == notarized[s]
          Voters == {node \in Nodes : votes[s][node] = NotarizedHash}
       IN StakeOf(Voters) >= ThresholdSlow
    /\ slowFinalized' = [slowFinalized EXCEPT ![s] = notarized[s]]
    /\ UNCHANGED <<finalized, leader, blocks, votes, notarized, fastFinalized>>

UpdateFinalizedChain ==
    /\ \E s \in 1..MaxSlots :
        LET FinalBlockHash == IF fastFinalized[s] # "NULL" THEN fastFinalized[s] ELSE slowFinalized[s]
        IN /\ FinalBlockHash # "NULL"
           /\ \A i \in 1..Len(finalized) : finalized[i] # FinalBlockHash
           /\ finalized' = Append(finalized, FinalBlockHash)
    /\ UNCHANGED <<leader, blocks, votes, notarized, fastFinalized, slowFinalized>>

=============================================================================