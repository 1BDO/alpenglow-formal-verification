------------------------------ MODULE Alpenglow ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* =============================================================================
\* This is the main specification for the Alpenglow consensus protocol.
\* Self-contained version with constants defined inline
\* =============================================================================

\* Define constants directly in the spec
Nodes == {"n1", "n2", "n3", "n4"}
TotalStake == 100
MaxSlots == 3
Stake == [n \in Nodes |-> 25]  \* Each node has 25 stake

VARIABLES
    finalized,
    leader,
    blocks,
    votes,
    notarized,
    fastFinalized,
    slowFinalized

vars == << finalized, leader, blocks, votes, notarized, fastFinalized, slowFinalized >>

\* Import the actions from the sub-modules
INSTANCE Votor WITH Nodes <- Nodes, TotalStake <- TotalStake, MaxSlots <- MaxSlots, Stake <- Stake
INSTANCE Rotor

Init ==
    /\ finalized = <<>>
    /\ leader = [s \in 1..MaxSlots |-> CHOOSE n \in Nodes: TRUE]
    /\ blocks = [s \in 1..MaxSlots |-> "NULL"]
    /\ votes = [s \in 1..MaxSlots |-> [n \in Nodes |-> "NULL"]]
    /\ notarized = [s \in 1..MaxSlots |-> "NULL"]
    /\ fastFinalized = [s \in 1..MaxSlots |-> "NULL"]
    /\ slowFinalized = [s \in 1..MaxSlots |-> "NULL"]

Next ==
    \/ (\E s \in 1..MaxSlots:
        \/ ProposeBlock(s)
        \/ \E n \in Nodes: CastNotarVote(s, n)
        \/ FormNotarCert(s)
        \/ FormFastFinalCert(s)
        \/ FormSlowFinalCert(s)
       )
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

NoConflictingFinalizations ==
    \A s \in 1..MaxSlots:
        (fastFinalized[s] # "NULL" /\ slowFinalized[s] # "NULL") => (fastFinalized[s] = slowFinalized[s])

=============================================================================