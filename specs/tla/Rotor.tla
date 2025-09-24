-------------------------------- MODULE Rotor --------------------------------
EXTENDS Naturals, Sequences, TLC

\* This module provides a simplified, abstract model of the Rotor component.
\* All variables are passed as parameters from the main module.

VARIABLES finalized, leader, blocks, votes, notarized, fastFinalized, slowFinalized

ProposeBlock(s) ==
    /\ blocks[s] = "NULL"
    /\ blocks' = [blocks EXCEPT ![s] = "Block_" \o ToString(s)]
    /\ UNCHANGED <<finalized, leader, votes, notarized, fastFinalized, slowFinalized>>

=============================================================================