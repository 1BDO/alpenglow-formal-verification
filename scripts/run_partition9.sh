#!/bin/bash
# This script runs Theorem 9: Network Partition Recovery verification
set -e

echo "--- Theorem 9: Network Partition Recovery ---"

# Ensure we're in the right directory and have results folder
mkdir -p results

echo "--- Running TLA+ Partition Recovery Verification ---"
cd specs/tla
java -jar /app/tla2tools.jar -workers auto -config PartitionRecovery.cfg PartitionRecovery.tla | tee ../../results/partition9_tlc.log

