#!/usr/bin/env bash
set -e

echo "--- Preparing Python Environment for Partition Simulation ---"
python3 -m venv venv
source venv/bin/activate
pip install -r sim/requirements.txt

echo "--- Running Partition Recovery Simulator ---"
python3 sim/partition_simulator.py --nodes 100 --byzantine 0.15 --offline 0.15 --partition 0.20 --runs 1000 --output /app/results

