#!/bin/bash
# This script runs the Python statistical simulator for Alpenglow.
set -e

echo "--- Preparing Python Environment ---"
python3 -m venv venv
source venv/bin/activate
pip install -r sim/requirements.txt

echo "--- Running Simulator (100 nodes, 20% Byzantine, 20% Offline) ---"
python3 sim/sim_engine.py --nodes 100 --byzantine 0.20 --offline 0.20 --runs 10000 --output results