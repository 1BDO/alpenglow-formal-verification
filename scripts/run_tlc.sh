#!/bin/bash
# Hardcoded path for maximum reliability
set -e

echo "--- Starting TLC Model Check ---"
mkdir -p results

# We know the JAR file is at /app/tla2tools.jar inside the container.
# We will use this absolute path to guarantee it is found.
java -jar /app/tla2tools.jar -workers auto -config specs/tla/Alpenglow.cfg specs/tla/Alpenglow.tla | tee results/tlc_output.log
