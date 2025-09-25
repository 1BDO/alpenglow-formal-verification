# Makefile for the Alpenglow Formal Verification Suite

.PHONY: all verify check simulate partitionTLA clean

# Default command: run the full verification suite.
all: verify

# Main command to run all checks: TLA+ and Python simulation.
verify: check simulate
	@echo "\n✅ Full verification suite complete. All checks passed."
	@echo "Results are available in the 'results/' directory."

# Run only the TLA+ exhaustive model checks.
check:
	@echo "--- Running TLA+ Exhaustive Model Checks ---"
	@./scripts/run_tlc.sh
	@echo "--------------------------------------------"

# Run only the Python statistical simulation.
simulate:
	@echo "--- Running Python Statistical Simulation ---"
	@./scripts/run_simulator.sh
	@echo "-------------------------------------------"
	@echo "Running partition recovery simulation..." 
	@./scripts/run_partition_simulation.sh

partitionTLA: simulate
	@echo "--- Running Final Partition TLA+ Check ---"
	@bash ./scripts/run_partition9.sh
	@echo "-------------------------------------------"

verify-all: verify partitionTLA
	@echo "\n======================================================="
	@echo "Results are available in the 'results/' directory."
	@echo "======================================================="
	

# Clean up all generated artifacts.
clean:
	@echo "--- Cleaning up generated artifacts ---"
	@rm -rf results/*
	@rm -f sim/*.csv
	@echo "Cleanup complete."

