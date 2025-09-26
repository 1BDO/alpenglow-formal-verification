
# Alpenglow Formal Verification 

Comprehensive formal verification of Solana's Alpenglow consensus protocol using TLA+ and statistical simulation.

⚠️ **Note:** Clean the `results/` directory before running.

### Watch the project [demo](#https://www.loom.com/share/a0827a2ed4f04c3c899498036cff6598?sid=54ee78e1-e3e1-4c3e-8b2c-5f8332566588) tutorial video. 

## Quick Start

### 1. Clone the repository

```bash
git clone https://github.com/1BDO/alpenglow-formal-verification.git
````
````
cd alpenglow-formal-verification
````
### 2. Check Out `docs/HOW_TO_RUN.md`:

This entire project is reproducible. The recommended method is to use the provided `Makefile`, which leverages Docker to ensure a consistent environment.

---

## Documentation

* **[Technical Report](docs/TECHNICAL_REPORT.md)**: Complete verification methodology and results
* **[How to Run](docs/HOW_TO_RUN.md)**: Detailed usage instructions and configuration
* **[Verification Status](docs/VERIFICATION.md)**: Theorem-by-theorem verification mapping
* **[Configuration Guide](docs/CONFIG.md)**: Parameter customization and scaling

---

## Results

All verification results are saved to `results/`:

* `tlc_output.log` — TLA+ model checking results
* `simulation_summary.csv` — Statistical simulation outcomes
* `simulation_latencies.csv` — Latency measurements
* `partition_recovery_summary.csv` — Partition recovery results
* `partition9_tlc.log` — Partition recovery TLA+ verification

---

## Project Structure

```
alpenglow-formal-verification/
├── docs/                      # Documentation
│   ├── CONFIG.md              # Configuration guide
│   ├── HOW_TO_RUN.md          # Detailed usage instructions
│   ├── TECHNICAL_REPORT.md    # Complete verification results
│   └── VERIFICATION.md        # Theorem-by-theorem verification status
├── specs/tla/                 # TLA+ formal specifications
│   ├── Alpenglow.tla          # Main protocol specification
│   ├── Alpenglow.cfg          # TLA+ configuration
│   ├── Votor.tla              # Dual-path voting logic
│   ├── Rotor.tla              # Block propagation model
│   ├── PartitionRecovery.tla  # Network partition recovery 
│   └── PartitionRecovery.cfg  # Partition recovery configuration
├── sim/                       # Statistical simulation
│   ├── sim_engine.py          # Main Alpenglow simulator
│   ├── partition_simulator.py # Partition recovery simulator
│   └── requirements.txt       # Python dependencies
├── scripts/                   # Automation scripts
├── tools/                     # Docker and build configuration
└── results/                   # Verification outputs (generated)
```

---

## Contributing

This is a formal verification research project. Contributions should focus on:

* Enhanced TLA+ specifications
* Additional property verification
* Simulation model improvements
* Documentation and reproducibility
