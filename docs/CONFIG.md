### **Configuring the Model**

The number of nodes is configured differently for the TLA+ model and the Python simulator, reflecting their different purposes.

#### **For the TLA+ Model (Small-Scale Proofs)**

To change the number of nodes for the exhaustive model check, you must **manually edit the configuration file**.

1.  Open `specs/tla/Alpenglow.tla`.
2.  Modify the `CONSTANTS` block. For example, to change from 4 to 6 nodes:

    **Before:**
    ```tla
    CONSTANTS
        Nodes = {"n1", "n2", "n3", "n4"}
        TotalStake = 100
        Stake == [n \in Nodes |-> 25]
    ```

    **After:**
    ```tla
    CONSTANTS
        Nodes = {"n1", "n2", "n3", "n4", "n5", "n6"}
        TotalStake = 100
        Stake == [n \in Nodes |-> 25]
    ```

#### **For the Python Simulator (Large-Scale Validation)**

To change the number of nodes for the statistical simulation, you use the `--nodes` **command-line argument**.

1.  Open the `scripts/run_simulator.sh` file.
2.  Change the value of the `--nodes` argument in the `python3` command at the bottom of the file.

    **Before (for 100 nodes):**
    ```bash
    python3 sim/sim_engine.py --nodes 100 --byzantine 0.20 --offline 0.20 --runs 10000 --output results
    ```

    **After (for 500 nodes):**
    ```bash
    python3 sim/sim_engine.py --nodes 500 --byzantine 0.20 --offline 0.20 --runs 10000 --output results
    ```
You can also change the `--byzantine` and `--offline` fractions to test different resilience scenarios.


## Network Partition Recovery Configuration

### Overview

Alpenglow protocol can recover from network partitions and resume consensus once connectivity is restored. The partition recovery model requires careful configuration to balance verification completeness with computational feasibility.

### TLA+ Model Configuration

The partition recovery model is more computationally intensive than the base consensus model due to additional state variables for partition tracking and recovery logic.

#### Basic Configuration

1. Open `specs/tla/PartitionRecovery.tla`
2. Locate the constants section at the top:

```tla
Nodes == {"n1", "n2", "n3", "n4"}
TotalStake == 100
MaxSlots == 3
Stake == [n \in Nodes |-> 25]
```

#### Memory-Optimized Settings (Recommended)

For reliable verification completion on standard hardware:

```tla
Nodes == {"n1", "n2", "n3", "n4"}
TotalStake == 100
MaxSlots == 2    \* Reduced to prevent memory exhaustion
Stake == [n \in Nodes |-> 25]
```

**Verification Stats:**
- Expected states: ~50,000 distinct states
- Memory usage: <2GB

#### Extended Network Configuration

For testing larger networks (use with caution):

```tla
Nodes == {"n1", "n2", "n3", "n4", "n5", "n6"}
TotalStake == 150
MaxSlots == 2    \* Must keep slots low for 6+ nodes
Stake == [n \in Nodes |-> 25]
```

**Warning:** 6 nodes with MaxSlots > 2 may exhaust available memory.

#### State Constraint (Emergency Memory Management)

If verification still runs out of memory, add this constraint:

```tla
\* Add this after the invariants section
StateConstraint == Len(finalized) <= 2
```

This limits the finalized chain length, reducing state space exploration.

### Configuration Trade-offs

| Configuration | States Explored | Memory Usage | 
|---------------|-----------------|--------------|
| 4 nodes, 2 slots | ~25K | <1GB | 
| 4 nodes, 3 slots | ~200K | 1-2GB | 
| 6 nodes, 2 slots | ~1M+ | 2-3GB | 
| 4 nodes, 5 slots | 60M+ | >4GB | 

### Understanding Partition Parameters

The partition recovery model introduces these key variables:

```tla
VARIABLES
    partitioned,     \* Set of nodes that are network-partitioned
    networkHealed,   \* Boolean indicating if partition is resolved
    partitionStart   \* Slot when partition began
```

**Initial Partition Setup:**
```tla
\* In Init predicate
partitioned = CHOOSE S \subseteq Nodes : StakeOf(S) <= (TotalStake \div 3)
```

This creates a partition affecting ≤33% of total stake, ensuring the remaining network can still make progress.

### Python Simulator Configuration

The partition recovery simulator can handle much larger networks efficiently:

#### Standard Partition Recovery Test

```bash
python3 sim/partition_simulator.py \
  --nodes 100 \
  --byzantine 0.15 \
  --offline 0.15 \
  --partition 0.20 \
  --runs 1000 \
  --output results
```

#### Large-Scale Partition Test

```bash
python3 sim/partition_simulator.py \
  --nodes 500 \
  --byzantine 0.10 \
  --offline 0.10 \
  --partition 0.25 \
  --runs 2000 \
  --output results
```

### Parameter Guidelines

**Fault Distribution Rules:**
- Total faults should not exceed 50%: `byzantine + offline + partition ≤ 0.5`
- For partition testing, reduce byzantine/offline to isolate network connectivity effects
- Partition percentage can be higher than byzantine/offline since it's temporary

**Example Valid Configurations:**
- Conservative: 10% Byzantine + 10% Offline + 20% Partitioned = 40% total
- Aggressive: 15% Byzantine + 15% Offline + 20% Partitioned = 50% total
- Stress test: 5% Byzantine + 5% Offline + 30% Partitioned = 40% total


