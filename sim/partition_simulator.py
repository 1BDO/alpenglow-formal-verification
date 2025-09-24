#!/usr/bin/env python3
"""
Network Partition Recovery Simulator for Alpenglow Protocol
Theorem 9: Network partition recovery guarantees
"""
import sys
import os
import argparse
import random
import csv
from collections import defaultdict
import numpy as np
from tqdm import trange

# Add the sim directory to path for reusing existing simulator
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../sim'))

class PartitionSimulator:
    def __init__(self, num_nodes, byzantine_share, offline_share, partition_share, rng_seed):
        self.num_nodes = num_nodes
        self.byzantine_share = byzantine_share
        self.offline_share = offline_share
        self.partition_share = partition_share
        self.rng = random.Random(rng_seed)

        nodes = [f"N{i}" for i in range(self.num_nodes)]
        self.rng.shuffle(nodes)

        num_byzantine = int(self.num_nodes * self.byzantine_share)
        num_offline = int(self.num_nodes * self.offline_share)
        num_partitioned = int(self.num_nodes * self.partition_share)

        self.byzantine_nodes = set(nodes[:num_byzantine])
        self.offline_nodes = set(nodes[num_byzantine:num_byzantine + num_offline])
        
        # Partitioned nodes are separate from byzantine/offline
        remaining_nodes = set(nodes[num_byzantine + num_offline:])
        self.partitioned_nodes = set(self.rng.sample(list(remaining_nodes), 
                                                   min(num_partitioned, len(remaining_nodes))))
        
        self.honest_online_nodes = remaining_nodes - self.partitioned_nodes

        self.total_stake = self.num_nodes
        self.stake_per_node = 1
        self.threshold_80 = 0.8 * self.total_stake
        self.threshold_60 = 0.6 * self.total_stake

    def get_available_stake(self, healed=False):
        """Calculate stake available for consensus"""
        available_nodes = self.honest_online_nodes.union(self.byzantine_nodes)
        if healed:
            available_nodes = available_nodes.union(self.partitioned_nodes)
        return len(available_nodes) * self.stake_per_node

    def run_partition_scenario(self, partition_duration_slots=5):
        """Simulate network partition and recovery"""
        results = []
        
        # Phase 1: Partition exists
        partition_phase_results = []
        for slot in range(partition_duration_slots):
            available_stake = self.get_available_stake(healed=False)
            
            if available_stake >= self.threshold_80:
                latency = self.rng.gauss(mu=80, sigma=20)
                partition_phase_results.append(("FAST_FINAL_PARTITION", max(40, latency)))
            elif available_stake >= self.threshold_60:
                latency = self.rng.gauss(mu=140, sigma=30)
                partition_phase_results.append(("SLOW_FINAL_PARTITION", max(80, latency)))
            else:
                partition_phase_results.append(("SKIPPED_PARTITION", 200))
        
        # Phase 2: Network heals
        heal_latency = self.rng.gauss(mu=50, sigma=15)  # Time to detect healing
        
        # Phase 3: First finalization after healing
        available_stake_healed = self.get_available_stake(healed=True)
        
        if available_stake_healed >= self.threshold_80:
            recovery_latency = self.rng.gauss(mu=60, sigma=15)
            recovery_outcome = "FAST_FINAL_RECOVERY"
        elif available_stake_healed >= self.threshold_60:
            recovery_latency = self.rng.gauss(mu=120, sigma=25)
            recovery_outcome = "SLOW_FINAL_RECOVERY"
        else:
            recovery_latency = 300
            recovery_outcome = "FAILED_RECOVERY"
        
        total_recovery_time = heal_latency + max(30, recovery_latency)
        
        return {
            'partition_phase': partition_phase_results,
            'recovery_outcome': recovery_outcome,
            'recovery_latency': total_recovery_time,
            'available_stake_during': self.get_available_stake(healed=False),
            'available_stake_after': available_stake_healed
        }

    def save_results(self, results, output_dir):
        """Save simulation results to CSV files"""
        # Ensure absolute path resolution
        if not os.path.isabs(output_dir):
            output_dir = os.path.abspath(output_dir)
        
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
            print(f"Created directory: {output_dir}")
        
        # Recovery statistics
        recovery_summary = defaultdict(int)
        recovery_latencies = []
        
        for result in results:
            recovery_summary[result['recovery_outcome']] += 1
            if result['recovery_outcome'] in ['FAST_FINAL_RECOVERY', 'SLOW_FINAL_RECOVERY']:
                recovery_latencies.append(result['recovery_latency'])
        
        # Save summary
        summary_path = os.path.join(output_dir, "partition_recovery_summary.csv")
        with open(summary_path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["outcome", "count", "percentage"])
            total_runs = len(results)
            for outcome, count in recovery_summary.items():
                writer.writerow([outcome, count, f"{(count / total_runs):.2%}"])
        
        print(f"Saved summary to: {summary_path}")
        
        # Save latencies
        latency_path = os.path.join(output_dir, "partition_recovery_latencies.csv")
        with open(latency_path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["recovery_latency_ms"])
            for lat in recovery_latencies:
                writer.writerow([lat])
        
        print(f"Saved latencies to: {latency_path}")
        
        print(f"\n--- Partition Recovery Simulation Results ---")
        total_runs = len(results)
        for outcome, count in recovery_summary.items():
            print(f"{outcome}: {count}/{total_runs} ({(count / total_runs):.2%})")
        
        if recovery_latencies:
            print(f"Median Recovery Latency: {np.median(recovery_latencies):.2f} ms")
            print(f"95th Percentile Recovery: {np.percentile(recovery_latencies, 95):.2f} ms")
        
        # Calculate success rate
        successful_recoveries = recovery_summary['FAST_FINAL_RECOVERY'] + recovery_summary['SLOW_FINAL_RECOVERY']
        success_rate = successful_recoveries / total_runs
        print(f"Recovery Success Rate: {success_rate:.2%}")
        
        print(f"\nResults saved to '{output_dir}'")

def main():
    parser = argparse.ArgumentParser(description="Alpenglow Partition Recovery Simulator")
    parser.add_argument("--nodes", type=int, default=100, help="Total number of nodes")
    parser.add_argument("--byzantine", type=float, default=0.15, help="Fraction of Byzantine nodes")
    parser.add_argument("--offline", type=float, default=0.15, help="Fraction of offline nodes")
    parser.add_argument("--partition", type=float, default=0.20, help="Fraction of partitioned nodes")
    parser.add_argument("--runs", type=int, default=1000, help="Number of simulation runs")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument("--output", type=str, default="results", help="Output directory")
    args = parser.parse_args()

    total_fault_share = args.byzantine + args.offline + args.partition
    if total_fault_share >= 0.5:
        print(f"Total fault share ({total_fault_share:.0%}) >= 50%.")

    sim = PartitionSimulator(args.nodes, args.byzantine, args.offline, args.partition, args.seed)
    
    results = []
    print(f"\n--- Starting Partition Recovery Simulation ---")
    print(f"Nodes: {args.nodes}, Byzantine: {args.byzantine:.0%}, Offline: {args.offline:.0%}, Partitioned: {args.partition:.0%}")
    
    for _ in trange(args.runs, desc="Simulating Partition Recovery"):
        result = sim.run_partition_scenario()
        results.append(result)

    sim.save_results(results, args.output)

if __name__ == "__main__":
    main()