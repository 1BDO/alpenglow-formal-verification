#!/usr/bin/env python3

import argparse
import random
import csv
import os
from collections import defaultdict
import numpy as np
from tqdm import trange

class Simulator:
    def __init__(self, num_nodes, byzantine_share, offline_share, rng_seed):
        self.num_nodes = num_nodes
        self.byzantine_share = byzantine_share
        self.offline_share = offline_share
        self.rng = random.Random(rng_seed)

        nodes = [f"N{i}" for i in range(self.num_nodes)]
        self.rng.shuffle(nodes)

        num_byzantine = int(self.num_nodes * self.byzantine_share)
        num_offline = int(self.num_nodes * self.offline_share)

        self.byzantine_nodes = set(nodes[:num_byzantine])
        self.offline_nodes = set(nodes[num_byzantine : num_byzantine + num_offline])
        self.honest_online_nodes = set(nodes[num_byzantine + num_offline :])

        self.total_stake = self.num_nodes
        self.stake_per_node = 1
        self.threshold_80 = 0.8 * self.total_stake
        self.threshold_60 = 0.6 * self.total_stake

    def run_slot(self):
        """Simulates a single slot and returns the outcome."""
        notar_voters = set()
        notar_voters.update(self.honest_online_nodes)
        notar_voters.update(self.byzantine_nodes)
        notar_stake = len(notar_voters) * self.stake_per_node

        if notar_stake >= self.threshold_80:
            latency = self.rng.gauss(mu=60, sigma=15)
            return "FAST_FINAL", max(30, latency)

        if notar_stake >= self.threshold_60:
            final_voters = self.honest_online_nodes.union(self.byzantine_nodes)
            final_stake = len(final_voters) * self.stake_per_node
            if final_stake >= self.threshold_60:
                latency = self.rng.gauss(mu=120, sigma=25)
                return "SLOW_FINAL", max(60, latency)

        return "SKIPPED", 200

    def save_results(self, results, latencies, output_dir):
        """Saves the simulation results to CSV files."""
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
        
        summary_path = os.path.join(output_dir, "simulation_summary.csv")
        with open(summary_path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["outcome", "count", "percentage"])
            total_runs = sum(results.values())
            for outcome, count in results.items():
                writer.writerow([outcome, count, f"{(count / total_runs):.2%}"])

        latency_path = os.path.join(output_dir, "simulation_latencies.csv")
        with open(latency_path, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["latency_ms"])
            for lat in latencies:
                writer.writerow([lat])
        
        print(f"\n--- Simulation Results ---")
        total_runs = sum(results.values())
        for outcome, count in results.items():
            print(f"{outcome}: {count}/{total_runs} ({(count / total_runs):.2%})")

        if latencies:
            print(f"Median Finalization Latency: {np.median(latencies):.2f} ms")
            print(f"95th Percentile Latency: {np.percentile(latencies, 95):.2f} ms")
        
        print(f"\nResults saved to '{output_dir}'")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Alpenglow Protocol Simulator.")
    parser.add_argument("--nodes", type=int, default=100, help="Total number of nodes.")
    parser.add_argument("--byzantine", type=float, default=0.20, help="Fraction of Byzantine nodes.")
    parser.add_argument("--offline", type=float, default=0.20, help="Fraction of offline nodes.")
    parser.add_argument("--runs", type=int, default=10000, help="Number of simulation runs.")
    parser.add_argument("--seed", type=int, default=42, help="Random seed.")
    parser.add_argument("--output", type=str, default="results", help="Directory to save results.")
    args = parser.parse_args()

    if args.byzantine + args.offline >= 0.4:
        print(f"Warning: Byzantine ({args.byzantine:.0%}) + Offline ({args.offline:.0%}) >= 40%. Protocol liveness may be compromised.")

    sim = Simulator(args.nodes, args.byzantine, args.offline, args.seed)
    
    all_results = defaultdict(int)
    all_latencies = []

    print(f"\n--- Starting Simulation ---")
    print(f"Nodes: {args.nodes}, Byzantine: {args.byzantine:.0%}, Offline: {args.offline:.0%}")
    print(f"Honest & Online Stake: {(1 - args.byzantine - args.offline):.0%}")

    for _ in trange(args.runs, desc="Simulating Slots"):
        outcome, latency = sim.run_slot()
        all_results[outcome] += 1
        if outcome != "SKIPPED":
            all_latencies.append(latency)

    sim.save_results(all_results, all_latencies, args.output)