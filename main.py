"""
Command-Line Interface and Interactive Demonstration for Holographic SAT Solver.
"""

import sys
import os
import argparse
import time
from cnf_formula import CNFFormula, Clause, Literal
from pcp_oracle import HolographicProof, formula_to_quadratic_system
from pcp_verifier import HolographicVerifier
from holographic_solver import HolographicSATSolver
from benchmarks import (
    generate_random_3sat, generate_n_queens_sat,
    generate_graph_coloring_sat, generate_pigeonhole_sat,
    run_scaling_benchmark
)


def print_banner():
    banner = r"""
================================================================================
   HOLOGRAPHIC SAT SOLVER & SEARCH-TO-DECISION REDUCTION ENGINE
   Based on: "P=NP in Polylogarithmic Time with Holographic Proofs
              and Search-to-Decision Reduction" (Aguilera Katayama, 2026)
================================================================================
    """
    print(banner)


def run_demo():
    print_banner()
    print("[*] Running Step-by-Step Educational Demo on a 3-SAT Formula...")

    # Define a 3-SAT formula on 4 variables
    # (x1 v x2 v ~x3) ^ (~x1 v x2 v x4) ^ (~x2 v ~x3 v ~x4) ^ (x1 v ~x2 v x3)
    f = CNFFormula([
        Clause.from_ints([1, 2, -3]),
        Clause.from_ints([-1, 2, 4]),
        Clause.from_ints([-2, -3, -4]),
        Clause.from_ints([1, -2, 3])
    ], num_vars=4)

    print("\n[+] Input Formula phi(x1, x2, x3, x4):")
    print(f)

    print("\n[+] Step 1: Arithmetization over GF(2)...")
    constraints, total_vars = formula_to_quadratic_system(f)
    print(f"    - Original variables: {f.num_vars}")
    print(f"    - Total arithmetized variables (including auxiliary): {total_vars}")
    print(f"    - Generated {len(constraints)} quadratic constraints over GF(2):")
    for i, c in enumerate(constraints[:6]):
        print(f"      Eq {i+1}: {c}")
    if len(constraints) > 6:
        print(f"      ... (+{len(constraints)-6} more equations)")

    print("\n[+] Step 2: Search-to-Decision Reduction with Holographic PCP Oracle...")
    solver = HolographicSATSolver(soundness_error=0.005)
    report = solver.solve(f)

    print("\n[+] Step-by-step Decision Query Trace:")
    for log in report.query_logs:
        val_str = f"x{log.var} = {int(log.tested_value)}"
        res_str = "SAT (Branch Confirmed)" if log.is_satisfiable else "UNSAT (Branch Pruned)"
        print(f"    Query [{val_str:<10}] -> {res_str:<25} | "
              f"Proof queries: {log.queries_to_proof:<3} | "
              f"Random bits: {log.random_bits:<4} | "
              f"Time: {log.duration_ms:.3f} ms")

    print("\n" + report.summary())

    print("\n[+] Step 3: Demonstrating Holographic Proof Verification Integrity...")
    if report.is_satisfiable and report.assignment:
        valid_proof = solver.generate_proof(f, report.assignment)
        v_res = solver.verify_proof(f, valid_proof)
        print(f"    - Valid Holographic Proof check: {v_res}")

        # Corrupt proof by flipping bits
        print("    - Testing Corrupted Proof detection:")
        corrupted_vec = list(valid_proof.assignment)
        corrupted_vec[0] ^= 1  # Corrupt witness
        bad_proof = HolographicProof(corrupted_vec, valid_proof.n)
        v_bad = solver.verify_proof(f, bad_proof)
        print(f"    - Corrupted Proof check: {v_bad} (Correctly Rejected: {not v_bad.is_valid})")


def run_n_queens(n: int):
    print_banner()
    print(f"[*] Encoding and Solving {n}-Queens Problem as SAT...")
    formula = generate_n_queens_sat(n)
    print(f"    - Variables: {formula.num_vars} ({n}x{n} chessboard)")
    print(f"    - Clauses: {formula.num_clauses}")

    solver = HolographicSATSolver()
    report = solver.solve(formula)
    print(report.summary())

    if report.is_satisfiable and report.assignment:
        print(f"\n[+] Solution Board ({n}x{n}):")
        for r in range(n):
            row_str = ""
            for c in range(n):
                var = r * n + c + 1
                row_str += " [Q] " if report.assignment.get(var, False) else "  .  "
            print(f"    {row_str}")


def run_dimacs_file(filepath: str):
    print_banner()
    if not os.path.exists(filepath):
        print(f"[-] File not found: {filepath}")
        return

    with open(filepath, 'r', encoding='utf-8', errors='ignore') as fh:
        content = fh.read()

    print(f"[*] Loading DIMACS file: {filepath}")
    formula = CNFFormula.from_dimacs_string(content)
    print(f"    - Variables: {formula.num_vars}")
    print(f"    - Clauses: {formula.num_clauses}")

    solver = HolographicSATSolver()
    report = solver.solve(formula)
    print(report.summary())


def main():
    parser = argparse.ArgumentParser(description="Holographic SAT Solver & Search-to-Decision Reduction Engine")
    parser.add_argument("--demo", action="store_true", help="Run interactive step-by-step demonstration")
    parser.add_argument("--benchmark", action="store_true", help="Run scaling complexity benchmark")
    parser.add_argument("--n-queens", type=int, metavar="N", help="Solve N-Queens SAT encoding")
    parser.add_argument("--dimacs", type=str, metavar="FILE", help="Solve DIMACS CNF file")

    if len(sys.argv) == 1:
        run_demo()
        return

    args = parser.parse_args()

    if args.demo:
        run_demo()
    elif args.benchmark:
        print_banner()
        print("[*] Running Scaling Complexity Benchmarks...")
        run_scaling_benchmark([4, 8, 12, 16, 20, 24, 28])
    elif args.n_queens:
        run_n_queens(args.n_queens)
    elif args.dimacs:
        run_dimacs_file(args.dimacs)


if __name__ == "__main__":
    main()
