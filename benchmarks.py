"""
Benchmark Generators and Empirical Complexity Scaling for Holographic SAT Solver.
Includes Random 3-SAT, N-Queens SAT, Graph 3-Coloring, and Pigeonhole formulas.
"""

from typing import List, Tuple, Dict
import random
import time
from cnf_formula import CNFFormula, Clause, Literal
from holographic_solver import HolographicSATSolver, SolveReport


def generate_random_3sat(num_vars: int, num_clauses: int, seed: int = 42) -> CNFFormula:
    """Generates a random 3-CNF formula over num_vars with num_clauses."""
    rng = random.Random(seed)
    clauses = []
    for _ in range(num_clauses):
        # Pick 3 distinct variables
        vars_selected = rng.sample(range(1, num_vars + 1), 3)
        lits = []
        for v in vars_selected:
            negated = (rng.randint(0, 1) == 1)
            lits.append(Literal(var=v, negated=negated))
        clauses.append(Clause(lits))
    return CNFFormula(clauses, num_vars=num_vars)


def generate_n_queens_sat(n: int) -> CNFFormula:
    """
    Encodes the N-Queens problem on an n x n board into CNF.
    Variable (r, c) is mapped to index r * n + c + 1.
    """
    def var_id(r: int, c: int) -> int:
        return r * n + c + 1

    clauses: List[Clause] = []

    # 1. At least one queen in each row
    for r in range(n):
        row_lits = [Literal(var_id(r, c)) for c in range(n)]
        clauses.append(Clause(row_lits))

    # 2. At most one queen in each row
    for r in range(n):
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append(Clause([Literal(var_id(r, c1), negated=True),
                                       Literal(var_id(r, c2), negated=True)]))

    # 3. At most one queen in each column
    for c in range(n):
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                clauses.append(Clause([Literal(var_id(r1, c), negated=True),
                                       Literal(var_id(r2, c), negated=True)]))

    # 4. At most one queen on each diagonal
    for r1 in range(n):
        for c1 in range(n):
            for r2 in range(r1 + 1, n):
                for c2 in range(n):
                    if abs(r1 - r2) == abs(c1 - c2):
                        clauses.append(Clause([Literal(var_id(r1, c1), negated=True),
                                               Literal(var_id(r2, c2), negated=True)]))

    return CNFFormula(clauses, num_vars=n * n)


def generate_graph_coloring_sat(num_vertices: int, edges: List[Tuple[int, int]], num_colors: int = 3) -> CNFFormula:
    """
    Encodes Graph Coloring into CNF.
    Variable for (vertex v, color c): v * num_colors + c + 1.
    """
    def var_id(v: int, c: int) -> int:
        return v * num_colors + c + 1

    clauses: List[Clause] = []

    # 1. Each vertex must have at least one color
    for v in range(num_vertices):
        clauses.append(Clause([Literal(var_id(v, c)) for c in range(num_colors)]))

    # 2. Each vertex has at most one color
    for v in range(num_vertices):
        for c1 in range(num_colors):
            for c2 in range(c1 + 1, num_colors):
                clauses.append(Clause([Literal(var_id(v, c1), negated=True),
                                       Literal(var_id(v, c2), negated=True)]))

    # 3. Adjacent vertices cannot share the same color
    for u, v in edges:
        for c in range(num_colors):
            clauses.append(Clause([Literal(var_id(u, c), negated=True),
                                   Literal(var_id(v, c), negated=True)]))

    return CNFFormula(clauses, num_vars=num_vertices * num_colors)


def generate_pigeonhole_sat(num_pigeons: int, num_holes: int) -> CNFFormula:
    """
    Encodes the Pigeonhole Principle PHP(pigeons, holes) into CNF.
    Unsatisfiable whenever num_pigeons > num_holes.
    Variable (p, h): p * num_holes + h + 1.
    """
    def var_id(p: int, h: int) -> int:
        return p * num_holes + h + 1

    clauses: List[Clause] = []

    # 1. Each pigeon must be in at least one hole
    for p in range(num_pigeons):
        clauses.append(Clause([Literal(var_id(p, h)) for h in range(num_holes)]))

    # 2. No two pigeons in the same hole
    for h in range(num_holes):
        for p1 in range(num_pigeons):
            for p2 in range(p1 + 1, num_pigeons):
                clauses.append(Clause([Literal(var_id(p1, h), negated=True),
                                       Literal(var_id(p2, h), negated=True)]))

    return CNFFormula(clauses, num_vars=num_pigeons * num_holes)


def run_scaling_benchmark(var_sizes: List[int] = [5, 10, 15, 20, 25, 30]) -> List[Dict]:
    """Runs scaling benchmark measuring time, random bits, and queries across formula sizes."""
    solver = HolographicSATSolver(soundness_error=0.01)
    results = []

    print("\n" + "=" * 80)
    print(f"{'n (vars)':<10}{'m (clauses)':<14}{'Queries':<12}{'Proof Bits':<14}{'Random Bits':<14}{'Time (ms)':<12}{'Status'}")
    print("=" * 80)

    for n in var_sizes:
        # Generate 3-SAT formula with clause-to-var ratio 3.5 (in satisfiable region)
        m = int(3.5 * n)
        formula = generate_random_3sat(num_vars=n, num_clauses=m, seed=100 + n)
        
        report = solver.solve(formula)
        status_str = "SAT" if report.is_satisfiable else "UNSAT"

        print(f"{report.num_vars:<10}{report.num_clauses:<14}{report.decision_queries:<12}"
              f"{report.total_proof_queries:<14}{report.total_random_bits:<14}"
              f"{report.total_time_ms:<12.3f}{status_str}")

        results.append({
            'n': report.num_vars,
            'm': report.num_clauses,
            'decision_queries': report.decision_queries,
            'proof_bits_read': report.total_proof_queries,
            'random_bits_sampled': report.total_random_bits,
            'total_time_ms': report.total_time_ms,
            'is_sat': report.is_satisfiable
        })

    print("=" * 80 + "\n")
    return results


if __name__ == "__main__":
    run_scaling_benchmark()
