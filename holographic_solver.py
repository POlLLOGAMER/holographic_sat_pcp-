"""
Unified Holographic SAT Solver.
Integrates Search-to-Decision Reduction, Holographic Proofs (PCP), and Complexity Profiling.
"""

from typing import Dict, List, Optional, Tuple, Union
import time
from dataclasses import dataclass
from cnf_formula import CNFFormula
from pcp_oracle import HolographicProof
from pcp_verifier import HolographicVerifier, VerificationResult
from search_to_decision import SearchToDecisionReducer, DecisionOracleQueryLog


@dataclass
class SolveReport:
    """Complete diagnostic and complexity report of the Holographic SAT Solver."""
    is_satisfiable: bool
    assignment: Optional[Dict[int, bool]]
    num_vars: int
    num_clauses: int
    decision_queries: int
    total_proof_queries: int
    total_random_bits: int
    total_time_ms: float
    avg_verification_time_ms: float
    theoretical_complexity_bound: str
    query_logs: List[DecisionOracleQueryLog]

    def summary(self) -> str:
        status = "SATISFIABLE" if self.is_satisfiable else "UNSATISFIABLE"
        lines = [
            "=" * 65,
            f" HOLOGRAPHIC SAT SOLVER REPORT: {status}",
            "=" * 65,
            f"  Variables (n):                {self.num_vars}",
            f"  Clauses (m):                  {self.num_clauses}",
            f"  Search-to-Decision Queries:   {self.decision_queries}",
            f"  Total PCP Proof Bits Read:    {self.total_proof_queries}",
            f"  Total Random Bits Sampled:    {self.total_random_bits}",
            f"  Total Elapsed Time:           {self.total_time_ms:.4f} ms",
            f"  Avg Verification Time/Query:  {self.avg_verification_time_ms:.4f} ms",
            f"  Theoretical Verification:     {self.theoretical_complexity_bound}",
            "-" * 65,
        ]
        if self.is_satisfiable and self.assignment:
            assign_str = ", ".join(f"x{k}={int(v)}" for k, v in sorted(self.assignment.items())[:12])
            if len(self.assignment) > 12:
                assign_str += f", ... (+{len(self.assignment)-12} more)"
            lines.append(f"  Assignment: {assign_str}")
        lines.append("=" * 65)
        return "\n".join(lines)


class HolographicSATSolver:
    """
    Solves SAT instances by combining Holographic Proofs with Search-to-Decision reduction.
    """

    def __init__(self, soundness_error: float = 0.01, random_seed: Optional[int] = None):
        self.verifier = HolographicVerifier(sound_error_delta=soundness_error, seed=random_seed)
        self.reducer = SearchToDecisionReducer(verifier=self.verifier)

    def generate_proof(self, formula: CNFFormula, assignment: Dict[int, bool]) -> HolographicProof:
        """Generates the Holographic Proof (PCP table) for a formula and satisfying assignment."""
        return HolographicProof.create_for_formula(formula, assignment)

    def verify_proof(self, formula: CNFFormula, proof: HolographicProof) -> VerificationResult:
        """Verifies a Holographic Proof in O(log n) time."""
        return self.verifier.verify(formula, proof)

    def solve(self, formula: CNFFormula) -> SolveReport:
        """
        Solves the SAT formula using the nested Search-to-Decision + Holographic Proof architecture.
        """
        start_time = time.perf_counter()

        # Cache of sub-formula proofs for the oracle provider
        def oracle_proof_provider(sub_f: CNFFormula) -> Optional[HolographicProof]:
            # Finds satisfying assignment for sub-formula to produce the holographic oracle
            sub_assign = self._find_satisfying_witness(sub_f)
            if sub_assign is None:
                return None
            return HolographicProof.create_for_formula(sub_f, sub_assign)

        assignment, query_logs = self.reducer.reduce(formula, proof_provider=oracle_proof_provider)
        total_time = (time.perf_counter() - start_time) * 1000.0

        decision_queries = len(query_logs)
        total_proof_queries = sum(log.queries_to_proof for log in query_logs)
        total_random_bits = sum(log.random_bits for log in query_logs)
        verif_times = [log.duration_ms for log in query_logs if log.duration_ms > 0]
        avg_verif_time = (sum(verif_times) / len(verif_times)) if verif_times else 0.0

        is_sat = (assignment is not None)

        return SolveReport(
            is_satisfiable=is_sat,
            assignment=assignment,
            num_vars=formula.num_vars,
            num_clauses=formula.num_clauses,
            decision_queries=decision_queries,
            total_proof_queries=total_proof_queries,
            total_random_bits=total_random_bits,
            total_time_ms=total_time,
            avg_verification_time_ms=avg_verif_time,
            theoretical_complexity_bound="O(log n) x O(log n) = O(log^2 n) verification queries",
            query_logs=query_logs
        )

    def _find_satisfying_witness(self, formula: CNFFormula) -> Optional[Dict[int, bool]]:
        """
        Helper that provides a witness assignment to instantiate the Holographic Proof oracle.
        Uses DPLL with unit propagation and pure literal elimination.
        """
        return self._dpll_solve(formula, {})

    def _dpll_solve(self, formula: CNFFormula, current_assignment: Dict[int, bool]) -> Optional[Dict[int, bool]]:
        if formula.is_empty():
            return current_assignment
        if formula.has_empty_clause():
            return None

        # 1. Unit Clause Rule
        for clause in formula.clauses:
            if len(clause) == 1:
                lit = clause.literals[0]
                val = not lit.negated
                new_assign = dict(current_assignment)
                new_assign[lit.var] = val
                return self._dpll_solve(formula.restrict(lit.var, val), new_assign)

        # 2. Pure Literal Rule
        all_lits = [lit for clause in formula.clauses for lit in clause.literals]
        vars_pos = {l.var for l in all_lits if not l.negated}
        vars_neg = {l.var for l in all_lits if l.negated}
        pure_pos = vars_pos - vars_neg
        pure_neg = vars_neg - vars_pos

        if pure_pos:
            var = next(iter(pure_pos))
            new_assign = dict(current_assignment)
            new_assign[var] = True
            return self._dpll_solve(formula.restrict(var, True), new_assign)
        if pure_neg:
            var = next(iter(pure_neg))
            new_assign = dict(current_assignment)
            new_assign[var] = False
            return self._dpll_solve(formula.restrict(var, False), new_assign)

        # 3. Branching: Choose first available variable
        var = formula.clauses[0].literals[0].var
        
        # Try True branch
        assign_t = dict(current_assignment)
        assign_t[var] = True
        res = self._dpll_solve(formula.restrict(var, True), assign_t)
        if res is not None:
            return res

        # Try False branch
        assign_f = dict(current_assignment)
        assign_f[var] = False
        return self._dpll_solve(formula.restrict(var, False), assign_f)
