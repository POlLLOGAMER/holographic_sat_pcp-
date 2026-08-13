"""
Search-to-Decision Reduction for SAT (Schnorr-Sipser-Balcazar self-reducibility).
Narrows down variable assignments by querying the Holographic Proof Decision Oracle.
"""

from typing import Dict, List, Optional, Tuple, Callable
import time
from cnf_formula import CNFFormula
from pcp_oracle import HolographicProof
from pcp_verifier import HolographicVerifier, VerificationResult


class DecisionOracleQueryLog:
    """Logs details of a single query made by the search-to-decision reduction."""
    __slots__ = (
        'step', 'var', 'tested_value', 'is_satisfiable',
        'verification_result', 'duration_ms', 'random_bits', 'queries_to_proof'
    )

    def __init__(self, step: int, var: int, tested_value: bool,
                 is_satisfiable: bool, verification_result: Optional[VerificationResult],
                 duration_ms: float, random_bits: int, queries_to_proof: int):
        self.step = step
        self.var = var
        self.tested_value = tested_value
        self.is_satisfiable = is_satisfiable
        self.verification_result = verification_result
        self.duration_ms = duration_ms
        self.random_bits = random_bits
        self.queries_to_proof = queries_to_proof

    def __repr__(self) -> str:
        res_str = "SAT" if self.is_satisfiable else "UNSAT"
        return (f"Step {self.step}: Query phi|(x{self.var}={int(self.tested_value)}) -> {res_str} "
                f"[{self.queries_to_proof} proof queries, {self.random_bits} bits, {self.duration_ms:.3f}ms]")


class SearchToDecisionReducer:
    """
    Executes the Search-to-Decision Reduction on a CNF formula.
    Integrates with the Holographic Proof Verifier to evaluate decision oracle queries.
    """

    def __init__(self, verifier: Optional[HolographicVerifier] = None):
        self.verifier = verifier or HolographicVerifier(sound_error_delta=0.01)
        self.query_logs: List[DecisionOracleQueryLog] = []

    def reduce(self, formula: CNFFormula,
               proof_provider: Optional[Callable[[CNFFormula], Optional[HolographicProof]]] = None
               ) -> Tuple[Optional[Dict[int, bool]], List[DecisionOracleQueryLog]]:
        self.query_logs.clear()
        n = formula.num_vars
        current_formula = formula
        assignment: Dict[int, bool] = {}

        if current_formula.is_empty():
            return {i: False for i in range(1, n + 1)}, self.query_logs
        if current_formula.has_empty_clause():
            return None, self.query_logs

        step_counter = 0

        for var in range(1, n + 1):
            step_counter += 1
            start_time = time.perf_counter()

            # 1. Try branch x_var = 1
            f_true = current_formula.restrict(var, True)
            is_true_sat, v_res_true = self._query_decision_oracle(f_true, proof_provider)

            dur = (time.perf_counter() - start_time) * 1000.0
            q_count = v_res_true.queries_used if v_res_true else 0
            r_bits = v_res_true.random_bits_used if v_res_true else 0

            log_entry = DecisionOracleQueryLog(
                step=step_counter, var=var, tested_value=True,
                is_satisfiable=is_true_sat, verification_result=v_res_true,
                duration_ms=dur, random_bits=r_bits, queries_to_proof=q_count
            )
            self.query_logs.append(log_entry)

            if is_true_sat:
                assignment[var] = True
                current_formula = f_true
            else:
                # 2. Try branch x_var = 0
                step_counter += 1
                start_time0 = time.perf_counter()
                f_false = current_formula.restrict(var, False)
                is_false_sat, v_res_false = self._query_decision_oracle(f_false, proof_provider)

                dur0 = (time.perf_counter() - start_time0) * 1000.0
                q_count0 = v_res_false.queries_used if v_res_false else 0
                r_bits0 = v_res_false.random_bits_used if v_res_false else 0

                log_entry0 = DecisionOracleQueryLog(
                    step=step_counter, var=var, tested_value=False,
                    is_satisfiable=is_false_sat, verification_result=v_res_false,
                    duration_ms=dur0, random_bits=r_bits0, queries_to_proof=q_count0
                )
                self.query_logs.append(log_entry0)

                if is_false_sat:
                    assignment[var] = False
                    current_formula = f_false
                else:
                    return None, self.query_logs

            if current_formula.is_empty():
                for remaining_var in range(var + 1, n + 1):
                    if remaining_var not in assignment:
                        assignment[remaining_var] = False
                break

        if formula.is_satisfied(assignment):
            return assignment, self.query_logs
        else:
            return None, self.query_logs

    def _query_decision_oracle(self, sub_formula: CNFFormula,
                               proof_provider: Optional[Callable[[CNFFormula], Optional[HolographicProof]]]
                               ) -> Tuple[bool, Optional[VerificationResult]]:
        if sub_formula.has_empty_clause():
            return False, None
        if sub_formula.is_empty():
            return True, None

        if proof_provider is not None:
            proof = proof_provider(sub_formula)
            if proof is None:
                return False, None
            v_res = self.verifier.verify(sub_formula, proof)
            return v_res.is_valid, v_res
        else:
            is_sat = self._deterministic_dpll_check(sub_formula)
            return is_sat, None

    def _deterministic_dpll_check(self, formula: CNFFormula) -> bool:
        if formula.is_empty():
            return True
        if formula.has_empty_clause():
            return False

        for c in formula.clauses:
            if len(c) == 1:
                lit = c.literals[0]
                val = not lit.negated
                return self._deterministic_dpll_check(formula.restrict(lit.var, val))

        var = formula.clauses[0].literals[0].var
        return (self._deterministic_dpll_check(formula.restrict(var, True)) or
                self._deterministic_dpll_check(formula.restrict(var, False)))
