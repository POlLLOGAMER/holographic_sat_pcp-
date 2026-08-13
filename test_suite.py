"""
Comprehensive Automated Unit & Integration Tests for Holographic SAT Solver.
"""

import unittest
from cnf_formula import CNFFormula, Clause, Literal
from pcp_oracle import HolographicProof, formula_to_quadratic_system, MerkleWitnessCommitment
from pcp_verifier import HolographicVerifier
from search_to_decision import SearchToDecisionReducer
from holographic_solver import HolographicSATSolver
from benchmarks import generate_random_3sat, generate_n_queens_sat, generate_graph_coloring_sat, generate_pigeonhole_sat


class TestCNFFormula(unittest.TestCase):
    def test_literal_and_clause_evaluation(self):
        c = Clause.from_ints([1, -2, 3])
        # Case 1: x1 = True -> Satisfied
        self.assertTrue(c.is_satisfied({1: True, 2: True, 3: False}))
        # Case 2: x2 = False (negated is True) -> Satisfied
        self.assertTrue(c.is_satisfied({1: False, 2: False, 3: False}))
        # Case 3: All false -> Falsified
        self.assertFalse(c.is_satisfied({1: False, 2: True, 3: False}))

    def test_restriction(self):
        f = CNFFormula([
            Clause.from_ints([1, 2]),
            Clause.from_ints([-1, 3]),
            Clause.from_ints([2, -3])
        ], num_vars=3)
        # Restrict x1 = True: clause 1 is satisfied (dropped), clause 2 becomes (3)
        f_res = f.restrict(1, True)
        self.assertEqual(len(f_res.clauses), 2)
        self.assertIn(Clause.from_ints([3]), f_res.clauses)
        self.assertIn(Clause.from_ints([2, -3]), f_res.clauses)

    def test_to_3sat_conversion(self):
        # 4-clause: (1 v 2 v 3 v 4) -> (1 v 2 v y1) ^ (not y1 v 3 v 4)
        f = CNFFormula([Clause.from_ints([1, 2, 3, 4])], num_vars=4)
        f3 = f.to_3sat()
        self.assertEqual(f3.num_clauses, 2)
        for c in f3.clauses:
            self.assertEqual(len(c), 3)

    def test_dimacs_roundtrip(self):
        dimacs_text = """
        c Sample DIMACS comment
        p cnf 3 2
        1 -2 3 0
        -1 2 0
        """
        f = CNFFormula.from_dimacs_string(dimacs_text)
        self.assertEqual(f.num_vars, 3)
        self.assertEqual(f.num_clauses, 2)


class TestHolographicProofAndVerifier(unittest.TestCase):
    def setUp(self):
        self.verifier = HolographicVerifier(sound_error_delta=0.01, seed=42)

    def test_walsh_hadamard_linear_query(self):
        # Assignment: x1=1, x2=0, x3=1
        proof = HolographicProof([1, 0, 1], n=3)
        # A((1, 0, 0)) = 1*1 + 0*0 + 0*1 = 1
        self.assertEqual(proof.query_A([1, 0, 0]), 1)
        # A((0, 1, 0)) = 0
        self.assertEqual(proof.query_A([0, 1, 0]), 0)
        # A((1, 1, 1)) = 1 + 0 + 1 = 0 mod 2
        self.assertEqual(proof.query_A([1, 1, 1]), 0)

    def test_blr_linearity_test_pass(self):
        proof = HolographicProof([1, 1, 0, 1], n=4)
        passed, queries, bits = self.verifier.test_linearity_A(proof, num_trials=20)
        self.assertTrue(passed)
        self.assertEqual(queries, 60)

    def test_multiplication_consistency_test(self):
        proof = HolographicProof([1, 0, 1, 1], n=4)
        passed, queries, bits = self.verifier.test_multiplication_consistency(proof, num_trials=15)
        self.assertTrue(passed)

    def test_clause_satisfaction_test(self):
        # Formula: (x1 v x2) ^ (not x1 v x2) -> satisfied by x2=1, x1=0
        f = CNFFormula([Clause.from_ints([1, 2]), Clause.from_ints([-1, 2])], num_vars=2)
        proof = HolographicProof.create_for_formula(f, {1: False, 2: True})
        v_res = self.verifier.verify(f, proof)
        self.assertTrue(v_res.is_valid)

    def test_corrupted_proof_rejection(self):
        f = CNFFormula([Clause.from_ints([1, 2]), Clause.from_ints([-1, 2])], num_vars=2)
        # Unsatisfying assignment: x1=1, x2=0 (falsifies second clause)
        bad_proof = HolographicProof.create_for_formula(f, {1: True, 2: False})
        v_res = self.verifier.verify(f, bad_proof)
        self.assertFalse(v_res.is_valid)

    def test_merkle_polynomial_commitment(self):
        witness = [1, 0, 1, 1, 0, 1, 0, 0]
        tree = MerkleWitnessCommitment(witness)
        root = tree.root
        self.assertTrue(len(root) == 32)
        # Verify opening for each leaf
        for i, val in enumerate(witness):
            path = tree.get_auth_path(i)
            self.assertTrue(MerkleWitnessCommitment.verify_auth_path(root, i, val, path))
            # Test corrupted leaf bit rejected
            self.assertFalse(MerkleWitnessCommitment.verify_auth_path(root, i, val ^ 1, path))


class TestSearchToDecisionAndSolver(unittest.TestCase):
    def setUp(self):
        self.solver = HolographicSATSolver(soundness_error=0.01)

    def test_solve_simple_satisfiable(self):
        f = CNFFormula([
            Clause.from_ints([1, 2, -3]),
            Clause.from_ints([-1, 2]),
            Clause.from_ints([3])
        ], num_vars=3)
        report = self.solver.solve(f)
        self.assertTrue(report.is_satisfiable)
        self.assertIsNotNone(report.assignment)
        self.assertTrue(f.is_satisfied(report.assignment))

    def test_solve_simple_unsatisfiable(self):
        # (x1) ^ (not x1)
        f = CNFFormula([
            Clause.from_ints([1]),
            Clause.from_ints([-1])
        ], num_vars=1)
        report = self.solver.solve(f)
        self.assertFalse(report.is_satisfiable)
        self.assertIsNone(report.assignment)

    def test_solve_n_queens_4(self):
        f = generate_n_queens_sat(4)
        report = self.solver.solve(f)
        self.assertTrue(report.is_satisfiable)
        self.assertTrue(f.is_satisfied(report.assignment))

    def test_solve_pigeonhole_unsat(self):
        # 3 pigeons into 2 holes -> UNSAT
        f = generate_pigeonhole_sat(num_pigeons=3, num_holes=2)
        report = self.solver.solve(f)
        self.assertFalse(report.is_satisfiable)

    def test_solve_graph_coloring(self):
        # Triangle graph with 3 colors -> SAT
        edges = [(0, 1), (1, 2), (2, 0)]
        f = generate_graph_coloring_sat(num_vertices=3, edges=edges, num_colors=3)
        report = self.solver.solve(f)
        self.assertTrue(report.is_satisfiable)
        self.assertTrue(f.is_satisfied(report.assignment))


if __name__ == "__main__":
    unittest.main()
