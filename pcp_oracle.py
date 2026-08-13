"""
Implicit Holographic Proof / PCP Generator and Polynomial Commitment Oracle over GF(2).
Computes Walsh-Hadamard and Quadratic evaluations on-the-fly without constructing
explicit 2^n tables in RAM (O(n) witness storage, O(1) query auxiliary memory).
Integrates Merkle Tree / Polynomial Commitments for cryptographic binding.
"""

from typing import List, Dict, Tuple, Optional, Callable, Union
import random
import hashlib
from cnf_formula import CNFFormula, Clause, Literal


class MerkleWitnessCommitment:
    """
    Cryptographic Merkle Tree Commitment over the witness bitstring.
    Provides O(log n) authentication paths for local verification.
    """

    def __init__(self, bit_array: List[int]):
        self.leaves = [hashlib.sha256(f"leaf:{i}:{b}".encode()).digest() for i, b in enumerate(bit_array)]
        if not self.leaves:
            self.leaves = [hashlib.sha256(b"empty").digest()]
        # Pad leaves to power of 2
        n_leaves = len(self.leaves)
        power_of_2 = 1
        while power_of_2 < n_leaves:
            power_of_2 <<= 1
        self.padded_leaves = list(self.leaves)
        pad_hash = hashlib.sha256(b"pad").digest()
        while len(self.padded_leaves) < power_of_2:
            self.padded_leaves.append(pad_hash)

        # Build tree levels
        self.tree = [self.padded_leaves]
        while len(self.tree[-1]) > 1:
            curr = self.tree[-1]
            next_lvl = []
            for i in range(0, len(curr), 2):
                h = hashlib.sha256(curr[i] + curr[i + 1]).digest()
                next_lvl.append(h)
            self.tree.append(next_lvl)

    @property
    def root(self) -> bytes:
        return self.tree[-1][0]

    @property
    def root_hex(self) -> str:
        return self.root.hex()

    def get_auth_path(self, leaf_idx: int) -> List[Tuple[bytes, bool]]:
        """Returns authentication path: [(sibling_hash, is_sibling_right), ...]"""
        path = []
        idx = leaf_idx
        for level in self.tree[:-1]:
            is_right = (idx % 2 == 0)
            sibling_idx = idx + 1 if is_right else idx - 1
            path.append((level[sibling_idx], is_right))
            idx //= 2
        return path

    @staticmethod
    def verify_auth_path(root: bytes, leaf_idx: int, bit: int, path: List[Tuple[bytes, bool]]) -> bool:
        curr = hashlib.sha256(f"leaf:{leaf_idx}:{bit}".encode()).digest()
        for sibling, is_sibling_right in path:
            if is_sibling_right:
                curr = hashlib.sha256(curr + sibling).digest()
            else:
                curr = hashlib.sha256(sibling + curr).digest()
        return curr == root


class QuadraticConstraint:
    """
    Represents an equation over GF(2):
    x^T M x + c^T x + d = 0 (mod 2)
    Evaluated implicitly without materializing full dense matrices.
    """
    __slots__ = ('M_terms', 'c_terms', 'd', 'n')

    def __init__(self, n: int, M_terms: Optional[Dict[Tuple[int, int], int]] = None,
                 c_terms: Optional[Dict[int, int]] = None, d: int = 0):
        self.n = n
        self.M_terms: Dict[Tuple[int, int], int] = {k: v % 2 for k, v in (M_terms or {}).items() if v % 2 != 0}
        self.c_terms: Dict[int, int] = {k: v % 2 for k, v in (c_terms or {}).items() if v % 2 != 0}
        self.d: int = d % 2

    def evaluate(self, x: List[int]) -> int:
        val = self.d
        for i, c in self.c_terms.items():
            if c and i < len(x) and x[i]:
                val ^= 1
        for (i, j), m in self.M_terms.items():
            if m and i < len(x) and j < len(x) and x[i] and x[j]:
                val ^= 1
        return val % 2

    def __repr__(self) -> str:
        terms = []
        for (i, j) in sorted(self.M_terms.keys()):
            terms.append(f"x{i+1}*x{j+1}")
        for i in sorted(self.c_terms.keys()):
            terms.append(f"x{i+1}")
        if self.d:
            terms.append("1")
        expr = " + ".join(terms) if terms else "0"
        return f"({expr} = 0 mod 2)"


class HolographicProof:
    """
    Implicit Holographic Proof / Multilinear Polynomial Oracle for SAT.
    Does NOT construct or allocate 2^n memory in RAM.
    Evaluates queries on-the-fly using the compact witness (O(n) witness storage).
    """

    def __init__(self, assignment_vec: List[int], n: int):
        self.n = n
        self.assignment = [int(v) % 2 for v in assignment_vec]
        if len(self.assignment) < n:
            self.assignment.extend([0] * (n - len(self.assignment)))
        self.assignment = self.assignment[:n]
        self.query_count = 0
        self._commitment: Optional[MerkleWitnessCommitment] = None

    @property
    def commitment(self) -> MerkleWitnessCommitment:
        if self._commitment is None:
            self._commitment = MerkleWitnessCommitment(self.assignment)
        return self._commitment

    @property
    def commitment_root(self) -> str:
        return self.commitment.root_hex

    @classmethod
    def from_dict(cls, assignment: Dict[int, bool], n: int) -> 'HolographicProof':
        vec = [1 if assignment.get(i, False) else 0 for i in range(1, n + 1)]
        return cls(vec, n)

    @classmethod
    def create_for_formula(cls, formula: CNFFormula, assignment: Dict[int, bool]) -> 'HolographicProof':
        f3, extend_to_3sat = formula.to_3sat_and_extension()
        ext_assign = extend_to_3sat(assignment)

        constraints, total_vars, aux_calculators = formula_to_quadratic_system_with_calc(f3)
        full_vec = [0] * total_vars
        
        # 1. Fill base and 3-SAT auxiliary variables
        for i in range(1, f3.num_vars + 1):
            if ext_assign.get(i, False):
                full_vec[i - 1] = 1

        # 2. Compute quadratic arithmetization auxiliary variables on-the-fly
        for aux_idx, func in aux_calculators:
            full_vec[aux_idx] = func(full_vec)

        return cls(full_vec, total_vars)

    def query_A(self, u: Union[List[int], Tuple[int, ...]]) -> int:
        """
        Implicit on-the-fly evaluation: A(u) = <u, a> mod 2.
        Memory: O(1) auxiliary space.
        """
        self.query_count += 1
        res = 0
        limit = min(len(u), self.n)
        for i in range(limit):
            if u[i] and self.assignment[i]:
                res ^= 1
        return res

    def query_B_matrix(self, M_terms: Dict[Tuple[int, int], int]) -> int:
        """
        Implicit on-the-fly evaluation: B(M) = a^T M a mod 2.
        Evaluates only non-zero sparse terms. Memory: O(1) auxiliary space.
        """
        self.query_count += 1
        res = 0
        for (i, j), coeff in M_terms.items():
            if coeff % 2 != 0 and i < self.n and j < self.n:
                if self.assignment[i] and self.assignment[j]:
                    res ^= 1
        return res

    def query_B_outer(self, u: List[int], v: List[int]) -> int:
        """
        Implicit on-the-fly evaluation: B(u (x) v) = <u, a> * <v, a> mod 2.
        Memory: O(1) auxiliary space.
        """
        self.query_count += 1
        val_u = 0
        val_v = 0
        limit_u = min(len(u), self.n)
        for i in range(limit_u):
            if u[i] and self.assignment[i]:
                val_u ^= 1
        limit_v = min(len(v), self.n)
        for j in range(limit_v):
            if v[j] and self.assignment[j]:
                val_v ^= 1
        return (val_u & val_v)

    def self_corrected_query_A(self, u: List[int]) -> int:
        r = [random.randint(0, 1) for _ in range(self.n)]
        u_xor_r = [u[i] ^ r[i] for i in range(self.n)]
        return self.query_A(r) ^ self.query_A(u_xor_r)

    def self_corrected_query_B_outer(self, u: List[int], v: List[int]) -> int:
        r_terms = {(i, j): random.randint(0, 1) for i in range(self.n) for j in range(self.n)}
        r_terms = {k: v for k, v in r_terms.items() if v}
        
        m_terms = dict(r_terms)
        for i in range(self.n):
            if u[i]:
                for j in range(self.n):
                    if v[j]:
                        m_terms[(i, j)] = m_terms.get((i, j), 0) ^ 1
        m_terms = {k: v for k, v in m_terms.items() if v}

        return self.query_B_matrix(m_terms) ^ self.query_B_matrix(r_terms)


def formula_to_quadratic_system_with_calc(formula: CNFFormula):
    n_orig = formula.num_vars
    max_total_vars = n_orig + formula.num_clauses + 32
    constraints: List[QuadraticConstraint] = []
    aux_calcs = []
    next_aux = n_orig

    def get_lit_affine(lit: Literal) -> Tuple[int, int]:
        return (lit.var - 1, 1 if lit.negated else 0)

    for clause in formula.clauses:
        lits = clause.literals
        k = len(lits)
        if k == 0:
            constraints.append(QuadraticConstraint(n=max_total_vars, d=1))
        elif k == 1:
            var_i, off_i = get_lit_affine(lits[0])
            constraints.append(QuadraticConstraint(
                n=max_total_vars,
                c_terms={var_i: 1},
                d=1 ^ off_i
            ))
        elif k == 2:
            var_i, off_i = get_lit_affine(lits[0])
            var_j, off_j = get_lit_affine(lits[1])
            u1 = 1 ^ off_i
            u2 = 1 ^ off_j
            M = {(min(var_i, var_j), max(var_i, var_j)): 1} if var_i != var_j else {}
            c = {}
            if u2:
                c[var_i] = c.get(var_i, 0) ^ 1
            if u1:
                c[var_j] = c.get(var_j, 0) ^ 1
            if var_i == var_j:
                c[var_i] = c.get(var_i, 0) ^ 1

            constraints.append(QuadraticConstraint(
                n=max_total_vars,
                M_terms=M,
                c_terms=c,
                d=u1 & u2
            ))
        elif k == 3:
            var1, off1 = get_lit_affine(lits[0])
            var2, off2 = get_lit_affine(lits[1])
            var3, off3 = get_lit_affine(lits[2])
            u1, u2, u3 = 1 ^ off1, 1 ^ off2, 1 ^ off3

            aux_idx = next_aux
            next_aux += 1

            def make_calc(v1=var1, o1=u1, v2=var2, o2=u2):
                return lambda vec: ((vec[v1] ^ o1) & (vec[v2] ^ o2)) % 2

            aux_calcs.append((aux_idx, make_calc()))

            M1 = {(min(var1, var2), max(var1, var2)): 1} if var1 != var2 else {}
            c1 = {aux_idx: 1}
            if u2:
                c1[var1] = c1.get(var1, 0) ^ 1
            if u1:
                c1[var2] = c1.get(var2, 0) ^ 1
            if var1 == var2:
                c1[var1] = c1.get(var1, 0) ^ 1

            constraints.append(QuadraticConstraint(
                n=max_total_vars,
                M_terms=M1,
                c_terms=c1,
                d=u1 & u2
            ))

            M2 = {(min(aux_idx, var3), max(aux_idx, var3)): 1}
            c2 = {}
            if u3:
                c2[aux_idx] = 1

            constraints.append(QuadraticConstraint(
                n=max_total_vars,
                M_terms=M2,
                c_terms=c2,
                d=0
            ))

    total_vars = next_aux
    final_constraints = [
        QuadraticConstraint(total_vars, c.M_terms, c.c_terms, c.d) for c in constraints
    ]
    return final_constraints, total_vars, aux_calcs


def formula_to_quadratic_system(formula: CNFFormula) -> Tuple[List[QuadraticConstraint], int]:
    f3 = formula.to_3sat()
    constraints, total_vars, _ = formula_to_quadratic_system_with_calc(f3)
    return constraints, total_vars
