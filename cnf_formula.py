"""
CNF Formula representation, 3-SAT normalizer, DIMACS parser, and formula restriction
for self-reducibility and Holographic Proofs.
"""

from typing import List, Set, Dict, Optional, Tuple, Union, Callable
import re


class Literal:
    """Represents a Boolean literal (x_i or not x_i). Variable index is 1-based."""
    __slots__ = ('var', 'negated')

    def __init__(self, var: int, negated: bool = False):
        if var <= 0:
            raise ValueError(f"Variable index must be positive, got {var}")
        self.var = var
        self.negated = negated

    @classmethod
    def from_int(cls, lit: int) -> 'Literal':
        if lit == 0:
            raise ValueError("Literal cannot be 0 in DIMACS format")
        return cls(var=abs(lit), negated=(lit < 0))

    def to_int(self) -> int:
        return -self.var if self.negated else self.var

    def negate(self) -> 'Literal':
        return Literal(self.var, not self.negated)

    def evaluate(self, assignment: Dict[int, bool]) -> Optional[bool]:
        if self.var not in assignment:
            return None
        val = assignment[self.var]
        return not val if self.negated else val

    def __repr__(self) -> str:
        return f"~x{self.var}" if self.negated else f"x{self.var}"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Literal):
            return False
        return self.var == other.var and self.negated == other.negated

    def __hash__(self) -> int:
        return hash((self.var, self.negated))


class Clause:
    """Represents a disjunctive clause (l_1 or l_2 or ... or l_k)."""
    __slots__ = ('literals',)

    def __init__(self, literals: List[Literal]):
        seen = set()
        unique_lits = []
        for lit in literals:
            if lit not in seen:
                seen.add(lit)
                unique_lits.append(lit)
        self.literals: Tuple[Literal, ...] = tuple(unique_lits)

    @classmethod
    def from_ints(cls, lits: List[int]) -> 'Clause':
        return cls([Literal.from_int(x) for x in lits])

    def to_ints(self) -> List[int]:
        return [lit.to_int() for lit in self.literals]

    def evaluate(self, assignment: Dict[int, bool]) -> Optional[bool]:
        has_unassigned = False
        for lit in self.literals:
            val = lit.evaluate(assignment)
            if val is True:
                return True
            if val is None:
                has_unassigned = True
        return None if has_unassigned else False

    def is_satisfied(self, assignment: Dict[int, bool]) -> bool:
        return self.evaluate(assignment) is True

    def restrict(self, var: int, val: bool) -> Optional['Clause']:
        new_lits = []
        for lit in self.literals:
            if lit.var == var:
                lit_val = (not val) if lit.negated else val
                if lit_val:
                    return None  # Clause is satisfied!
                else:
                    continue  # Literal is False, drop from clause
            else:
                new_lits.append(lit)
        return Clause(new_lits)

    def __len__(self) -> int:
        return len(self.literals)

    def __repr__(self) -> str:
        if not self.literals:
            return "FALSE"
        return "(" + " v ".join(str(lit) for lit in self.literals) + ")"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Clause):
            return False
        return self.literals == other.literals

    def __hash__(self) -> int:
        return hash(self.literals)


class CNFFormula:
    """Represents a Boolean formula in Conjunctive Normal Form (CNF)."""

    def __init__(self, clauses: Optional[List[Clause]] = None, num_vars: Optional[int] = None):
        self.clauses: List[Clause] = clauses or []
        if num_vars is not None:
            self._num_vars = num_vars
        else:
            self._num_vars = self._compute_max_var()

    def _compute_max_var(self) -> int:
        max_v = 0
        for clause in self.clauses:
            for lit in clause.literals:
                if lit.var > max_v:
                    max_v = lit.var
        return max_v

    @property
    def num_vars(self) -> int:
        return max(self._num_vars, self._compute_max_var())

    @property
    def num_clauses(self) -> int:
        return len(self.clauses)

    def add_clause(self, clause: Union[Clause, List[int], List[Literal]]):
        if isinstance(clause, Clause):
            self.clauses.append(clause)
        elif isinstance(clause, list):
            if clause and isinstance(clause[0], Literal):
                self.clauses.append(Clause(clause))
            else:
                self.clauses.append(Clause.from_ints(clause))
        self._num_vars = max(self._num_vars, self._compute_max_var())

    def restrict(self, var: int, val: bool) -> 'CNFFormula':
        """Self-reducibility operator phi|x_var = val."""
        new_clauses = []
        for clause in self.clauses:
            res = clause.restrict(var, val)
            if res is not None:
                new_clauses.append(res)
        return CNFFormula(new_clauses, num_vars=self.num_vars)

    def evaluate(self, assignment: Dict[int, bool]) -> Optional[bool]:
        has_unassigned = False
        for clause in self.clauses:
            val = clause.evaluate(assignment)
            if val is False:
                return False
            if val is None:
                has_unassigned = True
        return None if has_unassigned else True

    def is_satisfied(self, assignment: Dict[int, bool]) -> bool:
        return self.evaluate(assignment) is True

    def has_empty_clause(self) -> bool:
        return any(len(c) == 0 for c in self.clauses)

    def is_empty(self) -> bool:
        return len(self.clauses) == 0

    def to_3sat_and_extension(self) -> Tuple['CNFFormula', Callable[[Dict[int, bool]], Dict[int, bool]]]:
        """
        Converts CNF clauses to 3-CNF and returns a closure that extends any
        satisfying assignment of the original formula to the 3-SAT auxiliary variables.
        """
        new_clauses: List[Clause] = []
        next_aux_var = self.num_vars + 1
        aux_assigners = []

        for clause in self.clauses:
            k = len(clause)
            if k == 0:
                new_clauses.append(Clause([]))
            elif k == 1:
                l = clause.literals[0]
                y1 = Literal(next_aux_var)
                y2 = Literal(next_aux_var + 1)
                aux_var_ids = (next_aux_var, next_aux_var + 1)
                next_aux_var += 2
                new_clauses.append(Clause([l, y1, y2]))
                new_clauses.append(Clause([l, y1, y2.negate()]))
                new_clauses.append(Clause([l, y1.negate(), y2]))
                new_clauses.append(Clause([l, y1.negate(), y2.negate()]))

                def make_1_assigner(ids=aux_var_ids):
                    def assign(curr):
                        curr[ids[0]] = False
                        curr[ids[1]] = False
                    return assign
                aux_assigners.append(make_1_assigner())

            elif k == 2:
                l1, l2 = clause.literals[0], clause.literals[1]
                y = Literal(next_aux_var)
                aux_var_id = next_aux_var
                next_aux_var += 1
                new_clauses.append(Clause([l1, l2, y]))
                new_clauses.append(Clause([l1, l2, y.negate()]))

                def make_2_assigner(y_id=aux_var_id):
                    def assign(curr):
                        curr[y_id] = False
                    return assign
                aux_assigners.append(make_2_assigner())

            elif k == 3:
                new_clauses.append(clause)
            else:
                lits = clause.literals
                aux_var_ids = [next_aux_var + i for i in range(k - 3)]
                aux_vars = [Literal(v_id) for v_id in aux_var_ids]
                next_aux_var += (k - 3)

                new_clauses.append(Clause([lits[0], lits[1], aux_vars[0]]))
                for i in range(1, k - 3):
                    new_clauses.append(Clause([aux_vars[i - 1].negate(), lits[i + 1], aux_vars[i]]))
                new_clauses.append(Clause([aux_vars[-1].negate(), lits[-2], lits[-1]]))

                def make_k_assigner(literals=lits, aux_ids=aux_var_ids):
                    def assign(curr):
                        # Find first true literal
                        true_idx = None
                        for idx, lit in enumerate(literals):
                            if lit.evaluate(curr) is True:
                                true_idx = idx + 1
                                break
                        if true_idx is None or true_idx <= 2:
                            for y_id in aux_ids:
                                curr[y_id] = False
                        else:
                            split_point = true_idx - 2
                            for i, y_id in enumerate(aux_ids):
                                curr[y_id] = (i < split_point)
                    return assign
                aux_assigners.append(make_k_assigner())

        f3 = CNFFormula(new_clauses, num_vars=next_aux_var - 1)

        def extend_assignment(base_assign: Dict[int, bool]) -> Dict[int, bool]:
            extended = dict(base_assign)
            # Ensure base vars are present
            for i in range(1, self.num_vars + 1):
                if i not in extended:
                    extended[i] = False
            for assigner in aux_assigners:
                assigner(extended)
            return extended

        return f3, extend_assignment

    def to_3sat(self) -> 'CNFFormula':
        f3, _ = self.to_3sat_and_extension()
        return f3

    @classmethod
    def from_dimacs_string(cls, dimacs_str: str) -> 'CNFFormula':
        clauses = []
        num_vars = 0
        for line in dimacs_str.strip().splitlines():
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p'):
                parts = line.split()
                if len(parts) >= 3 and parts[1] == 'cnf':
                    num_vars = int(parts[2])
                continue
            tokens = [int(tok) for tok in line.split() if tok != '']
            if not tokens:
                continue
            current_clause = []
            for tok in tokens:
                if tok == 0:
                    clauses.append(Clause.from_ints(current_clause))
                    current_clause = []
                else:
                    current_clause.append(tok)
            if current_clause:
                clauses.append(Clause.from_ints(current_clause))
        return cls(clauses, num_vars=num_vars)

    def to_dimacs(self) -> str:
        lines = [f"p cnf {self.num_vars} {self.num_clauses}"]
        for clause in self.clauses:
            ints = clause.to_ints()
            lines.append(" ".join(map(str, ints)) + " 0")
        return "\n".join(lines)

    def __repr__(self) -> str:
        if not self.clauses:
            return "TRUE (Empty formula)"
        return " ^\n".join(str(c) for c in self.clauses)
