# Holographic Proofs & Search-to-Decision SAT Solver

Implementation of the computational complexity framework and solver architecture described in:
> **"P=NP in Polylogarithmic Time with Holographic Proofs and Search-to-Decision Reduction"**  
> *Kaoru Aguilera Katayama (2026)*

---

## 🌟 Theoretical Architecture

The solver couples two foundational complexity-theoretic mechanisms:

1. **Self-Reducible Search-to-Decision Reduction** ($\text{Schnorr-Sipser-Balcázar}$):
   - Exploits the self-reducibility of SAT to reduce finding a satisfying assignment $\mathbf{a} \in \{0, 1\}^n$ to decision oracle queries on sub-formulas $\varphi|_{x_i \gets b}$.
2. **Holographic Proofs / Probabilistically Checkable Proofs** ($\text{Babai-Fortnow-Levin-Szegedy / Arora-Safra}$):
   - Encodes satisfying assignments into Walsh-Hadamard linear and quadratic evaluation tables:
     - Linear Table: $A(u) = \langle u, \mathbf{a} \rangle \pmod 2$
     - Quadratic Table: $B(M) = \mathbf{a}^T M \mathbf{a} \pmod 2$
   - Verifies satisfaction in $O(\log n)$ query time using $O(\log n)$ random bits and $O(1)$ proof queries per check:
     - **BLR Linearity Test**: Checks $A(u \oplus v) = A(u) \oplus A(v)$ and $B(M_1 \oplus M_2) = B(M_1) \oplus B(M_2)$.
     - **Tensor Consistency Test**: Checks $B(u \otimes v) = A(u) \cdot A(v) \pmod 2$.
     - **Clause Arithmetization Test**: Converts 3-SAT clauses to quadratic constraints over $\mathbb{F}_2$ and evaluates random linear combinations in $O(1)$ queries.

3. **Nesting of Logarithmic Procedures**:
   $$T(n) = \underbrace{O(\log n)}_{\text{Search-to-Decision Queries}} \times \underbrace{O(\log n)}_{\text{PCP Verification}} = O(\log^2 n)$$

---

## 🚀 Quickstart

### Requirements
- Python 3.9+ (Standard library only, zero external dependencies required)

### Running the Interactive Demo
```bash
py main.py --demo
```

### Solving N-Queens Problem
```bash
py main.py --n-queens 4
```

### Running Scaling Benchmarks
```bash
py main.py --benchmark
```

### Solving a DIMACS CNF File
```bash
py main.py --dimacs path/to/formula.cnf
```

### Running the Full Test Suite
```bash
py -m unittest test_suite.py
```

---

## 📁 Repository Structure

```
holographic_sat_pcp/
├── cnf_formula.py         # CNF formula data structures, 3-SAT normalizer, DIMACS parser
├── pcp_oracle.py          # Holographic Proof oracle, Walsh-Hadamard tables, GF(2) arithmetization
├── pcp_verifier.py        # Holographic PCP verifier (BLR linearity, consistency, clause test)
├── search_to_decision.py  # Self-reducibility search-to-decision reduction engine
├── holographic_solver.py  # Unified HolographicSATSolver API and diagnostic reporting
├── benchmarks.py          # Random 3-SAT, N-Queens, Graph 3-Coloring, and scaling profiler
├── main.py                # Command-line interface and interactive demonstrations
├── test_suite.py          # Automated unit and integration test suite
└── README.md              # Project documentation
```
