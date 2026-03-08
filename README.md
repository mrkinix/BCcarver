# BCcarver — Hamiltonian Cycle Solver

A fast, exact Hamiltonian cycle solver written in Rust. Built from first principles — the pruning rules were derived independently with pen and paper through experiment and intuition, then implemented with AI assistance, though I don't claim inventing many of those rules, it happens that I just rediscovered them. No prior knowledge of graph theory or Rust was assumed.

**20/20 on adversarial test suite. Solves N=500 sparse random graphs (p=0.08) in ~3.5 seconds consistently.**

---

## What Is a Hamiltonian Cycle?

A Hamiltonian cycle is a closed path through a graph that visits every node exactly once. Deciding whether such a cycle exists is NP-complete — there is no known polynomial-time algorithm. This solver uses constraint propagation + backtracking search to find cycles exactly, or prove none exist.

---

## Algorithm

The solver is a **constraint-propagation / backtracking** engine operating on two edge states: *locked* (must be in the cycle) and *deleted* (cannot be in the cycle).

### Propagation Rules (applied exhaustively before each branch)

| Rule | Description |
|------|-------------|
| **Degree-2 forcing** | If a node has only 2 available edges, both must be locked |
| **Chord deletion** | When a node's two neighbours are adjacent, their shared edge would create a premature subcycle — delete it |
| **Saturation** | Once a node has 2 locked edges, delete all its remaining available edges |
| **Locked-count constraint** | If a node is forced by too many degree-2 nodes simultaneously, contradiction |
| **2-connectivity pruning** | If the available graph has any articulation point, no Hamiltonian cycle is possible — prune |
| **Subcycle detection** | If locked edges form a cycle on a proper subset of nodes, prune |
| **Path endpoint connectivity** | Track the two open ends of the partial path; if they cannot reach each other through available edges, prune |
| **Degree-3 near-forcing** | One-step lookahead: if locking a specific edge would starve a neighbour below degree 2, delete it |

### Branch Variable Selection (MRV + Fail-First)

Instead of picking an arbitrary edge to branch on, the solver uses **Minimum Remaining Values (MRV)**: it finds the most-constrained node (lowest available degree, highest locked degree) and branches on its tightest incident edge. This is the same heuristic used in state-of-the-art SAT/CSP solvers.

### Pre-Filters (O(n+m), run before search)

- **Bridge detection** — a graph with a bridge cannot have a Hamiltonian cycle
- **Bipartite parity check** — a bipartite graph needs equal partition sizes

### Memoization

Dead-end states are stored in a transposition table keyed by the exact `(locked_bits, deleted_bits)` pair. Collision-free, unlike Zobrist-hash-only approaches.

---

## Performance

### Adversarial Test Suite — 20/20 ✅

```
Graph                            | N     | Expected   | Result     | Time(s)   | Status
---------------------------------|-------|------------|------------|-----------|--------
Petersen (UNSAT)                 | 10    | UNSAT      | UNSAT      | 0.00052   | ✅ PASS
Tutte Graph (UNSAT)              | 46    | UNSAT      | UNSAT      | 0.16316   | ✅ PASS
8x8 Grid (SAT)                   | 64    | SAT        | SAT        | 0.01766   | ✅ PASS
Heawood (SAT)                    | 14    | SAT        | SAT        | 0.00056   | ✅ PASS
Hypercube Q4 (SAT)               | 16    | SAT        | SAT        | 0.00103   | ✅ PASS
Dodecahedral (SAT)               | 20    | SAT        | SAT        | 0.00091   | ✅ PASS
Desargues (SAT)                  | 20    | SAT        | SAT        | 0.00103   | ✅ PASS
Complete K15 (SAT)               | 15    | SAT        | SAT        | 0.00171   | ✅ PASS
Wheel W20 (SAT)                  | 20    | SAT        | SAT        | 0.00351   | ✅ PASS
Circular Ladder 10 (SAT)         | 20    | SAT        | SAT        | 0.00108   | ✅ PASS
Bipartite K5,6 (UNSAT)           | 11    | UNSAT      | UNSAT      | 0.00002   | ✅ PASS
Star S8 (UNSAT)                  | 9     | UNSAT      | UNSAT      | 0.00001   | ✅ PASS
7x7 Grid (UNSAT)                 | 49    | UNSAT      | UNSAT      | 0.00005   | ✅ PASS
Barbell B8 (UNSAT)               | 16    | UNSAT      | UNSAT      | 0.00003   | ✅ PASS
5x5 Knight (UNSAT)               | 25    | UNSAT      | UNSAT      | 0.00003   | ✅ PASS
10x10 Grid (SAT)                 | 100   | SAT        | SAT        | 0.04018   | ✅ PASS
11x11 Grid (UNSAT)               | 121   | UNSAT      | UNSAT      | 0.00012   | ✅ PASS
Hypercube Q5 (SAT)               | 32    | SAT        | SAT        | 0.00477   | ✅ PASS
Complete K20 (SAT)               | 20    | SAT        | SAT        | 0.00340   | ✅ PASS
Circular Ladder 30 (SAT)         | 60    | SAT        | SAT        | 0.00691   | ✅ PASS
```

The Petersen graph and Tutte graph are classic adversarial cases specifically constructed to be non-Hamiltonian while resisting simple heuristics. Both are handled correctly.

### Sparse Random Graphs (p = 0.08, phase-transition density)

This is the hardest regime — where approximately half of all random graphs are Hamiltonian and half are not. No easy structural shortcuts exist.

```
N     | Edges  | Time (s)
------|--------|----------
150   | ~900   | 0.15
300   | ~3600  | 0.80
491   | 9631   | 3.27
495   | 9957   | 3.41
500   | 9799   | 3.51
504   | 10328  | 3.82
```

Zero timeouts across N=100–504 at p=0.08. Scaling is sub-quadratic in this range.

---

## Usage

### Build

```toml
# Cargo.toml
[dependencies]
rand = "0.8"

[profile.release]
opt-level = 3
```

```bash
cargo build --release
```

### Run Built-in Test Suite

```bash
cargo run --release
```

### Solve a Single FHCP File

```bash
cargo run --release -- instance.hcp
```

### Run FHCP Benchmark Directory

```bash
cargo run --release -- --fhcp ./fhcp_instances/ 120
# 120 = timeout per instance in seconds
```

### Random Graph Audit

```bash
cargo run --release -- --random 100 500 0.08
# start_n end_n p
```

---

## FHCP Benchmark

This solver supports the [Flinders Hamiltonian Cycle Problem benchmark](http://www.flinders.edu.au/science_engineering/csem/research/programs/flinders-hamiltonian-cycle-project/) — 1001 structured graph instances used to compare HC solvers in the research literature.

Download the `.hcp` files and point the solver at the directory:

```bash
cargo run --release -- --fhcp ./fhcp/ 60
```

The parser handles both `EDGE_LIST` and `ADJ_LIST` formats.

---

## Input Format

The solver accepts graphs in [TSPLIB HCP format](http://comopt.ifi.uni-heidelberg.de/software/TSPLIB95/):

```
NAME: my_graph
TYPE: HCP
DIMENSION: 5
EDGE_DATA_FORMAT: EDGE_LIST
EDGE_DATA_SECTION
1 2
1 3
2 4
3 4
4 5
5 1
-1
EOF
```

Nodes are 1-indexed in the file; the solver converts to 0-indexed internally.

---

## Repository Structure

```
bc_craver_v4.rs   — full solver (single file, ~1370 lines)
README.md         — this file
```

---

## Background

This project started as an experiment: could someone with no formal computer science background, no Rust experience, and no prior knowledge of graph theory build a competitive Hamiltonian cycle solver? The approach was to study the problem from scratch, derive pruning rules by hand, and use AI as an implementation assistant.

The core algorithmic ideas — degree-2 forcing, 2-connectivity pruning, MRV branching — were arrived at independently before discovering they match techniques in the published literature (Vandeghen 2012, and earlier work going back to the 1970s). The path endpoint connectivity prune and degree-3 near-forcing lookahead are refinements developed during this project.

The solver is not the fastest in the world. State-of-the-art approaches using linear programming relaxations (Concorde, LKH) solve vastly larger instances. What this solver demonstrates is that the combinatorial core of the problem — the constraint propagation structure — is discoverable from first principles, and that a clean implementation of the right rules competes with published research solvers from 10–15 years ago.

---

## Limitations

- Single-threaded
- No LP relaxation (pure combinatorial search)
- Large sparse cubic graphs (N>600, degree=3) may exceed practical time limits
- Memory usage grows with memoization table on hard instances

---

## Author

[@mrkinix](https://github.com/mrkinix)

