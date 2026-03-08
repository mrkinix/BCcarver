# BCcarver v6 — Hamiltonian Cycle Solver (Parallel Edition)
> Ben-Chiboub Carver is an experimental research project exploring constraint-propagation approaches to the Hamiltonian Cycle problem.

**Author:** Hédi Ben Chiboub ([@mrkinix](https://github.com/mrkinix))

A fast, exact Hamiltonian cycle solver written in Rust. The pruning rules were derived independently through experiment and intuition — pen and paper, no textbooks, no papers. Implementation was done with AI assistance. No prior knowledge of graph theory or Rust was assumed going in.

Many of the rules I arrived at turn out to exist in some form in the literature. I don't claim to have invented all of them. What I claim is that I rediscovered them independently, combined them in a specific way, added rules of my own, and built something that works at a level I didn't expect when I started.

**20/20 adversarial suite. N=1000 in ~17.6s. N=2000 in ~127s. Cache hits: single digits to low tens. Zero timeouts on dense random graphs up to N=2000 (N=3000 hits 300s timeout).**

---

## What Is a Hamiltonian Cycle?

A Hamiltonian cycle is a closed path through a graph that visits every node exactly once. Deciding whether one exists is NP-complete — no polynomial-time algorithm is known. This solver decides the question exactly: SAT with a valid cycle, or UNSAT with proof.

---

## Algorithm & Parallelism

The solver is a **constraint-propagation / backtracking** engine. Every edge is in one of three states: *available*, *locked* (must be in the cycle), or *deleted* (cannot be in the cycle). Propagation rules fire exhaustively before each branch, collapsing the search space. Branching is a last resort.

## Solver Pipeline

Each solve follows the same deterministic pipeline:

1. **Pre-filters**
   - Bridge detection (Tarjan)
   - Bipartite parity check

2. **Constraint Propagation**
   Apply propagation rules exhaustively until a fixed point:
   - Degree-2 forcing
   - Chord deletion
   - Saturation
   - Locked-count constraint
   - Subcycle detection
   - Endpoint connectivity
   - BC rules

3. **Branch Selection**
   Select a decision edge using the MRV + Fail-First heuristic.

4. **Branching**
   Create two branches:
   - lock(edge)
   - delete(edge)

5. **Recursive Solve**
   Propagate again and repeat.

6. **Parallel Execution**
   Initial branch tree is split to depth *d* (default 4) and subtrees are solved concurrently using Rayon.

7. **Termination**
   - A Hamiltonian cycle covering all vertices ⇒ **SAT**
   - All branches inconsistent ⇒ **UNSAT**
     

**v6 Parallel Strategy:**

Single instance solving utilizes parallel tree splitting. The solver runs initial propagation once, enumerates branch decisions to a specific split depth (default 4, producing up to 16 independent subtrees), and solves them concurrently on the thread pool. First SAT wins; all must report UNSAT for global UNSAT.

### Propagation Rules

| Rule | Description |
|-----|-------------|
| **Degree-2 forcing** | A node with only 2 available edges must use both — lock them |
| **Chord deletion** | When two forced neighbours are adjacent, their shared edge would create a premature subcycle — delete it |
| **Saturation** | A node with 2 locked edges is done — delete all remaining available edges at that node |
| **Locked-count constraint** | If more than 2 degree-2 nodes are forcing edges onto the same node — contradiction |
| **2-connectivity pruning** | If the available graph has an articulation point, no Hamiltonian cycle exists in this branch — prune |
| **Subcycle detection** | Locked edges forming a cycle on a proper subset — contradiction |
| **Path endpoint connectivity** | The two open ends of the partial locked path must be able to reach each other through available edges — else prune |
| **Degree-3 near-forcing** | One-step lookahead: if locking an edge would starve a neighbour below degree 2 via saturation cascade — delete it |

---

## Ben-Chiboub Rules (BC-1, BC-2, BC-3)

Three structural rules derived independently, specifically effective on cubic and near-cubic graphs.

### BC-1 — Diamond Chain Forcing

In a 5-node cluster where two interior nodes each have exactly one external connection, the bypass edge between them is always unused. Delete it and force the external connections.

This reduces branching on cubic substructures that appear frequently in FHCP-class graphs.

### BC-2 — Ladder Rung Forcing

In a ladder structure (two parallel chains connected by rungs, each rung node with degree 3), the rungs are forced.

Lock the rung and delete the rail chord that would create a short circuit.

### BC-3 — Square Fourth-Edge Deletion

If exactly 3 of 4 edges forming a 4-cycle are locked, the 4th must be deleted. Locking it would complete a premature subcycle.

Applied proactively before the subcycle check catches it.

---

## Branch Variable Selection

**MRV + Fail-First heuristic**

Find the most constrained node using the packed priority key:

```
avail_deg * 4 - locked_degree
```

Among its incident edges, prefer the edge whose other endpoint is most committed.

The solver intentionally commits to the hardest decisions first, causing dead branches to collapse quickly.

---

## Pre-Filters (O(n + m), executed before search)

- **Bridge detection** — iterative Tarjan algorithm; any bridge implies immediate UNSAT
- **Bipartite parity** — unequal partition sizes imply UNSAT

---

## Memoization

Dead-end states are stored keyed by the exact `(locked_bits, deleted_bits)` pair.

This is not a hash approximation — the full state is stored, so collisions cannot occur.

Benchmark results show very low cache counts (often below 30 even for N=2000), indicating that most of the search space collapses via propagation before branching occurs.

---

# Performance

## Adversarial Suite — 20/20

Run on **BCcarver v6 — 8 threads (split depth = 4).**

```
Graph                            | N     | Expected   | Result     | Time(s)   | Status
-----------------------------------------------------------------------------------------
Petersen (UNSAT)                 | 10    | UNSAT      | UNSAT      | 0.00065   | PASS
Tutte (UNSAT)                    | 46    | UNSAT      | UNSAT      | 0.17651   | PASS
8x8 Grid (SAT)                   | 64    | SAT        | SAT        | 0.01268   | PASS
Heawood (SAT)                    | 14    | SAT        | SAT        | 0.00047   | PASS
Hypercube Q4 (SAT)               | 16    | SAT        | SAT        | 0.00078   | PASS
Dodecahedral (SAT)               | 20    | SAT        | SAT        | 0.00098   | PASS
Desargues (SAT)                  | 20    | SAT        | SAT        | 0.00095   | PASS
Complete K15 (SAT)               | 15    | SAT        | SAT        | 0.00162   | PASS
Wheel W20 (SAT)                  | 20    | SAT        | SAT        | 0.00220   | PASS
Circular Ladder 10 (SAT)         | 20    | SAT        | SAT        | 0.00073   | PASS
Bipartite K5,6 (UNSAT)           | 11    | UNSAT      | UNSAT      | 0.00003   | PASS
Star S8 (UNSAT)                  | 9     | UNSAT      | UNSAT      | 0.00001   | PASS
7x7 Grid (UNSAT)                 | 49    | UNSAT      | UNSAT      | 0.00003   | PASS
Barbell B8 (UNSAT)               | 16    | UNSAT      | UNSAT      | 0.00002   | PASS
5x5 Knight (UNSAT)               | 25    | UNSAT      | UNSAT      | 0.00002   | PASS
10x10 Grid (SAT)                 | 100   | SAT        | SAT        | 0.03521   | PASS
11x11 Grid (UNSAT)               | 121   | UNSAT      | UNSAT      | 0.00007   | PASS
Hypercube Q5 (SAT)               | 32    | SAT        | SAT        | 0.00360   | PASS
Complete K20 (SAT)               | 20    | SAT        | SAT        | 0.00270   | PASS
Circular Ladder 30 (SAT)         | 60    | SAT        | SAT        | 0.00278   | PASS
```

---

## Dense Random Graphs — Phase Transition (p = 0.08)

Density around **p ≈ 0.08** is one of the hardest regimes for random graphs.

Approximately half of the graphs are Hamiltonian and half are not, meaning the solver cannot rely on structural shortcuts and must perform genuine search.

```
N     | Edges   | Time(s)   | Cache | p      | Status
-------------------------------------------------------
500   | ~10k    | ~2.6      | ~10   | 0.0800 | Solved
1000  | ~40k    | ~17.7     | ~16   | 0.0800 | Solved
2000  | ~160k   | ~127.4    | ~25   | 0.0800 | Solved
3000  | 359k    | 300.1     | 22    | 0.0800 | Timeout
```

---

# Usage

### Cargo.toml

```toml
[dependencies]
rand  = "0.8"
rayon = "1.8"

[profile.release]
opt-level = 3
```

### Commands

Run built-in benchmark suite:

```bash
cargo run --release
```

Solve a single `.hcp` file:

```bash
cargo run --release -- instance.hcp
```

Run FHCP benchmark directory:

```bash
cargo run --release -- --fhcp ./fhcp_instances/ 120
```

Random graph audit:

```bash
cargo run --release -- --random 1000 2000 0.08
```

Override thread count:

```bash
cargo run --release -- --threads 8
```

---

# FHCP Benchmark

BCcarver supports the **Flinders Hamiltonian Cycle Problem benchmark (FHCP)**:

http://www.flinders.edu.au/science_engineering/csem/research/programs/flinders-hamiltonian-cycle-project/

This dataset contains **1001 structured Hamiltonian cycle instances** commonly used in academic research.

The parser supports both:

- `EDGE_LIST`
- `ADJ_LIST`

Most FHCP instances are **sparse cubic graphs (degree 3)**, which represent a different class of difficulty than dense random graphs.

---

# Background

This project started as an experiment.

No prior knowledge of graph theory.  
No Rust experience.  
Just curiosity about a difficult problem.

The workflow was simple:

1. Study the structure of Hamiltonian cycles
2. Derive rules explaining when cycles must or cannot exist
3. Encode those rules as propagation constraints
4. Implement them in Rust

The result was a solver that performs far better than expected for a first attempt.

The name **BCcarver** reflects the idea of carving the solution space down with structural rules.

---

# Limitations

- Large sparse cubic graphs (FHCP hard instances above ~500 nodes) remain difficult
- Memoization tables may grow large on pathological inputs

---

# Author

**Hédi Ben Chiboub**  
GitHub: https://github.com/mrkinix

Built an exact solver for an NP-complete problem using intuition, experimentation, and persistence.
