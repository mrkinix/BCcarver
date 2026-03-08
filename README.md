# BCcarver — Hamiltonian Cycle Solver

**Author:** Hédi Ben Chiboub ([@mrkinix](https://github.com/mrkinix))

A fast, exact Hamiltonian cycle solver written in Rust. The pruning rules were derived independently through experiment and intuition — pen and paper, no textbooks, no papers. Implementation was done with AI assistance. No prior knowledge of graph theory or Rust was assumed going in.

Many of the rules I arrived at turn out to exist in some form in the literature. I don't claim to have invented all of them. What I claim is that I rediscovered them independently, combined them in a specific way, added rules of my own, and built something that works at a level I didn't expect when I started.

**20/20 adversarial suite. N=1000 in ~18s. N=1500 in ~55s. N=2000 in ~128s. Cache hits: single digits to low tens. Zero timeouts on dense random graphs up to N=2000.**

---

## What Is a Hamiltonian Cycle?

A Hamiltonian cycle is a closed path through a graph that visits every node exactly once. Deciding whether one exists is NP-complete — no polynomial-time algorithm is known. This solver decides the question exactly: SAT with a valid cycle, or UNSAT with proof.

---

## Algorithm

The solver is a **constraint-propagation / backtracking** engine. Every edge is in one of three states: *available*, *locked* (must be in the cycle), or *deleted* (cannot be in the cycle). Propagation rules fire exhaustively before each branch, collapsing the search space. Branching is a last resort.

### Propagation Rules

| Rule | Description |
|------|-------------|
| **Degree-2 forcing** | A node with only 2 available edges must use both — lock them |
| **Chord deletion** | When two forced neighbours are adjacent, their shared edge would create a premature subcycle — delete it |
| **Saturation** | A node with 2 locked edges is done — delete all remaining available edges at that node |
| **Locked-count constraint** | If more than 2 degree-2 nodes are forcing edges onto the same node — contradiction |
| **2-connectivity pruning** | If the available graph has an articulation point, no Hamiltonian cycle exists in this branch — prune |
| **Subcycle detection** | Locked edges forming a cycle on a proper subset — contradiction |
| **Path endpoint connectivity** | The two open ends of the partial locked path must be able to reach each other through available edges — else prune |
| **Degree-3 near-forcing** | One-step lookahead: if locking an edge would starve a neighbour below degree 2 via saturation cascade — delete it |

### Ben-Chiboub Rules (BC-1, BC-2, BC-3)

Three structural rules derived independently, specifically effective on cubic and near-cubic graphs:

**BC-1 — Diamond chain forcing:** In a 5-node cluster where two interior nodes each have exactly one external connection, the bypass edge between them is always unused — delete it, and force the external connections. Reduces branching on cubic substructures that appear constantly in FHCP-class graphs.

**BC-2 — Ladder rung forcing:** In a ladder-structured section (two parallel chains connected by rungs, each rung node with degree 3), the rungs are forced. Lock the rung, delete the rail chord that would create a short-circuit.

**BC-3 — Square fourth-edge deletion:** If exactly 3 of 4 edges forming a 4-cycle are locked, the 4th must be deleted — locking it would complete a subcycle. Applied proactively, before the subcycle check catches it after the fact.

### Branch Variable Selection

**MRV + Fail-First:** Find the most constrained node — minimum available degree, maximum locked degree — using the packed key `avail_deg * 4 - locked_degree`. Among its incident edges, prefer the one whose other endpoint is most committed. The solver commits to the hardest decisions first, failing fast on dead ends.

### Pre-Filters (O(n+m), run once before search)

- **Bridge detection** — iterative Tarjan; any bridge means UNSAT immediately
- **Bipartite parity** — unequal partition sizes means UNSAT immediately

### Memoization

Dead-end states are stored keyed by the exact `(locked_bits, deleted_bits)` pair — not a hash, the full state. Collision-free. Low cache counts in benchmarks (typically under 30 even at N=2000) show how rarely the solver revisits states: propagation resolves most of the problem before branching is needed.

---

## Performance

### Adversarial Suite — 20/20 ✅

```
Graph                            | N     | Expected | Result | Time(s)  | Status
---------------------------------|-------|----------|--------|----------|--------
Petersen (UNSAT)                 | 10    | UNSAT    | UNSAT  | 0.00062  | ✅ PASS
Tutte (UNSAT)                    | 46    | UNSAT    | UNSAT  | 0.17308  | ✅ PASS
8x8 Grid (SAT)                   | 64    | SAT      | SAT    | 0.01246  | ✅ PASS
Heawood (SAT)                    | 14    | SAT      | SAT    | 0.00051  | ✅ PASS
Hypercube Q4 (SAT)               | 16    | SAT      | SAT    | 0.00097  | ✅ PASS
Dodecahedral (SAT)               | 20    | SAT      | SAT    | 0.00101  | ✅ PASS
Desargues (SAT)                  | 20    | SAT      | SAT    | 0.00115  | ✅ PASS
Complete K15 (SAT)               | 15    | SAT      | SAT    | 0.00149  | ✅ PASS
Wheel W20 (SAT)                  | 20    | SAT      | SAT    | 0.00220  | ✅ PASS
Circular Ladder 10 (SAT)         | 20    | SAT      | SAT    | 0.00057  | ✅ PASS
Bipartite K5,6 (UNSAT)           | 11    | UNSAT    | UNSAT  | 0.00001  | ✅ PASS
Star S8 (UNSAT)                  | 9     | UNSAT    | UNSAT  | 0.00000  | ✅ PASS
7x7 Grid (UNSAT)                 | 49    | UNSAT    | UNSAT  | 0.00003  | ✅ PASS
Barbell B8 (UNSAT)               | 16    | UNSAT    | UNSAT  | 0.00002  | ✅ PASS
5x5 Knight (UNSAT)               | 25    | UNSAT    | UNSAT  | 0.00002  | ✅ PASS
10x10 Grid (SAT)                 | 100   | SAT      | SAT    | 0.03575  | ✅ PASS
11x11 Grid (UNSAT)               | 121   | UNSAT    | UNSAT  | 0.00007  | ✅ PASS
Hypercube Q5 (SAT)               | 32    | SAT      | SAT    | 0.00387  | ✅ PASS
Complete K20 (SAT)               | 20    | SAT      | SAT    | 0.00273  | ✅ PASS
Circular Ladder 30 (SAT)         | 60    | SAT      | SAT    | 0.00339  | ✅ PASS
```

### Dense Random Graphs — p = 0.08 (Phase-Transition Density)

p = 0.08 is the hardest density for large random graphs — roughly half are Hamiltonian, half are not. No structural shortcuts. Every instance requires real search.

The cache column is the number of memoized dead ends. These numbers tell the real story: the solver is not exploring large search trees. It's propagating its way to the answer.

```
N     | Edges   | Time (s) | Cache hits
------|---------|----------|------------
500   | ~9,800  | 3.5      | ~10
1000  | ~40,200 | 17.3     | ~15
1500  | 90,063  | 54.6     | 24
2000  | 160,376 | 128.5    | 28
```

Zero timeouts. The full N=1000–1099 run, 100 consecutive graphs, zero failures:

```
N     | Edges  | Time(s) | Cache | N     | Edges  | Time(s) | Cache
------|--------|---------|-------|-------|--------|---------|------
1000  | 40156  | 17.32   | 18    | 1050  | 43728  | 20.04   | 17
1010  | 40364  | 17.34   | 14    | 1060  | 44960  | 20.73   | 16
1020  | 41588  | 19.63   | 13    | 1070  | 45707  | 21.21   | 13
1030  | 42582  | 19.30   | 14    | 1080  | 46964  | 21.79   | 7
1040  | 43097  | 19.71   | 17    | 1099  | 48129  | 22.37   | 17
```

---

## Usage

```toml
# Cargo.toml
[dependencies]
rand = "0.8"

[profile.release]
opt-level = 3
```

```bash
# Built-in adversarial suite + random audit
cargo run --release

# Solve a single .hcp file
cargo run --release -- instance.hcp

# Run full FHCP benchmark directory (120s timeout per instance)
cargo run --release -- --fhcp ./fhcp_instances/ 120

# Random graph audit: start_n end_n p
cargo run --release -- --random 1000 2000 0.08
```

---

## FHCP Benchmark

The solver supports the [Flinders Hamiltonian Cycle Problem benchmark](http://www.flinders.edu.au/science_engineering/csem/research/programs/flinders-hamiltonian-cycle-project/) — 1001 structured instances used to compare HC solvers in research. The HCP parser handles both `EDGE_LIST` and `ADJ_LIST` formats.

Note: FHCP instances are mostly sparse cubic graphs (degree 3), which are a different hard case from dense random graphs. BCcarver handles small-to-medium FHCP instances well. Large sparse cubic instances (N > 500) are the open challenge that am working on.

---

## Background

I started this knowing nothing about graph theory and having never written Rust. I wanted to work on something genuinely hard — not a tutorial project. The Hamiltonian cycle problem is NP-complete. I picked it.

The approach: study the problem structure, understand why a cycle can or cannot exist, derive rules that encode that understanding. Pen and paper. A lot of trial and error. Then implement with AI handling the Rust syntax while I directed the algorithm.

Many rules I arrived at independently exist in published literature. I didn't know that when I derived them. The BC rules and some implementation choices I haven't found in papers, though I make no strong novelty claims without a full literature survey.

What I can say: the combination works. N=2000 in 128 seconds with 28 cache hits on an NP-complete problem is not what I expected when I started.

BCcarver is named after me because it's mine. Not because I think I invented constraint propagation.

---

## Limitations (working on it)

- Single-threaded
- No LP relaxation — pure combinatorial search
- Sparse cubic graphs (FHCP hard instances, N > 500) remain challenging
- Memory scales with memoization table on adversarial inputs

---

## Author

**Hédi Ben Chiboub** — [@mrkinix](https://github.com/mrkinix)

CS dropout. First Rust project. First graph theory project. Built a competitive exact solver for an NP-complete problem with pen and paper and stubbornness.
