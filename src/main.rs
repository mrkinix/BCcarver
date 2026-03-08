// bc_craver_v4.rs — Hamiltonian Cycle Solver
// Ben Chiboub Carver v4
// USAGE:
//   cargo run --release                     → runs built-in adversarial suite + random audit
//   cargo run --release -- file.hcp         → solve a single FHCP .hcp file
//   cargo run --release -- --fhcp dir/      → run all *.hcp files in a directory
//
// Cargo.toml dependencies needed:
//   [dependencies]
//   rand = "0.8"

use std::collections::{HashMap, HashSet, VecDeque};
use std::time::Instant;
use std::path::Path;
use std::fs;
use std::env;
use rand::distributions::Uniform;
use rand::prelude::*;
use std::cmp::{max, min};

// ===================== DATA TYPES =====================

#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
struct Edge(usize, usize);

#[derive(Copy, Clone)]
enum Change {
    Lock(usize),
    Delete(usize),
}

enum PropResult {
    Continue,
    Contradiction,
    Solved,
}

// ===================== SOLVER STRUCT =====================

struct BcCraver {
    n: usize,
    g_orig: Vec<Vec<usize>>,
    memo_cache: HashMap<(Vec<u64>, Vec<u64>), ()>,
    best_path: Option<Vec<Edge>>,
    all_edges: Vec<Edge>,
    edge_id: HashMap<Edge, usize>,
    node_edges: Vec<Vec<usize>>,   // node → list of edge ids incident to it
    locked_bits: Vec<u64>,
    deleted_bits: Vec<u64>,
    undo_stack: Vec<Change>,
    locked_degree: Vec<usize>,
    total_deletions: usize,
    words: usize,                  // number of u64 words per adjacency row
    g_avail_bits: Vec<Vec<u64>>,   // current available adjacency (bitset)
    avail_deg: Vec<usize>,
    orig_bits: Vec<Vec<u64>>,
    orig_deg: Vec<usize>,
    // Path endpoint tracking: the partial locked path has exactly 2 "open ends"
    // (nodes with locked_degree == 1). Tracking them lets us apply the
    // path-closure prune without a full graph scan.
    path_endpoints: Vec<usize>,    // 0 or 2 nodes with locked_degree == 1
}

impl BcCraver {
    fn new(g: &[Vec<usize>]) -> Self {
        let n = g.len();

        let mut edge_set: HashSet<Edge> = HashSet::new();
        for u in 0..n {
            for &v in &g[u] {
                if u < v { edge_set.insert(Edge(u, v)); }
            }
        }
        let mut all_edges: Vec<Edge> = edge_set.into_iter().collect();
        // Sort for deterministic behaviour across runs
        all_edges.sort_unstable_by_key(|e| (e.0, e.1));

        let mut edge_id: HashMap<Edge, usize> = HashMap::new();
        for (i, &e) in all_edges.iter().enumerate() { edge_id.insert(e, i); }

        let m = all_edges.len();
        let num_words = (m * 2 + 63) / 64;

        let mut node_edges: Vec<Vec<usize>> = vec![vec![]; n];
        for (id, &Edge(u, v)) in all_edges.iter().enumerate() {
            node_edges[u].push(id);
            node_edges[v].push(id);
        }

        let words = (n + 63) / 64;
        let mut g_avail_bits = vec![vec![0u64; words]; n];
        let mut avail_deg = vec![0usize; n];
        for u in 0..n {
            avail_deg[u] = g[u].len();
            for &v in &g[u] {
                let w = v / 64; let b = v % 64;
                if w < words { g_avail_bits[u][w] |= 1u64 << b; }
            }
        }
        let orig_bits = g_avail_bits.clone();
        let orig_deg  = avail_deg.clone();

        BcCraver {
            n,
            g_orig: g.to_vec(),
            memo_cache: HashMap::new(),
            best_path: None,
            all_edges,
            edge_id,
            node_edges,
            locked_bits:   vec![0u64; num_words],
            deleted_bits:  vec![0u64; num_words],
            undo_stack:    vec![],
            locked_degree: vec![0; n],
            total_deletions: 0,
            words,
            g_avail_bits,
            avail_deg,
            orig_bits,
            orig_deg,
            path_endpoints: vec![],
        }
    }

    // ===================== BIT OPERATIONS =====================

    #[inline] fn is_locked(&self, id: usize) -> bool {
        (self.locked_bits[(id*2)/64] & (1u64 << ((id*2)%64))) != 0
    }
    #[inline] fn is_deleted(&self, id: usize) -> bool {
        (self.deleted_bits[(id*2+1)/64] & (1u64 << ((id*2+1)%64))) != 0
    }
    #[inline] fn is_active(&self, id: usize) -> bool {
        !self.is_locked(id) && !self.is_deleted(id)
    }
    #[inline] fn clear_avail(&mut self, u: usize, v: usize) {
        let w = v/64; let b = v%64;
        if w < self.words { self.g_avail_bits[u][w] &= !(1u64 << b); }
    }
    #[inline] fn set_avail(&mut self, u: usize, v: usize) {
        let w = v/64; let b = v%64;
        if w < self.words { self.g_avail_bits[u][w] |= 1u64 << b; }
    }
    #[inline] fn has_edge(&self, u: usize, v: usize) -> bool {
        if v >= self.n { return false; }
        (self.g_avail_bits[u][v/64] & (1u64 << (v%64))) != 0
    }

    // ===================== APPLY / UNDO =====================

    fn apply_lock(&mut self, id: usize) {
        self.locked_bits[(id*2)/64] |= 1u64 << ((id*2)%64);
        let Edge(u, v) = self.all_edges[id];
        self.locked_degree[u] += 1;
        self.locked_degree[v] += 1;
        // Update path endpoints
        for &node in &[u, v] {
            let ld = self.locked_degree[node];
            if ld == 1 {
                self.path_endpoints.push(node);
            } else if ld == 2 {
                self.path_endpoints.retain(|&x| x != node);
            }
        }
        self.undo_stack.push(Change::Lock(id));
    }

    fn apply_delete(&mut self, id: usize) {
        self.deleted_bits[(id*2+1)/64] |= 1u64 << ((id*2+1)%64);
        let Edge(u, v) = self.all_edges[id];
        self.clear_avail(u, v);
        self.clear_avail(v, u);
        self.avail_deg[u] -= 1;
        self.avail_deg[v] -= 1;
        self.total_deletions += 1;
        self.undo_stack.push(Change::Delete(id));
    }

    fn undo(&mut self) {
        match self.undo_stack.pop() {
            Some(Change::Lock(id)) => {
                self.locked_bits[(id*2)/64] &= !(1u64 << ((id*2)%64));
                let Edge(u, v) = self.all_edges[id];
                self.locked_degree[u] -= 1;
                self.locked_degree[v] -= 1;
                // Restore path endpoints
                for &node in &[u, v] {
                    let ld = self.locked_degree[node];
                    if ld == 1 {
                        self.path_endpoints.push(node);
                    } else if ld == 0 {
                        self.path_endpoints.retain(|&x| x != node);
                    }
                }
            }
            Some(Change::Delete(id)) => {
                self.deleted_bits[(id*2+1)/64] &= !(1u64 << ((id*2+1)%64));
                let Edge(u, v) = self.all_edges[id];
                self.set_avail(u, v);
                self.set_avail(v, u);
                self.avail_deg[u] += 1;
                self.avail_deg[v] += 1;
                self.total_deletions -= 1;
            }
            None => {}
        }
    }

    fn undo_to(&mut self, target: usize) {
        while self.undo_stack.len() > target { self.undo(); }
    }

    // ===================== MEMOIZATION =====================

    fn is_seen(&self) -> bool {
        let key = (self.locked_bits.clone(), self.deleted_bits.clone());
        self.memo_cache.contains_key(&key)
    }

    fn memoize(&mut self) {
        let key = (self.locked_bits.clone(), self.deleted_bits.clone());
        self.memo_cache.insert(key, ());
    }

    fn get_memo_size(&self) -> usize { self.memo_cache.len() }

    // ===================== GRAPH QUERIES =====================

    fn get_avail_neighbors(&self, u: usize) -> Vec<usize> {
        let mut res = Vec::with_capacity(self.avail_deg[u]);
        for wi in 0..self.words {
            let mut word = self.g_avail_bits[u][wi];
            while word != 0 {
                let tz = word.trailing_zeros() as usize;
                let v = wi * 64 + tz;
                if v < self.n { res.push(v); }
                word &= word - 1;
            }
        }
        res
    }

    fn build_avail_adj(&self) -> Vec<Vec<usize>> {
        (0..self.n).map(|u| self.get_avail_neighbors(u)).collect()
    }

    fn build_locked_graph(&self) -> Vec<Vec<usize>> {
        let mut gl = vec![vec![]; self.n];
        for (id, &Edge(u, v)) in self.all_edges.iter().enumerate() {
            if self.is_locked(id) { gl[u].push(v); gl[v].push(u); }
        }
        gl
    }

    fn collect_locked(&self) -> Vec<Edge> {
        self.all_edges.iter().enumerate()
            .filter(|&(id, _)| self.is_locked(id))
            .map(|(_, &e)| e)
            .collect()
    }

    fn is_connected_iter(&self, g: &[Vec<usize>]) -> bool {
        if self.n == 0 { return true; }
        let mut visited = vec![false; self.n];
        let mut stack = vec![0usize];
        visited[0] = true;
        while let Some(u) = stack.pop() {
            for &v in &g[u] {
                if !visited[v] { visited[v] = true; stack.push(v); }
            }
        }
        visited.iter().all(|&x| x)
    }

    fn connected_components(&self, g: &[Vec<usize>]) -> usize {
        let mut visited = vec![false; self.n];
        let mut count = 0;
        for start in 0..self.n {
            if !visited[start] {
                count += 1;
                let mut stack = vec![start];
                visited[start] = true;
                while let Some(u) = stack.pop() {
                    for &v in &g[u] {
                        if !visited[v] { visited[v] = true; stack.push(v); }
                    }
                }
            }
        }
        count
    }

    fn has_subcycle(&self, gl: &[Vec<usize>]) -> bool {
        let mut visited = vec![false; self.n];
        for start in 0..self.n {
            if !visited[start] {
                let mut comp = vec![];
                let mut stack = vec![start];
                visited[start] = true;
                comp.push(start);
                while let Some(u) = stack.pop() {
                    for &v in &gl[u] {
                        if !visited[v] {
                            visited[v] = true; comp.push(v); stack.push(v);
                        }
                    }
                }
                if comp.len() < self.n && comp.iter().all(|&u| gl[u].len() == 2) {
                    return true;
                }
            }
        }
        false
    }

    fn is_full_cycle(&self, gl: &[Vec<usize>]) -> bool {
        gl.iter().all(|adj| adj.len() == 2) && self.is_connected_iter(gl)
    }

    // Iterative Tarjan articulation point detection
    // Returns true as soon as the first AP is found (early exit)
    fn has_articulation_point(&self, g: &[Vec<usize>]) -> bool {
        if self.n <= 2 { return false; }
        let mut disc   = vec![-1i32; self.n];
        let mut low    = vec![ 0i32; self.n];
        let mut parent = vec![-1i32; self.n];
        let mut timer  = 0i32;

        // Explicit stack entry: (node, neighbour_index)
        let mut stack: Vec<(usize, usize)> = vec![];

        for root in 0..self.n {
            if disc[root] != -1 { continue; }
            disc[root] = timer; low[root] = timer; timer += 1;
            stack.push((root, 0));
            let mut root_children = 0usize;

            while let Some((u, ni)) = stack.last_mut() {
                let u = *u;
                if *ni < g[u].len() {
                    let v = g[u][*ni];
                    *ni += 1;
                    if disc[v] == -1 {
                        if parent[u] == -1 { root_children += 1; }
                        parent[v] = u as i32;
                        disc[v] = timer; low[v] = timer; timer += 1;
                        stack.push((v, 0));
                    } else if v as i32 != parent[u] {
                        low[u] = min(low[u], disc[v]);
                    }
                } else {
                    stack.pop();
                    if let Some(&(p, _)) = stack.last() {
                        low[p] = min(low[p], low[u]);
                        // Check if p is an AP via this child u
                        if parent[p] == -1 {
                            // root: handled after DFS
                        } else if low[u] >= disc[p] {
                            return true;
                        }
                    }
                }
            }
            // Check root
            if root_children > 1 { return true; }
        }
        false
    }

    // ===================== PATH ENDPOINT PRUNE =====================
    // If we have exactly 2 open path endpoints (A and B), and no available
    // path exists between A and B in the available graph *excluding* all
    // already-fully-locked nodes (locked_degree==2), then this state is UNSAT.
    // We do a simple reachability check: BFS from A, only through nodes that
    // still need edges (locked_degree < 2), see if we can reach B.
    fn path_endpoints_connected(&self) -> bool {
        if self.path_endpoints.len() != 2 { return true; } // no constraint yet
        let a = self.path_endpoints[0];
        let b = self.path_endpoints[1];

        // BFS from a to b using only available edges through non-saturated nodes
        let mut visited = vec![false; self.n];
        let mut queue = VecDeque::new();
        visited[a] = true;
        queue.push_back(a);

        while let Some(u) = queue.pop_front() {
            if u == b { return true; }
            // Traverse available edges
            for wi in 0..self.words {
                let mut word = self.g_avail_bits[u][wi];
                while word != 0 {
                    let tz = word.trailing_zeros() as usize;
                    let v = wi * 64 + tz;
                    word &= word - 1;
                    if v < self.n && !visited[v] {
                        visited[v] = true;
                        queue.push_back(v);
                    }
                }
            }
        }
        false
    }

    // ===================== FORCED PROPAGATION =====================

    fn do_forced_propagation(&mut self, entry_len: usize) -> PropResult {
        let mut last_deletion_count = usize::MAX; // force connectivity check first
        let mut changed = true;

        while changed {
            changed = false;

            // Rule 1: avail_deg < 2 → dead end
            if self.avail_deg.iter().any(|&d| d < 2) {
                self.undo_to(entry_len);
                return PropResult::Contradiction;
            }

            // Rule 2: locked_degree > 2 → invalid
            if self.locked_degree.iter().any(|&d| d > 2) {
                self.undo_to(entry_len);
                return PropResult::Contradiction;
            }

            // Rule 3: 2-connectivity check on available graph
            // Only rerun when the available graph actually changed
            if self.total_deletions != last_deletion_count {
                let adj = self.build_avail_adj();
                if self.connected_components(&adj) > 1 {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
                if self.has_articulation_point(&adj) {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
                last_deletion_count = self.total_deletions;
            }

            // Rule 4: locked_count constraint
            // If a node v is a neighbour of k different degree-2-available nodes,
            // those k nodes all force their edges onto v. If k > 2, contradiction.
            {
                let mut forced_onto = vec![0usize; self.n];
                for i in 0..self.n {
                    if self.avail_deg[i] == 2 {
                        for wi in 0..self.words {
                            let mut word = self.g_avail_bits[i][wi];
                            while word != 0 {
                                let tz = word.trailing_zeros() as usize;
                                let v = wi * 64 + tz;
                                word &= word - 1;
                                if v < self.n { forced_onto[v] += 1; }
                            }
                        }
                    }
                }
                if forced_onto.iter().any(|&c| c > 2) {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
            }

            // Rule 5a: Degree-2 forcing — if avail_deg[node] == 2 and locked_degree < 2,
            // both available edges must be locked.
            // Rule 5b: Chord deletion — if both endpoints are neighbours and we lock them,
            // the chord between the neighbours would create a premature subcycle.
            // Rule 5c: Saturation — if locked_degree[node] == 2, delete all other avail edges.
            // Rule 5d (NEW): Near-forcing — if avail_deg[node] == 3 and locked_degree[node] == 1,
            // the node has 3 available edges but only 1 more slot. For each available edge e,
            // if locking e would immediately force a contradiction on the other endpoints
            // (the two remaining edges would both need to lock onto a saturated node), we
            // can delete e. This is a lightweight one-step lookahead.
            for node in 0..self.n {
                if self.avail_deg[node] == 2 && self.locked_degree[node] < 2 {
                    let neigh = self.get_avail_neighbors(node);
                    // Force lock both edges
                    for &v in &neigh {
                        let e = Edge(min(node, v), max(node, v));
                        if let Some(&id) = self.edge_id.get(&e) {
                            if !self.is_locked(id) {
                                self.apply_lock(id);
                                changed = true;
                            }
                        }
                    }
                    // Delete chord between the two neighbours
                    if neigh.len() == 2 {
                        let (m1, m2) = (neigh[0], neigh[1]);
                        if m1 != m2 && self.has_edge(m1, m2) {
                            let ec = Edge(min(m1, m2), max(m1, m2));
                            if let Some(&id) = self.edge_id.get(&ec) {
                                if !self.is_locked(id) && !self.is_deleted(id) {
                                    self.apply_delete(id);
                                    changed = true;
                                }
                            }
                        }
                    }
                }

                // Saturation
                if self.locked_degree[node] == 2 && self.avail_deg[node] > 2 {
                    let to_del: Vec<usize> = self.node_edges[node].iter()
                        .copied()
                        .filter(|&id| self.is_active(id))
                        .collect();
                    for id in to_del {
                        self.apply_delete(id);
                        changed = true;
                    }
                }

                // Rule 5d: degree-3 near-forcing
                // If avail_deg == 3 and locked_degree == 1:
                // one of the 3 available edges MUST be chosen. For each candidate edge,
                // if choosing it would saturate the other endpoint (locked_degree would
                // reach 2) AND the other endpoint's remaining available edges would ALL
                // require locking from degree-2 nodes — that's a valid deletion trigger.
                // Simpler version we implement: if an available edge (node, v) would result
                // in v having locked_degree == 2 but v still has active edges beyond these 2,
                // those would be deleted, potentially starving other nodes.
                // We use the cheapest safe version: if locking edge (node→v) would immediately
                // make some third node w have avail_deg < 2 (after the implied saturation
                // deletions cascade once), delete it.
                // This is a one-step lookahead — entirely safe for correctness.
                if self.avail_deg[node] == 3 && self.locked_degree[node] == 1 {
                    let neigh = self.get_avail_neighbors(node);
                    for &v in &neigh {
                        let e = Edge(min(node, v), max(node, v));
                        if let Some(&eid) = self.edge_id.get(&e) {
                            if !self.is_active(eid) { continue; }
                            // Simulate: what happens to v if we lock this edge?
                            // v would get locked_degree += 1.
                            // If v.locked_degree+1 == 2, v saturates → all v's other
                            // available edges get deleted → check if any w adjacent to v
                            // ends up with avail_deg < 2 after that deletion.
                            let v_locked_after = self.locked_degree[v] + 1;
                            if v_locked_after == 2 {
                                // v would saturate. Check its other available neighbours.
                                let v_neigh = self.get_avail_neighbors(v);
                                let mut starvation = false;
                                for &w in &v_neigh {
                                    if w == node { continue; }
                                    // w would lose one available edge (the v-w edge deleted)
                                    if self.avail_deg[w].saturating_sub(1) < 2
                                        && self.locked_degree[w] < 2
                                    {
                                        starvation = true;
                                        break;
                                    }
                                }
                                if starvation {
                                    if !self.is_deleted(eid) {
                                        self.apply_delete(eid);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Rule 6: subcycle / full-cycle detection
            if self.undo_stack.len() > entry_len {
                let gl = self.build_locked_graph();
                if self.has_subcycle(&gl) {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
                if self.is_full_cycle(&gl) {
                    self.best_path = Some(self.collect_locked());
                    return PropResult::Solved;
                }
            }

            // Rule 7 (NEW): Path endpoint connectivity
            // If we have exactly 2 open path endpoints and they cannot reach
            // each other through available edges, this branch is dead.
            if self.path_endpoints.len() == 2 {
                if !self.path_endpoints_connected() {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
            }
        }

        PropResult::Continue
    }

    // ===================== BRANCH VARIABLE SELECTION (MRV) =====================

    fn select_branch_edge(&self) -> Option<usize> {
        // MRV: most-constrained node first
        // Key: avail_deg * 4 - locked_degree (smaller = more constrained)
        let branch_node = (0..self.n)
            .filter(|&v| self.locked_degree[v] < 2 && self.avail_deg[v] >= 2)
            .min_by_key(|&v| (self.avail_deg[v] * 4).saturating_sub(self.locked_degree[v]))?;

        // Among incident edges, prefer fail-first:
        // other endpoint's locked_degree (high = committed) and avail_deg (low = tight)
        let best_id = self.node_edges[branch_node].iter()
            .copied()
            .filter(|&id| self.is_active(id))
            .max_by_key(|&id| {
                let Edge(u, v) = self.all_edges[id];
                let other = if u == branch_node { v } else { u };
                self.locked_degree[other] * 100
                    + 50usize.saturating_sub(self.avail_deg[other])
            })?;

        Some(best_id)
    }

    // ===================== MAIN SEARCH =====================

    fn _search(&mut self) -> bool {
        if self.is_seen() { return false; }

        let entry_len = self.undo_stack.len();

        match self.do_forced_propagation(entry_len) {
            PropResult::Contradiction => { self.memoize(); return false; }
            PropResult::Solved        => { return true; }
            PropResult::Continue      => {}
        }

        // Safety net: all nodes fully locked → verify
        if self.locked_degree.iter().all(|&d| d == 2) {
            let gl = self.build_locked_graph();
            if self.is_connected_iter(&gl) && gl.iter().all(|a| a.len() == 2) {
                self.best_path = Some(self.collect_locked());
                return true;
            }
            self.undo_to(entry_len);
            self.memoize();
            return false;
        }

        let branch_id = match self.select_branch_edge() {
            Some(id) => id,
            None => { self.undo_to(entry_len); self.memoize(); return false; }
        };

        // Branch 1: lock edge
        self.apply_lock(branch_id);
        if self._search() { return true; }
        self.undo();

        // Branch 2: delete edge
        self.apply_delete(branch_id);
        if self._search() { return true; }
        self.undo();

        self.undo_to(entry_len);
        self.memoize();
        false
    }

    // ===================== PUBLIC SOLVE (with timeout) =====================

    fn solve(&mut self) -> Option<Vec<Edge>> {
        // Pre-checks
        if self.is_bipartite() {
            let color = self.get_color();
            let even = color.iter().filter(|&&c| c == 0).count();
            if even != self.n - even { return None; }
        }
        if self.has_bridges_check() { return None; }

        // Reset
        self.locked_bits.fill(0);
        self.deleted_bits.fill(0);
        self.undo_stack.clear();
        self.locked_degree.fill(0);
        self.g_avail_bits.clone_from(&self.orig_bits);
        self.avail_deg.clone_from(&self.orig_deg);
        self.best_path = None;
        self.total_deletions = 0;
        self.memo_cache.clear();
        self.path_endpoints.clear();

        if self._search() { self.best_path.clone() } else { None }
    }

    // Solve with a wall-clock timeout in seconds. Returns None on timeout.
    fn solve_with_timeout(&mut self, timeout_secs: f64) -> SolveResult {
        let start = Instant::now();

        if self.is_bipartite() {
            let color = self.get_color();
            let even = color.iter().filter(|&&c| c == 0).count();
            if even != self.n - even { return SolveResult::Unsat; }
        }
        if self.has_bridges_check() { return SolveResult::Unsat; }

        self.locked_bits.fill(0);
        self.deleted_bits.fill(0);
        self.undo_stack.clear();
        self.locked_degree.fill(0);
        self.g_avail_bits.clone_from(&self.orig_bits);
        self.avail_deg.clone_from(&self.orig_deg);
        self.best_path = None;
        self.total_deletions = 0;
        self.memo_cache.clear();
        self.path_endpoints.clear();

        if self._search_timeout(&start, timeout_secs) {
            if let Some(path) = &self.best_path {
                SolveResult::Sat(path.clone())
            } else {
                SolveResult::Unsat
            }
        } else if start.elapsed().as_secs_f64() >= timeout_secs {
            SolveResult::Timeout
        } else {
            SolveResult::Unsat
        }
    }

    fn _search_timeout(&mut self, start: &Instant, timeout_secs: f64) -> bool {
        if start.elapsed().as_secs_f64() >= timeout_secs { return false; }
        if self.is_seen() { return false; }

        let entry_len = self.undo_stack.len();

        match self.do_forced_propagation(entry_len) {
            PropResult::Contradiction => { self.memoize(); return false; }
            PropResult::Solved        => { return true; }
            PropResult::Continue      => {}
        }

        if self.locked_degree.iter().all(|&d| d == 2) {
            let gl = self.build_locked_graph();
            if self.is_connected_iter(&gl) && gl.iter().all(|a| a.len() == 2) {
                self.best_path = Some(self.collect_locked());
                return true;
            }
            self.undo_to(entry_len);
            self.memoize();
            return false;
        }

        let branch_id = match self.select_branch_edge() {
            Some(id) => id,
            None => { self.undo_to(entry_len); self.memoize(); return false; }
        };

        self.apply_lock(branch_id);
        if self._search_timeout(start, timeout_secs) { return true; }
        self.undo();

        if start.elapsed().as_secs_f64() >= timeout_secs { return false; }

        self.apply_delete(branch_id);
        if self._search_timeout(start, timeout_secs) { return true; }
        self.undo();

        self.undo_to(entry_len);
        self.memoize();
        false
    }

    // ===================== BIPARTITE =====================

    fn is_bipartite(&self) -> bool {
        let mut color = vec![-1i32; self.n];
        for i in 0..self.n {
            if color[i] == -1 && !self.bfs_color(i, &mut color) { return false; }
        }
        true
    }

    fn get_color(&self) -> Vec<i32> {
        let mut color = vec![-1i32; self.n];
        for i in 0..self.n {
            if color[i] == -1 { self.bfs_color(i, &mut color); }
        }
        color
    }

    fn bfs_color(&self, start: usize, color: &mut Vec<i32>) -> bool {
        let mut q = VecDeque::new();
        q.push_back(start); color[start] = 0;
        while let Some(u) = q.pop_front() {
            for &v in &self.g_orig[u] {
                if color[v] == -1 { color[v] = 1 - color[u]; q.push_back(v); }
                else if color[v] == color[u] { return false; }
            }
        }
        true
    }

    // ===================== BRIDGE CHECK (iterative Tarjan) =====================

    fn has_bridges_check(&self) -> bool {
        if self.n == 0 { return false; }
        let g = &self.g_orig;
        let mut disc   = vec![-1i32; self.n];
        let mut low    = vec![ 0i32; self.n];
        let mut parent = vec![-1i32; self.n];
        let mut timer  = 0i32;

        for root in 0..self.n {
            if disc[root] != -1 { continue; }
            disc[root] = timer; low[root] = timer; timer += 1;
            let mut stack: Vec<(usize, usize)> = vec![(root, 0)];

            while let Some((u, ni)) = stack.last_mut() {
                let u = *u;
                if *ni < g[u].len() {
                    let v = g[u][*ni]; *ni += 1;
                    if disc[v] == -1 {
                        parent[v] = u as i32;
                        disc[v] = timer; low[v] = timer; timer += 1;
                        stack.push((v, 0));
                    } else if v as i32 != parent[u] {
                        low[u] = min(low[u], disc[v]);
                    }
                } else {
                    stack.pop();
                    if let Some(&(p, _)) = stack.last() {
                        if low[u] > disc[p] { return true; } // bridge found
                        low[p] = min(low[p], low[u]);
                    }
                }
            }
        }
        false
    }
}

// ===================== SOLVE RESULT =====================

#[derive(Debug)]
enum SolveResult {
    Sat(Vec<Edge>),
    Unsat,
    Timeout,
}

// ===================== VALIDATION =====================

fn validate_cycle(g: &[Vec<usize>], edges: &[Edge]) -> bool {
    let n = g.len();
    if edges.len() != n { return false; }
    let mut adj = vec![vec![]; n];
    for &Edge(u, v) in edges { adj[u].push(v); adj[v].push(u); }
    if !adj.iter().all(|a| a.len() == 2) { return false; }
    // connectivity
    let mut visited = vec![false; n];
    let mut stack = vec![0usize]; visited[0] = true;
    while let Some(u) = stack.pop() {
        for &v in &adj[u] {
            if !visited[v] { visited[v] = true; stack.push(v); }
        }
    }
    visited.iter().all(|&x| x)
}

// ===================== HCP FILE PARSER =====================
// Parses TSPLIB .hcp format:
//   NAME: ...
//   TYPE: HCP
//   DIMENSION: N
//   EDGE_DATA_FORMAT: EDGE_LIST (or ADJ_LIST, we handle both)
//   EDGE_DATA_SECTION
//   u1 v1
//   ...
//   -1
//   EOF
//
// Nodes in HCP files are 1-indexed; we convert to 0-indexed.

fn parse_hcp(path: &Path) -> Result<(String, Vec<Vec<usize>>), String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Cannot read {}: {}", path.display(), e))?;

    let mut name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
    let mut n = 0usize;
    let mut in_edge_section = false;
    let mut edges: Vec<(usize, usize)> = vec![];
    let mut edge_format = "EDGE_LIST"; // default

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') { continue; }

        if line.starts_with("NAME") {
            name = line.splitn(2, ':').nth(1).unwrap_or("").trim().to_string();
            in_edge_section = false;
        } else if line.starts_with("DIMENSION") {
            n = line.splitn(2, ':').nth(1).unwrap_or("0").trim()
                .parse::<usize>().unwrap_or(0);
            in_edge_section = false;
        } else if line.starts_with("EDGE_DATA_FORMAT") {
            edge_format = if line.contains("ADJ_LIST") { "ADJ_LIST" } else { "EDGE_LIST" };
            in_edge_section = false;
        } else if line == "EDGE_DATA_SECTION" {
            in_edge_section = true;
        } else if line == "EOF" {
            break;
        } else if in_edge_section {
            if edge_format == "ADJ_LIST" {
                // format: u v1 v2 ... -1
                let nums: Vec<i64> = line.split_whitespace()
                    .filter_map(|s| s.parse::<i64>().ok())
                    .collect();
                if nums.is_empty() || nums[0] == -1 { continue; }
                let u = (nums[0] as usize) - 1;
                for &v_raw in &nums[1..] {
                    if v_raw == -1 { break; }
                    let v = (v_raw as usize) - 1;
                    if u < v { edges.push((u, v)); }
                }
            } else {
                // EDGE_LIST: u v  (one edge per line, -1 terminates)
                let nums: Vec<i64> = line.split_whitespace()
                    .filter_map(|s| s.parse::<i64>().ok())
                    .collect();
                if nums.len() >= 2 && nums[0] != -1 && nums[1] != -1 {
                    let u = (nums[0] as usize) - 1;
                    let v = (nums[1] as usize) - 1;
                    if u != v {
                        let (a, b) = if u < v { (u, v) } else { (v, u) };
                        edges.push((a, b));
                    }
                } else if nums.len() == 1 && nums[0] == -1 {
                    in_edge_section = false;
                }
            }
        }
    }

    if n == 0 { return Err(format!("DIMENSION not found in {}", path.display())); }

    let mut g = vec![vec![]; n];
    for (u, v) in edges {
        if u < n && v < n {
            g[u].push(v);
            g[v].push(u);
        }
    }
    // Deduplicate adjacency lists (some HCP files have duplicate edges)
    for u in 0..n {
        g[u].sort_unstable();
        g[u].dedup();
    }

    Ok((name, g))
}

// ===================== GRAPH GENERATORS =====================

fn get_tutte_graph() -> Vec<Vec<usize>> {
    let n = 46;
    let mut g = vec![vec![]; n];
    let edges = [
        (0,1),(0,2),(0,3),(1,4),(1,26),(2,10),(2,11),(3,18),(3,19),(4,5),(4,33),(5,6),(5,29),
        (6,7),(6,27),(7,8),(7,14),(8,9),(8,38),(9,10),(9,37),(10,39),(11,12),(11,39),(12,13),
        (12,35),(13,14),(13,15),(14,34),(15,16),(15,22),(16,17),(16,44),(17,18),(17,43),(18,45),
        (19,20),(19,45),(20,21),(20,41),(21,22),(21,23),(22,40),(23,24),(23,27),(24,25),(24,32),
        (25,26),(25,31),(26,33),(27,28),(28,29),(28,32),(29,30),(30,31),(30,33),(31,32),(34,35),
        (34,38),(35,36),(36,37),(36,39),(37,38),(40,41),(40,44),(41,42),(42,43),(42,45),(43,44),
    ];
    for (u, v) in edges { g[u].push(v); g[v].push(u); }
    g
}

fn get_petersen_graph() -> Vec<Vec<usize>> {
    let n = 10;
    let mut g = vec![vec![]; n];
    let edges = [
        (0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
        (0,5),(1,6),(2,7),(3,8),(4,9),
    ];
    for (u, v) in edges { g[u].push(v); g[v].push(u); }
    g
}

fn get_heawood_graph() -> Vec<Vec<usize>> {
    let n = 14;
    let mut g = vec![vec![]; n];
    let lines = [
        [0,1,2],[0,3,5],[0,4,6],[1,3,6],[1,4,5],[2,3,4],[2,5,6],
    ];
    for (l, pts) in lines.iter().enumerate() {
        for &p in pts { let ln = l + 7; g[p].push(ln); g[ln].push(p); }
    }
    g
}

fn get_desargues_graph() -> Vec<Vec<usize>> {
    let n = 20;
    let mut g = vec![vec![]; n];
    let edges = [
        (0,1),(0,5),(0,19),(1,2),(1,16),(2,3),(2,11),(3,4),(3,14),(4,5),(4,9),(5,6),(6,7),
        (6,15),(7,8),(7,18),(8,9),(8,13),(9,10),(10,11),(10,19),(11,12),(12,13),(12,17),
        (13,14),(14,15),(15,16),(16,17),(17,18),(18,19),
    ];
    for (u, v) in edges { g[u].push(v); g[v].push(u); }
    g
}

fn get_dodecahedral_graph() -> Vec<Vec<usize>> {
    let n = 20;
    let mut g = vec![vec![]; n];
    let adjs = [
        1,4,7, 0,2,9, 1,3,11, 2,3,13, 0,3,5, 4,6,14, 5,7,16, 0,6,8,
        7,9,17, 1,8,10, 9,11,18, 2,10,12, 11,13,19, 3,12,14, 5,13,15,
        14,16,19, 6,15,17, 8,16,18, 10,17,19, 12,15,18usize,
    ];
    for i in 0..20 { for j in 0..3 { g[i].push(adjs[i*3+j]); } }
    g
}

fn get_hypercube_graph(dim: usize) -> Vec<Vec<usize>> {
    let nn = 1 << dim;
    let mut g = vec![vec![]; nn];
    for i in 0..nn { for j in 0..dim { g[i].push(i ^ (1 << j)); } }
    g
}

fn get_grid_graph(rows: usize, cols: usize) -> Vec<Vec<usize>> {
    let nn = rows * cols;
    let mut g = vec![vec![]; nn];
    for i in 0..rows {
        for j in 0..cols {
            let u = i * cols + j;
            if j + 1 < cols { let v = u+1; g[u].push(v); g[v].push(u); }
            if i + 1 < rows { let v = u+cols; g[u].push(v); g[v].push(u); }
        }
    }
    g
}

fn get_complete_graph(nn: usize) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; nn];
    for i in 0..nn { for j in i+1..nn { g[i].push(j); g[j].push(i); } }
    g
}

fn get_wheel_graph(nn: usize) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; nn];
    for i in 1..nn { g[0].push(i); g[i].push(0); }
    for i in 1..nn-1 { g[i].push(i+1); g[i+1].push(i); }
    g[1].push(nn-1); g[nn-1].push(1);
    g
}

fn get_circular_ladder_graph(k: usize) -> Vec<Vec<usize>> {
    let nn = 2*k;
    let mut g = vec![vec![]; nn];
    for i in 0..k {
        let next = (i+1)%k;
        g[i].push(next); g[next].push(i);
        let inner = i+k; let inner_next = (i+1)%k+k;
        g[inner].push(inner_next); g[inner_next].push(inner);
        g[i].push(inner); g[inner].push(i);
    }
    g
}

fn get_complete_bipartite(a: usize, b: usize) -> Vec<Vec<usize>> {
    let nn = a+b;
    let mut g = vec![vec![]; nn];
    for i in 0..a { for j in 0..b { let v=j+a; g[i].push(v); g[v].push(i); } }
    g
}

fn get_star_graph(k: usize) -> Vec<Vec<usize>> {
    let nn = k+1;
    let mut g = vec![vec![]; nn];
    for i in 1..=k { g[0].push(i); g[i].push(0); }
    g
}

fn get_barbell_graph(m1: usize) -> Vec<Vec<usize>> {
    let nn = 2*m1;
    let mut g = vec![vec![]; nn];
    for i in 0..m1 { for j in i+1..m1 { g[i].push(j); g[j].push(i); } }
    for i in m1..nn { for j in i+1..nn { g[i].push(j); g[j].push(i); } }
    g[m1-1].push(m1); g[m1].push(m1-1);
    g
}

fn get_knight_graph(rows: usize, cols: usize) -> Vec<Vec<usize>> {
    let deltas: [(isize,isize);8] = [(-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)];
    let n = rows*cols;
    let mut g = vec![vec![]; n];
    for r in 0..rows {
        for c in 0..cols {
            let u = r*cols+c;
            for &(dr,dc) in &deltas {
                let nr = r as isize+dr; let nc = c as isize+dc;
                if nr>=0 && nr<rows as isize && nc>=0 && nc<cols as isize {
                    g[u].push(nr as usize*cols+nc as usize);
                }
            }
        }
    }
    g
}

fn get_random_graph(nn: usize, p: f64) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; nn];
    let mut rng = thread_rng();
    let dist = Uniform::from(0.0..1.0);
    for i in 0..nn {
        for j in i+1..nn {
            if rng.sample(dist) < p { g[i].push(j); g[j].push(i); }
        }
    }
    g
}

fn is_connected_free(g: &[Vec<usize>], n: usize) -> bool {
    if n == 0 { return true; }
    let mut visited = vec![false; n];
    let mut stack = vec![0usize]; visited[0] = true;
    while let Some(u) = stack.pop() {
        for &v in &g[u] {
            if !visited[v] { visited[v] = true; stack.push(v); }
        }
    }
    visited.iter().all(|&x| x)
}

// ===================== TEST SUITES =====================

fn verify_carver_integrity() {
    println!("{:<32} | {:<5} | {:<10} | {:<10} | {:<9} | Status",
             "Graph", "N", "Expected", "Result", "Time(s)");
    println!("{}", "-".repeat(85));

    let tests: &[(&str, &dyn Fn() -> Vec<Vec<usize>>, &str)] = &[
        ("Petersen (UNSAT)",          &get_petersen_graph,              "UNSAT"),
        ("Tutte (UNSAT)",             &get_tutte_graph,                 "UNSAT"),
        ("8x8 Grid (SAT)",            &(|| get_grid_graph(8,8)),        "SAT"),
        ("Heawood (SAT)",             &get_heawood_graph,               "SAT"),
        ("Hypercube Q4 (SAT)",        &(|| get_hypercube_graph(4)),     "SAT"),
        ("Dodecahedral (SAT)",        &get_dodecahedral_graph,          "SAT"),
        ("Desargues (SAT)",           &get_desargues_graph,             "SAT"),
        ("Complete K15 (SAT)",        &(|| get_complete_graph(15)),     "SAT"),
        ("Wheel W20 (SAT)",           &(|| get_wheel_graph(20)),        "SAT"),
        ("Circular Ladder 10 (SAT)",  &(|| get_circular_ladder_graph(10)), "SAT"),
        ("Bipartite K5,6 (UNSAT)",    &(|| get_complete_bipartite(5,6)),"UNSAT"),
        ("Star S8 (UNSAT)",           &(|| get_star_graph(8)),          "UNSAT"),
        ("7x7 Grid (UNSAT)",          &(|| get_grid_graph(7,7)),        "UNSAT"),
        ("Barbell B8 (UNSAT)",        &(|| get_barbell_graph(8)),       "UNSAT"),
        ("5x5 Knight (UNSAT)",        &(|| get_knight_graph(5,5)),      "UNSAT"),
        // Additional adversarial cases
        ("10x10 Grid (SAT)",          &(|| get_grid_graph(10,10)),      "SAT"),
        ("11x11 Grid (UNSAT)",        &(|| get_grid_graph(11,11)),      "UNSAT"),
        ("Hypercube Q5 (SAT)",        &(|| get_hypercube_graph(5)),     "SAT"),
        ("Complete K20 (SAT)",        &(|| get_complete_graph(20)),     "SAT"),
        ("Circular Ladder 30 (SAT)",  &(|| get_circular_ladder_graph(30)), "SAT"),
    ];

    let mut pass = 0usize;
    let mut fail = 0usize;

    for &(name, maker, expected) in tests {
        let g = maker();
        let n = g.len();
        let mut solver = BcCraver::new(&g);
        let start = Instant::now();
        let path = solver.solve();
        let dur = start.elapsed().as_secs_f64();
        let result = if path.is_some() { "SAT" } else { "UNSAT" };
        let status = if result == expected {
            if result == "SAT" {
                if validate_cycle(&g, path.as_deref().unwrap_or(&[])) {
                    pass += 1; "✅ PASS"
                } else {
                    fail += 1; "❌ INVALID"
                }
            } else {
                pass += 1; "✅ PASS"
            }
        } else {
            fail += 1;
            if result == "UNSAT" { "❌ FALSE-UNSAT" } else { "❌ FALSE-SAT" }
        };
        println!("{:<32} | {:<5} | {:<10} | {:<10} | {:<9.5} | {}",
                 name, n, expected, result, dur, status);
    }
    println!("\nResult: {}/{} passed\n", pass, pass+fail);
}

fn run_random_audit(start_n: usize, end_n: usize, p_override: Option<f64>) {
    println!("{:<5} | {:<7} | {:<12} | {:<10} | {:<6} | Status",
             "N", "Edges", "Time(s)", "Cache", "p");
    println!("{}", "-".repeat(65));

    for nn in start_n..=end_n {
        let p_hard = ((nn as f64).ln()
            + ((nn as f64).ln().ln().max(0.0) + 1e-9)) / (nn as f64);
        let p = p_override.unwrap_or(p_hard.max(0.08));

        let mut g = get_random_graph(nn, p);
        let mut attempts = 0;
        while !is_connected_free(&g, nn) && attempts < 100 {
            g = get_random_graph(nn, p);
            attempts += 1;
        }

        let mut solver = BcCraver::new(&g);
        let start = Instant::now();
        let result = solver.solve_with_timeout(60.0);
        let dur = start.elapsed().as_secs_f64();
        let edges_num: usize = g.iter().map(|a| a.len()).sum::<usize>() / 2;
        let cache = solver.get_memo_size();
        let status = match &result {
            SolveResult::Sat(_)  => "Solved",
            SolveResult::Unsat   => "UNSAT",
            SolveResult::Timeout => "TIMEOUT",
        };
        println!("{:<5} | {:<7} | {:<12.5} | {:<10} | {:<6.4} | {}",
                 nn, edges_num, dur, cache, p, status);
    }
}

// ===================== FHCP BENCHMARK RUNNER =====================

fn run_fhcp_benchmark(dir: &Path, timeout_secs: f64) {
    // Find all .hcp files
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(e) => { eprintln!("Cannot open directory {}: {}", dir.display(), e); return; }
    };

    let mut hcp_files: Vec<std::path::PathBuf> = entries
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("hcp"))
        .collect();
    hcp_files.sort();

    if hcp_files.is_empty() {
        eprintln!("No .hcp files found in {}", dir.display());
        eprintln!("Download the FHCP benchmark from:");
        eprintln!("  http://www.flinders.edu.au/science_engineering/csem/research/programs/flinders-hamiltonian-cycle-project/");
        return;
    }

    println!("{:<30} | {:<6} | {:<7} | {:<12} | {:<10} | Status",
             "Instance", "N", "Edges", "Time(s)", "Cache");
    println!("{}", "-".repeat(85));

    let mut sat_count    = 0usize;
    let mut unsat_count  = 0usize;
    let mut timeout_count = 0usize;
    let mut total_time   = 0f64;

    for path in &hcp_files {
        let (name, g) = match parse_hcp(path) {
            Ok(x) => x,
            Err(e) => { eprintln!("Parse error: {}", e); continue; }
        };

        let n = g.len();
        let edges_num: usize = g.iter().map(|a| a.len()).sum::<usize>() / 2;
        let mut solver = BcCraver::new(&g);
        let start = Instant::now();
        let result = solver.solve_with_timeout(timeout_secs);
        let dur = start.elapsed().as_secs_f64();
        let cache = solver.get_memo_size();
        total_time += dur;

        let (status_str, valid_str) = match &result {
            SolveResult::Sat(edges) => {
                sat_count += 1;
                let valid = validate_cycle(&g, edges);
                let v = if valid { "✅ SAT" } else { "❌ INVALID" };
                (v, "")
            }
            SolveResult::Unsat   => { unsat_count += 1;   ("UNSAT",   "") }
            SolveResult::Timeout => { timeout_count += 1; ("TIMEOUT", "") }
        };
        let _ = valid_str;

        println!("{:<30} | {:<6} | {:<7} | {:<12.5} | {:<10} | {}",
                 &name[..name.len().min(30)], n, edges_num, dur, cache, status_str);
    }

    println!("\n{}", "=".repeat(85));
    println!("Total instances: {}", hcp_files.len());
    println!("SAT:     {}", sat_count);
    println!("UNSAT:   {}", unsat_count);
    println!("TIMEOUT: {} (limit: {}s each)", timeout_count, timeout_secs);
    println!("Total solve time: {:.2}s", total_time);
    println!("Solved (non-timeout): {}/{}",
             sat_count + unsat_count, hcp_files.len());
}

fn run_single_hcp(path: &Path, timeout_secs: f64) {
    let (name, g) = match parse_hcp(path) {
        Ok(x) => x,
        Err(e) => { eprintln!("{}", e); return; }
    };

    let n = g.len();
    let edges_num: usize = g.iter().map(|a| a.len()).sum::<usize>() / 2;
    println!("Instance: {}  N={}  Edges={}", name, n, edges_num);

    let mut solver = BcCraver::new(&g);
    let start = Instant::now();
    let result = solver.solve_with_timeout(timeout_secs);
    let dur = start.elapsed().as_secs_f64();

    match result {
        SolveResult::Sat(edges) => {
            let valid = validate_cycle(&g, &edges);
            println!("Result:  SAT  ({:.5}s)  valid={}", dur, valid);
            if valid {
                println!("Cycle length: {} edges", edges.len());
            }
        }
        SolveResult::Unsat   => println!("Result:  UNSAT  ({:.5}s)", dur),
        SolveResult::Timeout => println!("Result:  TIMEOUT after {:.1}s", timeout_secs),
    }
    println!("Cache entries: {}", solver.get_memo_size());
}

// ===================== MAIN =====================

fn main() {
    let args: Vec<String> = env::args().collect();

    match args.len() {
        // No arguments: run built-in test suite + random audit
        1 => {
            verify_carver_integrity();
            println!("=== Random Audit (p = p_hard threshold) ===\n");
            run_random_audit(100, 600, None);
        }

        // Single .hcp file
        2 if args[1].ends_with(".hcp") => {
            run_single_hcp(Path::new(&args[1]), 300.0);
        }

        // --fhcp <directory> [timeout_secs]
        _ if args.get(1).map(|s| s.as_str()) == Some("--fhcp") => {
            let dir = Path::new(args.get(2).map(|s| s.as_str()).unwrap_or("."));
            let timeout: f64 = args.get(3)
                .and_then(|s| s.parse().ok())
                .unwrap_or(120.0);
            run_fhcp_benchmark(dir, timeout);
        }

        // --random [start_n] [end_n] [p]
        _ if args.get(1).map(|s| s.as_str()) == Some("--random") => {
            let start_n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
            let end_n:   usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(1000);
            let p_opt: Option<f64> = args.get(4).and_then(|s| s.parse().ok());
            run_random_audit(start_n, end_n, p_opt);
        }

        _ => {
            eprintln!("Usage:");
            eprintln!("  bc_craver                          (built-in test suite)");
            eprintln!("  bc_craver file.hcp                 (solve one file)");
            eprintln!("  bc_craver --fhcp <dir> [timeout]   (run FHCP benchmark)");
            eprintln!("  bc_craver --random [start] [end] [p]  (random audit)");
        }
    }
}
