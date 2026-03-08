use std::collections::{HashMap, HashSet, VecDeque};
use std::time::Instant;
use rand::distributions::Uniform;
use rand::prelude::*;
use std::cmp::{max, min};

#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
struct Edge(usize, usize);

#[derive(Copy, Clone)]
enum Change {
    Lock(usize),
    Delete(usize),
}

struct BcCraver {
    n: usize,
    g_orig: Vec<Vec<usize>>,
    memo_cache: HashMap<(Vec<u64>, Vec<u64>), ()>,
    best_path: Option<Vec<Edge>>,
    all_edges: Vec<Edge>,
    edge_id: HashMap<Edge, usize>,
    // Adjacency list per node: node -> list of edge ids (not neighbour ids)
    // Used for O(deg) iteration without rebuilding adj lists
    node_edges: Vec<Vec<usize>>,
    locked_bits: Vec<u64>,
    deleted_bits: Vec<u64>,
    undo_stack: Vec<Change>,
    locked_degree: Vec<usize>,
    total_deletions: usize,
    words: usize,
    g_avail_bits: Vec<Vec<u64>>,
    avail_deg: Vec<usize>,
    orig_bits: Vec<Vec<u64>>,
    orig_deg: Vec<usize>,
}

impl BcCraver {
    fn new(g: &[Vec<usize>]) -> Self {
        let n = g.len();

        let mut edge_set: HashSet<Edge> = HashSet::new();
        for u in 0..n {
            for &v in &g[u] {
                if u < v {
                    edge_set.insert(Edge(u, v));
                }
            }
        }
        let all_edges: Vec<Edge> = edge_set.into_iter().collect();
        let mut edge_id: HashMap<Edge, usize> = HashMap::new();
        for (i, &e) in all_edges.iter().enumerate() {
            edge_id.insert(e, i);
        }
        let m = all_edges.len();
        let num_words = (m * 2 + 63) / 64;

        // Build per-node edge-id lists for O(deg) traversal
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
                let w = v / 64;
                let b = v % 64;
                if w < words {
                    g_avail_bits[u][w] |= 1u64 << b;
                }
            }
        }
        let orig_bits = g_avail_bits.clone();
        let orig_deg = avail_deg.clone();

        BcCraver {
            n,
            g_orig: g.to_vec(),
            memo_cache: HashMap::new(),
            best_path: None,
            all_edges,
            edge_id,
            node_edges,
            locked_bits: vec![0u64; num_words],
            deleted_bits: vec![0u64; num_words],
            undo_stack: vec![],
            locked_degree: vec![0; n],
            total_deletions: 0,
            words,
            g_avail_bits,
            avail_deg,
            orig_bits,
            orig_deg,
        }
    }

    #[inline]
    fn is_locked(&self, id: usize) -> bool {
        let word = (id * 2) / 64;
        let bit = (id * 2) % 64;
        (self.locked_bits[word] & (1u64 << bit)) != 0
    }

    #[inline]
    fn is_deleted(&self, id: usize) -> bool {
        let word = (id * 2 + 1) / 64;
        let bit = (id * 2 + 1) % 64;
        (self.deleted_bits[word] & (1u64 << bit)) != 0
    }

    #[inline]
    fn is_active(&self, id: usize) -> bool {
        !self.is_locked(id) && !self.is_deleted(id)
    }

    fn apply_lock(&mut self, id: usize) {
        let word = (id * 2) / 64;
        let bit = (id * 2) % 64;
        self.locked_bits[word] |= 1u64 << bit;
        let Edge(u, v) = self.all_edges[id];
        self.locked_degree[u] += 1;
        self.locked_degree[v] += 1;
        self.undo_stack.push(Change::Lock(id));
    }

    #[inline]
    fn clear_bit(&mut self, u: usize, v: usize) {
        let w = v / 64;
        let b = v % 64;
        if w < self.words {
            self.g_avail_bits[u][w] &= !(1u64 << b);
        }
    }

    #[inline]
    fn set_bit(&mut self, u: usize, v: usize) {
        let w = v / 64;
        let b = v % 64;
        if w < self.words {
            self.g_avail_bits[u][w] |= 1u64 << b;
        }
    }

    fn apply_delete(&mut self, id: usize) {
        let word = (id * 2 + 1) / 64;
        let bit = (id * 2 + 1) % 64;
        self.deleted_bits[word] |= 1u64 << bit;
        self.undo_stack.push(Change::Delete(id));

        let Edge(u, v) = self.all_edges[id];
        self.clear_bit(u, v);
        self.clear_bit(v, u);
        self.avail_deg[u] -= 1;
        self.avail_deg[v] -= 1;
        self.total_deletions += 1;
    }

    fn undo(&mut self) {
        if let Some(ch) = self.undo_stack.pop() {
            match ch {
                Change::Lock(id) => {
                    let word = (id * 2) / 64;
                    let bit = (id * 2) % 64;
                    self.locked_bits[word] &= !(1u64 << bit);
                    let Edge(u, v) = self.all_edges[id];
                    self.locked_degree[u] -= 1;
                    self.locked_degree[v] -= 1;
                }
                Change::Delete(id) => {
                    let word = (id * 2 + 1) / 64;
                    let bit = (id * 2 + 1) % 64;
                    self.deleted_bits[word] &= !(1u64 << bit);
                    let Edge(u, v) = self.all_edges[id];
                    self.set_bit(u, v);
                    self.set_bit(v, u);
                    self.avail_deg[u] += 1;
                    self.avail_deg[v] += 1;
                    self.total_deletions -= 1;
                }
            }
        }
    }

    fn undo_to(&mut self, target: usize) {
        while self.undo_stack.len() > target {
            self.undo();
        }
    }

    fn memoize(&mut self) {
        let key = (self.locked_bits.clone(), self.deleted_bits.clone());
        self.memo_cache.insert(key, ());
    }

    fn build_locked_graph(&self) -> Vec<Vec<usize>> {
        let mut gl: Vec<Vec<usize>> = vec![vec![]; self.n];
        for (id, &Edge(u, v)) in self.all_edges.iter().enumerate() {
            if self.is_locked(id) {
                gl[u].push(v);
                gl[v].push(u);
            }
        }
        gl
    }

    fn collect_locked(&self) -> Vec<Edge> {
        self.all_edges.iter().enumerate()
            .filter(|&(id, _)| self.is_locked(id))
            .map(|(_, &e)| e)
            .collect()
    }

    #[inline]
    fn has_edge(&self, u: usize, v: usize) -> bool {
        if v >= self.n { return false; }
        let w = v / 64;
        let b = v % 64;
        (self.g_avail_bits[u][w] & (1u64 << b)) != 0
    }

    fn get_avail_neighbors(&self, u: usize) -> Vec<usize> {
        let mut res = Vec::with_capacity(self.avail_deg[u]);
        for wi in 0..self.words {
            let mut word = self.g_avail_bits[u][wi];
            while word != 0 {
                let tz = word.trailing_zeros() as usize;
                let v = wi * 64 + tz;
                if v < self.n {
                    res.push(v);
                }
                word &= word - 1;
            }
        }
        res
    }

    fn build_avail_adj(&self) -> Vec<Vec<usize>> {
        (0..self.n).map(|u| self.get_avail_neighbors(u)).collect()
    }

    fn solve(&mut self) -> Option<Vec<Edge>> {
        // Fast pre-checks before any search
        if self.is_bipartite() {
            let color = self.get_color();
            let even = color.iter().filter(|&&c| c == 0).count();
            let odd = self.n - even;
            if even != odd {
                return None;
            }
        }
        if self.has_bridges() {
            return None;
        }

        // Reset state
        self.locked_bits.fill(0);
        self.deleted_bits.fill(0);
        self.undo_stack.clear();
        self.locked_degree.fill(0);
        self.g_avail_bits.clone_from(&self.orig_bits);
        self.avail_deg.clone_from(&self.orig_deg);
        self.best_path = None;
        self.total_deletions = 0;
        self.memo_cache.clear();

        if self._search() {
            return self.best_path.clone();
        }
        None
    }

    // ===================== FORCED PROPAGATION =====================
    // Returns false if a contradiction was found (and undoes to entry_len).
    // Returns true if propagation completed without contradiction.
    // Sets self.best_path and returns true if a full cycle was found.
    fn do_forced_propagation(&mut self, entry_len: usize) -> PropResult {
        let mut last_ap_deletions = usize::MAX; // force AP check first iteration
        let mut changed = true;

        while changed {
            changed = false;

            // --- Rule 1: any node with avail_deg < 2 is a dead end ---
            if self.avail_deg.iter().any(|&d| d < 2) {
                self.undo_to(entry_len);
                return PropResult::Contradiction;
            }

            // --- Rule 2: locked_degree > 2 is invalid ---
            if self.locked_degree.iter().any(|&d| d > 2) {
                self.undo_to(entry_len);
                return PropResult::Contradiction;
            }

            // --- Rule 3: 2-connectivity of available graph ---
            // Only recheck when deletions happened since last check
            if self.total_deletions != last_ap_deletions {
                let current_adj = self.build_avail_adj();
                if self.number_connected_components(&current_adj) > 1 {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
                if !self.get_articulation_points(&current_adj).is_empty() {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
                last_ap_deletions = self.total_deletions;
            }

            // --- Rule 4: locket_count constraint ---
            // A node v that appears as a neighbour of too many degree-2 nodes
            // would need more than 2 locked edges → contradiction.
            let mut locket_count: Vec<usize> = vec![0; self.n];
            for i in 0..self.n {
                if self.avail_deg[i] == 2 {
                    let neigh = self.get_avail_neighbors(i);
                    for &v in &neigh {
                        locket_count[v] += 1;
                    }
                }
            }
            if locket_count.iter().any(|&c| c > 2) {
                self.undo_to(entry_len);
                return PropResult::Contradiction;
            }

            // --- Rule 5: degree-2 forcing + chord deletion + saturation ---
            for node in 0..self.n {
                // Force both edges if avail_deg == 2 and not yet fully locked
                if self.avail_deg[node] == 2 && self.locked_degree[node] < 2 {
                    let neigh = self.get_avail_neighbors(node);
                    for &v in &neigh {
                        let e = Edge(min(node, v), max(node, v));
                        if let Some(&id) = self.edge_id.get(&e) {
                            if !self.is_locked(id) {
                                self.apply_lock(id);
                                changed = true;
                            }
                        }
                    }
                    // Delete the chord between the two neighbours (would create subcycle)
                    if neigh.len() == 2 {
                        let m1 = neigh[0];
                        let m2 = neigh[1];
                        if m1 != m2 && self.has_edge(m1, m2) {
                            let e_chord = Edge(min(m1, m2), max(m1, m2));
                            if let Some(&id) = self.edge_id.get(&e_chord) {
                                if !self.is_locked(id) && !self.is_deleted(id) {
                                    self.apply_delete(id);
                                    changed = true;
                                }
                            }
                        }
                    }
                }

                // Saturate: node already has 2 locked edges → delete all others
                if self.locked_degree[node] == 2 && self.avail_deg[node] > 2 {
                    // Collect ids first to avoid borrow issues
                    let to_delete: Vec<usize> = self.node_edges[node].iter()
                        .copied()
                        .filter(|&id| self.is_active(id))
                        .collect();
                    for id in to_delete {
                        self.apply_delete(id);
                        changed = true;
                    }
                }
            }

            // --- Rule 6: subcycle / full-cycle detection ---
            if self.undo_stack.len() > entry_len {
                let g_locked = self.build_locked_graph();
                if self.has_subcycle(&g_locked) {
                    self.undo_to(entry_len);
                    return PropResult::Contradiction;
                }
                if self.is_full_cycle(&g_locked) {
                    self.best_path = Some(self.collect_locked());
                    return PropResult::Solved;
                }
            }
        }
        PropResult::Continue
    }

    // ===================== BRANCH VARIABLE SELECTION =====================
    // MRV (Minimum Remaining Values): find the tightest node first.
    // "Tightness" = avail_deg - (2 - locked_degree), i.e. how many free slots remain
    // for how many available edges. The node with the smallest ratio is most constrained.
    // Among edges touching that node, prefer the one whose other endpoint has the highest
    // locked_degree (fail-first: resolve already-committed paths first).
    fn select_branch_edge(&self) -> Option<usize> {
        // Find the most-constrained node that still needs locked edges
        // remaining_slots = 2 - locked_degree[node]  (how many more locks it needs)
        // avail_deg[node] = how many edges it can still choose from
        // We want: min avail_deg among nodes with locked_degree < 2 and avail_deg >= 2
        let branch_node = (0..self.n)
            .filter(|&v| self.locked_degree[v] < 2 && self.avail_deg[v] >= 2)
            .min_by_key(|&v| {
                // Primary: smallest avail_deg (most constrained — MRV)
                // Secondary: largest locked_degree (prefer nodes already on a partial path)
                // Pack both into a single key: (avail_deg * 4) - locked_degree
                // so smaller avail_deg wins, ties broken by larger locked_degree
                (self.avail_deg[v] * 4).saturating_sub(self.locked_degree[v])
            })?;

        // Among edges incident to branch_node, find the best one using fail-first:
        // prefer the edge whose other endpoint has the highest locked_degree
        // (that endpoint is most committed and benefits most from resolving this edge)
        let best_id = self.node_edges[branch_node].iter()
            .copied()
            .filter(|&id| self.is_active(id))
            .max_by_key(|&id| {
                let Edge(u, v) = self.all_edges[id];
                let other = if u == branch_node { v } else { u };
                // Score: locked_degree of other endpoint * 100 + (avail_deg inversely)
                // Higher locked_degree = more committed = resolve first
                // Lower avail_deg of other end = tighter = prefer
                let lock_score = self.locked_degree[other] * 100;
                let tight_score = 50usize.saturating_sub(self.avail_deg[other]);
                lock_score + tight_score
            })?;

        Some(best_id)
    }

    // ===================== MAIN SEARCH =====================
    fn _search(&mut self) -> bool {
        // Transposition table: exact-match check
        let key = (self.locked_bits.clone(), self.deleted_bits.clone());
        if self.memo_cache.contains_key(&key) {
            return false;
        }

        let entry_len = self.undo_stack.len();

        match self.do_forced_propagation(entry_len) {
            PropResult::Contradiction => {
                self.memoize();
                return false;
            }
            PropResult::Solved => {
                return true;
            }
            PropResult::Continue => {}
        }

        // Check if all nodes are already satisfied (shouldn't be needed after propagation
        // but acts as a safety net)
        if self.locked_degree.iter().all(|&d| d == 2) {
            let g_locked = self.build_locked_graph();
            if self.is_connected(&g_locked) && self.all_degree2(&g_locked) {
                self.best_path = Some(self.collect_locked());
                return true;
            }
        }

        // Select branch edge via MRV + fail-first heuristic
        let branch_id = match self.select_branch_edge() {
            Some(id) => id,
            None => {
                // No active edges left but not solved
                self.undo_to(entry_len);
                self.memoize();
                return false;
            }
        };

        // Branch 1: lock this edge (include it in the cycle)
        self.apply_lock(branch_id);
        if self._search() {
            return true;
        }
        self.undo();

        // Branch 2: delete this edge (exclude it from the cycle)
        self.apply_delete(branch_id);
        if self._search() {
            return true;
        }
        self.undo();

        self.undo_to(entry_len);
        self.memoize();
        false
    }

    // ===================== GRAPH HELPERS =====================

    fn is_connected(&self, g: &[Vec<usize>]) -> bool {
        if self.n == 0 { return true; }
        let mut visited = vec![false; self.n];
        let mut stack: Vec<usize> = vec![0];
        visited[0] = true;
        while let Some(u) = stack.pop() {
            for &v in &g[u] {
                if !visited[v] {
                    visited[v] = true;
                    stack.push(v);
                }
            }
        }
        visited.iter().all(|&v| v)
    }

    fn number_connected_components(&self, g: &[Vec<usize>]) -> usize {
        let mut visited = vec![false; self.n];
        let mut count = 0;
        for i in 0..self.n {
            if !visited[i] {
                count += 1;
                let mut stack: Vec<usize> = vec![i];
                visited[i] = true;
                while let Some(u) = stack.pop() {
                    for &v in &g[u] {
                        if !visited[v] {
                            visited[v] = true;
                            stack.push(v);
                        }
                    }
                }
            }
        }
        count
    }

    fn has_subcycle(&self, g_locked: &[Vec<usize>]) -> bool {
        let mut visited = vec![false; self.n];
        for i in 0..self.n {
            if !visited[i] {
                let mut component: Vec<usize> = vec![];
                let mut stack: Vec<usize> = vec![i];
                visited[i] = true;
                component.push(i);
                while let Some(curr) = stack.pop() {
                    for &v in &g_locked[curr] {
                        if !visited[v] {
                            visited[v] = true;
                            component.push(v);
                            stack.push(v);
                        }
                    }
                }
                let comp_size = component.len();
                // A subcycle: all nodes in this component have degree 2 in locked graph
                // but the component doesn't span the whole graph
                if comp_size < self.n && component.iter().all(|&u| g_locked[u].len() == 2) {
                    return true;
                }
            }
        }
        false
    }

    fn is_full_cycle(&self, g_locked: &[Vec<usize>]) -> bool {
        self.is_connected(g_locked) && self.all_degree2(g_locked)
    }

    fn all_degree2(&self, g: &[Vec<usize>]) -> bool {
        g.iter().all(|adj| adj.len() == 2)
    }

    fn get_memo_size(&self) -> usize {
        self.memo_cache.len()
    }

    // ===================== BIPARTITE CHECK =====================

    fn is_bipartite(&self) -> bool {
        let mut color: Vec<i32> = vec![-1; self.n];
        for i in 0..self.n {
            if color[i] == -1 && !self.bfs_color(i, &mut color) {
                return false;
            }
        }
        true
    }

    fn get_color(&self) -> Vec<i32> {
        let mut color: Vec<i32> = vec![-1; self.n];
        for i in 0..self.n {
            if color[i] == -1 {
                self.bfs_color(i, &mut color);
            }
        }
        color
    }

    fn bfs_color(&self, start: usize, color: &mut Vec<i32>) -> bool {
        let mut q: VecDeque<usize> = VecDeque::new();
        q.push_back(start);
        color[start] = 0;
        while let Some(u) = q.pop_front() {
            for &v in &self.g_orig[u] {
                if color[v] == -1 {
                    color[v] = 1 - color[u];
                    q.push_back(v);
                } else if color[v] == color[u] {
                    return false;
                }
            }
        }
        true
    }

    // ===================== BRIDGE CHECK (recursive Tarjan — only called once on g_orig) =====================

    fn has_bridges(&self) -> bool {
        !self.get_bridges(&self.g_orig).is_empty()
    }

    fn get_bridges(&self, g: &[Vec<usize>]) -> Vec<Edge> {
        let mut disc = vec![-1i32; self.n];
        let mut low = vec![-1i32; self.n];
        let mut parent = vec![-1i32; self.n];
        let mut time_stamp = 0;
        let mut bridges = vec![];
        for i in 0..self.n {
            if disc[i] == -1 {
                self.dfs_bridges(i, g, &mut disc, &mut low, &mut parent, &mut time_stamp, &mut bridges);
            }
        }
        bridges
    }

    fn dfs_bridges(
        &self, u: usize, g: &[Vec<usize>],
        disc: &mut Vec<i32>, low: &mut Vec<i32>, parent: &mut Vec<i32>,
        time_stamp: &mut i32, bridges: &mut Vec<Edge>,
    ) {
        disc[u] = *time_stamp;
        low[u] = *time_stamp;
        *time_stamp += 1;
        for &v in &g[u] {
            if disc[v] == -1 {
                parent[v] = u as i32;
                self.dfs_bridges(v, g, disc, low, parent, time_stamp, bridges);
                if low[v] > disc[u] {
                    bridges.push(Edge(min(u, v), max(u, v)));
                }
                low[u] = min(low[u], low[v]);
            } else if v as i32 != parent[u] {
                low[u] = min(low[u], disc[v]);
            }
        }
    }

    // ===================== ARTICULATION POINTS (recursive Tarjan — called on available subgraph) =====================
    // Note: for N≤20000 random graphs the available subgraph stays well-connected and
    // recursion depth stays manageable. For adversarial chain graphs this could be deep,
    // but the 2-connectivity prune fires immediately for such graphs.

    fn get_articulation_points(&self, g: &[Vec<usize>]) -> Vec<usize> {
        let mut disc = vec![-1i32; self.n];
        let mut low = vec![-1i32; self.n];
        let mut parent = vec![-1i32; self.n];
        let mut ap = vec![false; self.n];
        let mut time_stamp = 0;
        for i in 0..self.n {
            if disc[i] == -1 {
                self.dfs_ap(i, g, &mut disc, &mut low, &mut parent, &mut time_stamp, &mut ap);
            }
        }
        (0..self.n).filter(|&i| ap[i]).collect()
    }

    fn dfs_ap(
        &self, u: usize, g: &[Vec<usize>],
        disc: &mut Vec<i32>, low: &mut Vec<i32>, parent: &mut Vec<i32>,
        time_stamp: &mut i32, ap: &mut Vec<bool>,
    ) {
        let mut children = 0;
        disc[u] = *time_stamp;
        low[u] = *time_stamp;
        *time_stamp += 1;
        for &v in &g[u] {
            if disc[v] == -1 {
                children += 1;
                parent[v] = u as i32;
                self.dfs_ap(v, g, disc, low, parent, time_stamp, ap);
                if parent[u] == -1 && children > 1 {
                    ap[u] = true;
                }
                if parent[u] != -1 && low[v] >= disc[u] {
                    ap[u] = true;
                }
                low[u] = min(low[u], low[v]);
            } else if v as i32 != parent[u] {
                low[u] = min(low[u], disc[v]);
            }
        }
    }
}

// ===================== PROPAGATION RESULT =====================
enum PropResult {
    Continue,       // propagation done, no conclusion yet → branch
    Contradiction,  // dead end → backtrack
    Solved,         // full Hamiltonian cycle found
}

// ===================== FREE HELPERS =====================

fn validate_cycle(g: &[Vec<usize>], path_edges: &Option<Vec<Edge>>) -> bool {
    let Some(edges) = path_edges else { return false; };
    if edges.len() != g.len() {
        return false;
    }
    let n = g.len();
    let mut g_res: Vec<Vec<usize>> = vec![vec![]; n];
    for e in edges {
        g_res[e.0].push(e.1);
        g_res[e.1].push(e.0);
    }
    g_res.iter().all(|adj| adj.len() == 2) && is_connected_free(&g_res, n)
}

fn is_connected_free(g: &[Vec<usize>], n: usize) -> bool {
    if n == 0 { return true; }
    let mut visited = vec![false; n];
    let mut stack: Vec<usize> = vec![0];
    visited[0] = true;
    while let Some(curr) = stack.pop() {
        for &v in &g[curr] {
            if !visited[v] {
                visited[v] = true;
                stack.push(v);
            }
        }
    }
    visited.iter().all(|&v| v)
}

// ===================== GRAPH GENERATORS =====================

fn get_tutte_graph() -> Vec<Vec<usize>> {
    let n = 46;
    let mut g = vec![vec![]; n];
    let edges = vec![
        (0,1),(0,2),(0,3),(1,4),(1,26),(2,10),(2,11),(3,18),(3,19),(4,5),(4,33),(5,6),(5,29),
        (6,7),(6,27),(7,8),(7,14),(8,9),(8,38),(9,10),(9,37),(10,39),(11,12),(11,39),(12,13),
        (12,35),(13,14),(13,15),(14,34),(15,16),(15,22),(16,17),(16,44),(17,18),(17,43),(18,45),
        (19,20),(19,45),(20,21),(20,41),(21,22),(21,23),(22,40),(23,24),(23,27),(24,25),(24,32),
        (25,26),(25,31),(26,33),(27,28),(28,29),(28,32),(29,30),(30,31),(30,33),(31,32),(34,35),
        (34,38),(35,36),(36,37),(36,39),(37,38),(40,41),(40,44),(41,42),(42,43),(42,45),(43,44),
    ];
    for &(u, v) in &edges {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

fn get_petersen_graph() -> Vec<Vec<usize>> {
    let n = 10;
    let mut g = vec![vec![]; n];
    let edges = vec![
        (0,1),(1,2),(2,3),(3,4),(4,0),(5,7),(7,9),(9,6),(6,8),(8,5),
        (0,5),(1,6),(2,7),(3,8),(4,9),
    ];
    for &(u, v) in &edges {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

fn get_heawood_graph() -> Vec<Vec<usize>> {
    let n = 14;
    let mut g = vec![vec![]; n];
    let lines: Vec<Vec<usize>> = vec![
        vec![0,1,2], vec![0,3,5], vec![0,4,6],
        vec![1,3,6], vec![1,4,5], vec![2,3,4], vec![2,5,6],
    ];
    for (l, line_pts) in lines.iter().enumerate() {
        for &p in line_pts {
            let line_node = l + 7;
            g[p].push(line_node);
            g[line_node].push(p);
        }
    }
    g
}

fn get_desargues_graph() -> Vec<Vec<usize>> {
    let n = 20;
    let mut g = vec![vec![]; n];
    let edges = vec![
        (0,1),(0,5),(0,19),(1,2),(1,16),(2,3),(2,11),(3,4),(3,14),(4,5),(4,9),(5,6),(6,7),
        (6,15),(7,8),(7,18),(8,9),(8,13),(9,10),(10,11),(10,19),(11,12),(12,13),(12,17),
        (13,14),(14,15),(15,16),(16,17),(17,18),(18,19),
    ];
    for &(u, v) in &edges {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

fn get_dodecahedral_graph() -> Vec<Vec<usize>> {
    let n = 20;
    let mut g = vec![vec![]; n];
    let adjs = [
        1,4,7, 0,2,9, 1,3,11, 2,3,13, 0,3,5, 4,6,14, 5,7,16, 0,6,8,
        7,9,17, 1,8,10, 9,11,18, 2,10,12, 11,13,19, 3,12,14, 5,13,15,
        14,16,19, 6,15,17, 8,16,18, 10,17,19, 12,15,18,
    ];
    for i in 0..20 {
        for j in 0..3 {
            let v = adjs[i * 3 + j];
            g[i].push(v);
        }
    }
    g
}

fn get_hypercube_graph(dim: usize) -> Vec<Vec<usize>> {
    let nn = 1 << dim;
    let mut g = vec![vec![]; nn];
    for i in 0..nn {
        for j in 0..dim {
            g[i].push(i ^ (1 << j));
        }
    }
    g
}

fn get_grid_graph(rows: usize, cols: usize) -> Vec<Vec<usize>> {
    let nn = rows * cols;
    let mut g = vec![vec![]; nn];
    for i in 0..rows {
        for j in 0..cols {
            let u = i * cols + j;
            if j + 1 < cols {
                let v = u + 1;
                g[u].push(v);
                g[v].push(u);
            }
            if i + 1 < rows {
                let v = u + cols;
                g[u].push(v);
                g[v].push(u);
            }
        }
    }
    g
}

fn get_complete_graph(nn: usize) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; nn];
    for i in 0..nn {
        for j in i + 1..nn {
            g[i].push(j);
            g[j].push(i);
        }
    }
    g
}

fn get_wheel_graph(nn: usize) -> Vec<Vec<usize>> {
    let mut g = vec![vec![]; nn];
    for i in 1..nn {
        g[0].push(i);
        g[i].push(0);
    }
    for i in 1..nn - 1 {
        g[i].push(i + 1);
        g[i + 1].push(i);
    }
    g[1].push(nn - 1);
    g[nn - 1].push(1);
    g
}

fn get_circular_ladder_graph(k: usize) -> Vec<Vec<usize>> {
    let nn = 2 * k;
    let mut g = vec![vec![]; nn];
    for i in 0..k {
        let next = (i + 1) % k;
        g[i].push(next);
        g[next].push(i);
        let inner = i + k;
        let inner_next = (i + 1) % k + k;
        g[inner].push(inner_next);
        g[inner_next].push(inner);
        g[i].push(inner);
        g[inner].push(i);
    }
    g
}

fn get_complete_bipartite(a: usize, b: usize) -> Vec<Vec<usize>> {
    let nn = a + b;
    let mut g = vec![vec![]; nn];
    for i in 0..a {
        for j in 0..b {
            let v = j + a;
            g[i].push(v);
            g[v].push(i);
        }
    }
    g
}

fn get_star_graph(k: usize) -> Vec<Vec<usize>> {
    let nn = k + 1;
    let mut g = vec![vec![]; nn];
    for i in 1..=k {
        g[0].push(i);
        g[i].push(0);
    }
    g
}

fn get_barbell_graph(m1: usize) -> Vec<Vec<usize>> {
    let nn = 2 * m1;
    let mut g = vec![vec![]; nn];
    for i in 0..m1 {
        for j in i + 1..m1 {
            g[i].push(j);
            g[j].push(i);
        }
    }
    for i in m1..nn {
        for j in i + 1..nn {
            g[i].push(j);
            g[j].push(i);
        }
    }
    g[m1 - 1].push(m1);
    g[m1].push(m1 - 1);
    g
}

fn get_knight_graph(rows: usize, cols: usize) -> Vec<Vec<usize>> {
    let deltas: [(isize, isize); 8] = [
        (-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1),
    ];
    let n = rows * cols;
    let mut g: Vec<Vec<usize>> = vec![vec![]; n];
    for r in 0..rows {
        for c in 0..cols {
            let u = r * cols + c;
            for &(dr, dc) in &deltas {
                let nr = r as isize + dr;
                let nc = c as isize + dc;
                if nr >= 0 && nr < rows as isize && nc >= 0 && nc < cols as isize {
                    let v = (nr as usize) * cols + (nc as usize);
                    g[u].push(v);
                }
            }
        }
    }
    g
}

// ===================== TEST FUNCTIONS =====================

fn verify_carver_integrity() {
    println!(
        "{:<30} | {:<5} | {:<10} | {:<10} | Time (s)",
        "Adversarial Case", "N", "Expected", "Result"
    );
    println!("{}", "-".repeat(80));

    let test_matrix: Vec<(String, Box<dyn Fn() -> Vec<Vec<usize>>>, String)> = vec![
        ("Petersen (UNSAT)".into(),         Box::new(get_petersen_graph),                    "UNSAT".into()),
        ("Tutte Graph (UNSAT)".into(),      Box::new(get_tutte_graph),                       "UNSAT".into()),
        ("8x8 Grid (SAT)".into(),           Box::new(|| get_grid_graph(8, 8)),               "SAT".into()),
        ("Heawood Graph (SAT)".into(),      Box::new(get_heawood_graph),                     "SAT".into()),
        ("Hypercube Q4 (SAT)".into(),       Box::new(|| get_hypercube_graph(4)),             "SAT".into()),
        ("Dodecahedral (SAT)".into(),       Box::new(get_dodecahedral_graph),                "SAT".into()),
        ("Desargues (SAT)".into(),          Box::new(get_desargues_graph),                   "SAT".into()),
        ("Complete K(15) (SAT)".into(),     Box::new(|| get_complete_graph(15)),             "SAT".into()),
        ("Wheel W(20) (SAT)".into(),        Box::new(|| get_wheel_graph(20)),                "SAT".into()),
        ("Circular Ladder (SAT)".into(),    Box::new(|| get_circular_ladder_graph(10)),      "SAT".into()),
        ("Bipartite K(5,6) (UNSAT)".into(), Box::new(|| get_complete_bipartite(5, 6)),       "UNSAT".into()),
        ("Star Graph S(8) (UNSAT)".into(),  Box::new(|| get_star_graph(8)),                  "UNSAT".into()),
        ("7x7 Grid (UNSAT)".into(),         Box::new(|| get_grid_graph(7, 7)),               "UNSAT".into()),
        ("Barbell B(8,0) (UNSAT)".into(),   Box::new(|| get_barbell_graph(8)),               "UNSAT".into()),
        ("5x5 Knight (UNSAT)".into(),       Box::new(|| get_knight_graph(5, 5)),             "UNSAT".into()),
    ];

    for (name, maker, expected) in &test_matrix {
        let g = maker();
        let n = g.len();
        let mut solver = BcCraver::new(&g);
        let start = Instant::now();
        let path = solver.solve();
        let duration = start.elapsed().as_secs_f64();
        let result = if path.is_some() { "SAT" } else { "UNSAT" };
        let status = if result == "SAT" {
            if validate_cycle(&g, &path) { "✅ PASS" } else { "❌ INVALID PATH" }
        } else if expected == "UNSAT" {
            "✅ PASS"
        } else {
            "❌ FALSE UNSAT"
        };
        println!(
            "{:<30} | {:<5} | {:<10} | {:<10} | {:.5} {}",
            name, n, expected, result, duration, status
        );
    }
}

fn get_random_graph(nn: usize, p: f64) -> Vec<Vec<usize>> {
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
    let mut rng = thread_rng();
    let dist = Uniform::from(0.0..1.0);
    for i in 0..nn {
        for j in i + 1..nn {
            if rng.sample(dist) < p {
                g[i].push(j);
                g[j].push(i);
            }
        }
    }
    g
}

fn run_bulletproof_audit(start_n: usize, max_n: usize) {
    println!(
        "{:<5} | {:<7} | {:<12} | {:<12} | Status",
        "N", "Edges", "Time (s)", "Cache Hits"
    );
    println!("{}", "-".repeat(60));

    for nn in start_n..=max_n {
        let p_hard = ((nn as f64).ln() + ((nn as f64).ln().ln().max(0.0) + 1e-9)) / (nn as f64);
        let p_test = p_hard.max(0.15);

        let mut g = get_random_graph(nn, p_test);
        while !is_connected_free(&g, nn) {
            g = get_random_graph(nn, p_test);
        }

        let mut solver = BcCraver::new(&g);
        let start = Instant::now();
        let path = solver.solve();
        let dur = start.elapsed().as_secs_f64();
        let cache_size = solver.get_memo_size();
        let edges_num: usize = g.iter().map(|adj| adj.len()).sum::<usize>() / 2;
        let status = if path.is_some() { "Solved" } else { "UNSAT" };

        println!(
            "{:<5} | {:<7} | {:.5}       | {:<12} | {}",
            nn, edges_num, dur, cache_size, status
        );
    }
}

fn main() {
    verify_carver_integrity();
    println!();
    run_bulletproof_audit(500, 20010);
}
