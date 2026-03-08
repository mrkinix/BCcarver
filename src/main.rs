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

#[derive(Clone)]
struct BcCraver {
    n: usize,
    nodes: Vec<usize>,
    g_orig: Vec<Vec<usize>>,
    memo_cache: HashMap<u64, Vec<(Vec<u64>, Vec<u64>)>>,
    best_path: Option<Vec<Edge>>,
    all_edges: Vec<Edge>,
    edge_id: HashMap<Edge, usize>,
    locked_bits: Vec<u64>,
    deleted_bits: Vec<u64>,
    current_hash: u64,
    undo_stack: Vec<Change>,
    graph_undo: Vec<(usize, usize)>,
    locked_degree: Vec<usize>,
    zobrist_lock: Vec<u64>,
    zobrist_delete: Vec<u64>,
    g_avail: Vec<Vec<usize>>,
    total_deletions: usize,
}

impl BcCraver {
    fn new(g: &Vec<Vec<usize>>) -> Self {
        let n = g.len();
        let nodes: Vec<usize> = (0..n).collect();

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

        let mut rng = thread_rng();
        let mut zobrist_lock = vec![0u64; m];
        let mut zobrist_delete = vec![0u64; m];
        for i in 0..m {
            zobrist_lock[i] = rng.r#gen::<u64>();
            zobrist_delete[i] = rng.r#gen::<u64>();
        }

        BcCraver {
            n,
            nodes,
            g_orig: g.clone(),
            memo_cache: HashMap::new(),
            best_path: None,
            all_edges,
            edge_id,
            locked_bits: vec![0u64; num_words],
            deleted_bits: vec![0u64; num_words],
            current_hash: 0,
            undo_stack: vec![],
            graph_undo: vec![],
            locked_degree: vec![0; n],
            zobrist_lock,
            zobrist_delete,
            g_avail: g.clone(),
            total_deletions: 0,
        }
    }

    fn is_locked(&self, id: usize) -> bool {
        let word = (id * 2) / 64;
        let bit = (id * 2) % 64;
        (self.locked_bits[word] & (1u64 << bit)) != 0
    }

    fn is_deleted(&self, id: usize) -> bool {
        let word = (id * 2 + 1) / 64;
        let bit = (id * 2 + 1) % 64;
        (self.deleted_bits[word] & (1u64 << bit)) != 0
    }

    fn apply_lock(&mut self, id: usize) {
        let word = (id * 2) / 64;
        let bit = (id * 2) % 64;
        self.locked_bits[word] |= 1u64 << bit;
        self.current_hash ^= self.zobrist_lock[id];
        let Edge(u, v) = self.all_edges[id];
        self.locked_degree[u] += 1;
        self.locked_degree[v] += 1;
        self.undo_stack.push(Change::Lock(id));
    }

    fn apply_delete(&mut self, id: usize) {
        let word = (id * 2 + 1) / 64;
        let bit = (id * 2 + 1) % 64;
        self.deleted_bits[word] |= 1u64 << bit;
        self.current_hash ^= self.zobrist_delete[id];
        self.undo_stack.push(Change::Delete(id));

        let Edge(u, v) = self.all_edges[id];
        if let Some(pos) = self.g_avail[u].iter().position(|&x| x == v) {
            self.g_avail[u].swap_remove(pos);
        }
        if let Some(pos) = self.g_avail[v].iter().position(|&x| x == u) {
            self.g_avail[v].swap_remove(pos);
        }
        self.graph_undo.push((u, v));
        self.total_deletions += 1;
    }

    fn undo(&mut self) {
        if let Some(ch) = self.undo_stack.pop() {
            match ch {
                Change::Lock(id) => {
                    let word = (id * 2) / 64;
                    let bit = (id * 2) % 64;
                    self.locked_bits[word] &= !(1u64 << bit);
                    self.current_hash ^= self.zobrist_lock[id];
                    let Edge(u, v) = self.all_edges[id];
                    self.locked_degree[u] -= 1;
                    self.locked_degree[v] -= 1;
                }
                Change::Delete(id) => {
                    let word = (id * 2 + 1) / 64;
                    let bit = (id * 2 + 1) % 64;
                    self.deleted_bits[word] &= !(1u64 << bit);
                    self.current_hash ^= self.zobrist_delete[id];
                    if let Some((u, v)) = self.graph_undo.pop() {
                        self.g_avail[u].push(v);
                        self.g_avail[v].push(u);
                    }
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

    fn memoize(&mut self, state: u64) {
        self.memo_cache
            .entry(state)
            .or_insert_with(Vec::new)
            .push((self.locked_bits.clone(), self.deleted_bits.clone()));
    }

    fn build_locked_graph(&self) -> Vec<Vec<usize>> {
        let mut gl: Vec<Vec<usize>> = vec![vec![]; self.n];
        let m = self.all_edges.len();
        for id in 0..m {
            if self.is_locked(id) {
                let Edge(u, v) = self.all_edges[id];
                gl[u].push(v);
                gl[v].push(u);
            }
        }
        gl
    }

    fn collect_locked(&self) -> Vec<Edge> {
        let mut path = vec![];
        let m = self.all_edges.len();
        for id in 0..m {
            if self.is_locked(id) {
                path.push(self.all_edges[id]);
            }
        }
        path
    }

    fn solve(&mut self) -> Option<Vec<Edge>> {
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

        self.locked_bits.fill(0);
        self.deleted_bits.fill(0);
        self.current_hash = 0;
        self.undo_stack.clear();
        self.graph_undo.clear();
        self.locked_degree.fill(0);
        self.g_avail = self.g_orig.clone();
        self.best_path = None;
        self.total_deletions = 0;

        if self._search() {
            return self.best_path.clone();
        }
        None
    }

    fn _search(&mut self) -> bool {
        let state = self.current_hash;

        // Exact zero-collision verification (Zobrist is now only a fast pre-filter)
        if let Some(entries) = self.memo_cache.get(&state) {
            for (locked, deleted) in entries {
                if locked == &self.locked_bits && deleted == &self.deleted_bits {
                    return false;
                }
            }
        }

        let entry_len = self.undo_stack.len();
        let mut last_ap_deletions = self.total_deletions;
        let mut needs_ap_check = true;
        let mut changed = true;

        while changed {
            changed = false;

            if self.g_avail.iter().any(|adj| adj.len() < 2) {
                self.undo_to(entry_len);
                self.memoize(state);
                return false;
            }

            // Gatekeeper de Mutation: AP only if a deletion occurred since last scan
            if needs_ap_check || self.total_deletions > last_ap_deletions {
                let aps = self.get_articulation_points(&self.g_avail);
                for ap in aps {
                    let mut g_temp = self.g_avail.clone();
                    self.remove_node(&mut g_temp, ap);
                    if self.number_connected_components(&g_temp) > 2 {
                        self.undo_to(entry_len);
                        self.memoize(state);
                        return false;
                    }
                }
                last_ap_deletions = self.total_deletions;
                needs_ap_check = false;
            }

            if self.locked_degree.iter().any(|&d| d > 2) {
                self.undo_to(entry_len);
                self.memoize(state);
                return false;
            }

            let degree: Vec<usize> = self.g_avail.iter().map(|adj| adj.len()).collect();
            let mut locket_count: Vec<usize> = vec![0; self.n];
            for i in 0..self.n {
                if degree[i] == 2 {
                    for &v in &self.g_avail[i] {
                        locket_count[v] += 1;
                    }
                }
            }
            if locket_count.iter().any(|&c| c > 2) {
                self.undo_to(entry_len);
                self.memoize(state);
                return false;
            }

            for node in 0..self.n {
                let avail_edges = self.g_avail[node].clone();

                if avail_edges.len() == 2 && self.locked_degree[node] < 2 {
                    for &v in &avail_edges {
                        let e = Edge(min(node, v), max(node, v));
                        if let Some(&id) = self.edge_id.get(&e) {
                            if !self.is_locked(id) {
                                self.apply_lock(id);
                                changed = true;
                            }
                        }
                    }
                    if avail_edges.len() == 2 {
                        let m1 = avail_edges[0];
                        let m2 = avail_edges[1];
                        if m1 != m2 {
                            let has_chord = self.g_avail[m1].iter().any(|&x| x == m2);
                            if has_chord {
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
                }

                if self.locked_degree[node] == 2 && self.g_avail[node].len() > 2 {
                    let current_neighbors: Vec<usize> = self.g_avail[node].clone();
                    for &v in &current_neighbors {
                        let e = Edge(min(node, v), max(node, v));
                        if let Some(&id) = self.edge_id.get(&e) {
                            if !self.is_locked(id) {
                                self.apply_delete(id);
                                changed = true;
                            }
                        }
                    }
                }
            }

            if self.undo_stack.len() > entry_len {
                let g_locked = self.build_locked_graph();
                if self.has_subcycle(&g_locked) {
                    self.undo_to(entry_len);
                    self.memoize(state);
                    return false;
                }
                if self.is_full_cycle(&g_locked) {
                    self.best_path = Some(self.collect_locked());
                    return true;
                }
            }
        }

        if self.locked_degree.iter().all(|&d| d == 2) {
            let g_locked = self.build_locked_graph();
            if self.is_connected(&g_locked) && self.all_degree2(&g_locked) {
                self.best_path = Some(self.collect_locked());
                return true;
            }
        }

        let avail_deg: Vec<usize> = self.g_avail.iter().map(|adj| adj.len()).collect();
        let mut available_edges: Vec<Edge> = vec![];
        for u in 0..self.n {
            for &v in &self.g_avail[u] {
                if u < v {
                    let e = Edge(u, v);
                    if let Some(&id) = self.edge_id.get(&e) {
                        if !self.is_locked(id) {
                            available_edges.push(e);
                        }
                    }
                }
            }
        }

        if available_edges.is_empty() {
            self.undo_to(entry_len);
            self.memoize(state);
            return false;
        }

        available_edges.sort_by(|ea, eb| {
            let sum1 = self.locked_degree[ea.0] + self.locked_degree[ea.1];
            let sum2 = self.locked_degree[eb.0] + self.locked_degree[eb.1];
            let force1 = (if self.locked_degree[ea.0] == 1 { avail_deg[ea.0].saturating_sub(2) } else { 0 })
                + (if self.locked_degree[ea.1] == 1 { avail_deg[ea.1].saturating_sub(2) } else { 0 });
            let force2 = (if self.locked_degree[eb.0] == 1 { avail_deg[eb.0].saturating_sub(2) } else { 0 })
                + (if self.locked_degree[eb.1] == 1 { avail_deg[eb.1].saturating_sub(2) } else { 0 });
            let score1 = (sum1 as u32) * 100 + force1 as u32;
            let score2 = (sum2 as u32) * 100 + force2 as u32;
            score2.cmp(&score1)
        });

        let guess_edge = available_edges[0];
        if let Some(&id) = self.edge_id.get(&guess_edge) {
            self.apply_lock(id);
            if self._search() {
                return true;
            }
            self.undo();
        }
        if let Some(&id) = self.edge_id.get(&guess_edge) {
            self.apply_delete(id);
            if self._search() {
                return true;
            }
            self.undo();
        }

        self.undo_to(entry_len);
        self.memoize(state);
        false
    }

    // ==================== ALL HELPERS (unchanged from previous version) ====================
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

    fn has_bridges(&self) -> bool {
        !self.get_bridges(&self.g_orig).is_empty()
    }

    fn get_bridges(&self, g: &Vec<Vec<usize>>) -> Vec<Edge> {
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

    fn dfs_bridges(&self, u: usize, g: &Vec<Vec<usize>>, disc: &mut Vec<i32>, low: &mut Vec<i32>, parent: &mut Vec<i32>, time_stamp: &mut i32, bridges: &mut Vec<Edge>) {
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

    fn is_connected(&self, g: &Vec<Vec<usize>>) -> bool {
        let mut visited = vec![false; self.n];
        self.dfs(0, g, &mut visited);
        visited.iter().all(|&v| v)
    }

    fn dfs(&self, u: usize, g: &Vec<Vec<usize>>, visited: &mut Vec<bool>) {
        visited[u] = true;
        for &v in &g[u] {
            if !visited[v] {
                self.dfs(v, g, visited);
            }
        }
    }

    fn number_connected_components(&self, g: &Vec<Vec<usize>>) -> usize {
        let mut visited = vec![false; self.n];
        let mut count = 0;
        for i in 0..self.n {
            if !visited[i] {
                self.dfs(i, g, &mut visited);
                count += 1;
            }
        }
        count
    }

    fn remove_node(&self, g: &mut Vec<Vec<usize>>, ap: usize) {
        g[ap].clear();
        for i in 0..self.n {
            g[i].retain(|&x| x != ap);
        }
    }

    fn get_articulation_points(&self, g: &Vec<Vec<usize>>) -> Vec<usize> {
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

    fn dfs_ap(&self, u: usize, g: &Vec<Vec<usize>>, disc: &mut Vec<i32>, low: &mut Vec<i32>, parent: &mut Vec<i32>, time_stamp: &mut i32, ap: &mut Vec<bool>) {
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

    fn has_subcycle(&self, g_locked: &Vec<Vec<usize>>) -> bool {
        let mut visited = vec![false; self.n];
        for i in 0..self.n {
            if !visited[i] {
                let mut component = vec![];
                self.dfs_component(i, g_locked, &mut visited, &mut component);
                let comp_size = component.len();
                if component.iter().all(|&u| g_locked[u].len() == 2) && comp_size < self.n {
                    return true;
                }
            }
        }
        false
    }

    fn is_full_cycle(&self, g_locked: &Vec<Vec<usize>>) -> bool {
        self.is_connected(g_locked) && self.all_degree2(g_locked)
    }

    fn dfs_component(&self, u: usize, g: &Vec<Vec<usize>>, visited: &mut Vec<bool>, component: &mut Vec<usize>) {
        visited[u] = true;
        component.push(u);
        for &v in &g[u] {
            if !visited[v] {
                self.dfs_component(v, g, visited, component);
            }
        }
    }

    fn all_degree2(&self, g: &Vec<Vec<usize>>) -> bool {
        g.iter().all(|adj| adj.len() == 2)
    }

    fn get_memo_size(&self) -> usize {
        self.memo_cache.len()
    }
}

// ====================== FREE HELPERS ======================
fn validate_cycle(g: &Vec<Vec<usize>>, path_edges: &Option<Vec<Edge>>) -> bool {
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
    all_degree2_free(&g_res, n) && is_connected_free(&g_res, n)
}

fn all_degree2_free(g: &Vec<Vec<usize>>, _n: usize) -> bool {
    g.iter().all(|adj| adj.len() == 2)
}

fn is_connected_free(g: &Vec<Vec<usize>>, n: usize) -> bool {
    let mut visited = vec![false; n];
    dfs_free(0, g, &mut visited);
    visited.iter().all(|&v| v)
}

fn dfs_free(u: usize, g: &Vec<Vec<usize>>, visited: &mut Vec<bool>) {
    visited[u] = true;
    for &v in &g[u] {
        if !visited[v] {
            dfs_free(v, g, visited);
        }
    }
}

// ====================== ALL GRAPH GENERATORS ======================
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
        vec![0,1,2],
        vec![0,3,5],
        vec![0,4,6],
        vec![1,3,6],
        vec![1,4,5],
        vec![2,3,4],
        vec![2,5,6],
    ];
    for l in 0..7 {
        for &p in &lines[l] {
            let line = l + 7;
            g[p].push(line);
            g[line].push(p);
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
    let adjs = vec![
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

fn get_barbell_graph(m1: usize, _m2: usize) -> Vec<Vec<usize>> {
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

// NEW: Knight's Tour graph generator (Cavalier)
fn get_knight_graph(rows: usize, cols: usize) -> Vec<Vec<usize>> {
    let deltas: [(isize, isize); 8] = [
        (-2, -1),
        (-2, 1),
        (-1, -2),
        (-1, 2),
        (1, -2),
        (1, 2),
        (2, -1),
        (2, 1),
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

// ====================== TEST FUNCTIONS ======================
fn verify_carver_integrity() {
    println!("{:<30} | {:<5} | {:<10} | {:<10} | Time (s)", "Adversarial Case", "N", "Expected", "Result");
    println!("{}", "-".repeat(80));
    let test_matrix: Vec<(String, fn() -> Vec<Vec<usize>>, String)> = vec![
        ("Petersen (UNSAT)".to_string(), get_petersen_graph, "UNSAT".to_string()),
        ("Tutte Graph (UNSAT)".to_string(), get_tutte_graph, "UNSAT".to_string()),
        ("8x8 Grid (SAT)".to_string(), || get_grid_graph(8, 8), "SAT".to_string()),
        ("Heawood Graph (SAT)".to_string(), get_heawood_graph, "SAT".to_string()),
        ("Hypercube Q4 (SAT)".to_string(), || get_hypercube_graph(4), "SAT".to_string()),
        ("Dodecahedral (SAT)".to_string(), get_dodecahedral_graph, "SAT".to_string()),
        ("Desargues (SAT)".to_string(), get_desargues_graph, "SAT".to_string()),
        ("Complete K(15) (SAT)".to_string(), || get_complete_graph(15), "SAT".to_string()),
        ("Wheel W(20) (SAT)".to_string(), || get_wheel_graph(20), "SAT".to_string()),
        ("Circular Ladder (SAT)".to_string(), || get_circular_ladder_graph(10), "SAT".to_string()),
        ("Bipartite K(5,6) (UNSAT)".to_string(), || get_complete_bipartite(5, 6), "UNSAT".to_string()),
        ("Star Graph S(8) (UNSAT)".to_string(), || get_star_graph(8), "UNSAT".to_string()),
        ("7x7 Grid (UNSAT)".to_string(), || get_grid_graph(7, 7), "UNSAT".to_string()),
        ("Barbell B(8,0) (UNSAT)".to_string(), || get_barbell_graph(8, 0), "UNSAT".to_string()),
        ("5x5 Knight (UNSAT)".to_string(), || get_knight_graph(5, 5), "UNSAT".to_string()),
    ];
    for (name, maker, expected) in test_matrix {
        let g = maker();
        let n = g.len();
        let mut solver = BcCraver::new(&g);
        let start = Instant::now();
        let path = solver.solve();
        let duration = start.elapsed().as_secs_f64();
        let result = if path.is_some() { "SAT" } else { "UNSAT" };
        let status = if result == "SAT" {
            if validate_cycle(&g, &path) {
                "✅ PASS"
            } else {
                "❌ INVALID PATH"
            }
        } else if expected == "UNSAT" {
            "✅ PASS"
        } else {
            "❌ FALSE UNSAT"
        };
        println!("{:<30} | {:<5} | {:<10} | {:<10} | {:.5} {}", name, n, expected, result, duration, status);
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

fn run_bulletproof_audit(max_n: usize) {
    let ns: Vec<usize> = (6..=max_n).collect();
    println!("{:<5} | {:<7} | {:<10} | {:<12} | Status", "N", "Edges", "Time (s)", "Cache Hits");
    println!("{}", "-".repeat(55));
    for nn in ns {
        let mut trial_times: Vec<f64> = vec![];
        let mut cache_size = 0;
        let mut edges_num = 0;
        let mut status = String::new();
        for _ in 0..3 {
            let p_hard = ((nn as f64).ln() + ((nn as f64).ln().ln() + 1e-9)) / (nn as f64);
            let p_test = p_hard.max(0.15);
            let mut g = get_random_graph(nn, p_test);
            while !is_connected_free(&g, nn) {
                g = get_random_graph(nn, p_test);
            }
            let mut solver = BcCraver::new(&g);
            let start = Instant::now();
            let path = solver.solve();
            let dur = start.elapsed().as_secs_f64();
            trial_times.push(dur);
            cache_size = solver.get_memo_size();
            edges_num = g.iter().map(|adj| adj.len()).sum::<usize>() / 2;
            status = if path.is_some() { "Solved".to_string() } else { "UNSAT".to_string() };
        }
        let avg_t = trial_times.iter().sum::<f64>() / 3.0;
        println!("{:<5} | {:<7} | {:.5}     | {:<12} | {}", nn, edges_num, avg_t, cache_size, status);
    }
}

fn main() {
    verify_carver_integrity();
    run_bulletproof_audit(20010);
}