use std::collections::{HashMap, HashSet, VecDeque};
use std::time::Instant;
use rand::distributions::Uniform;
use rand::prelude::*;
use std::cmp::{max, min};

#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
struct Edge(usize, usize);

#[derive(Clone)]
struct BcCraver {
    n: usize,
    nodes: Vec<usize>,
    g_orig: Vec<Vec<usize>>,
    memo_cache: HashSet<Vec<u64>>,
    best_path: Option<Vec<Edge>>,
    all_edges: Vec<Edge>,
    edge_id: HashMap<Edge, usize>,
}

impl BcCraver {
    fn new(g: &Vec<Vec<usize>>) -> Self {
        let n = g.len();
        let mut nodes = vec![];
        for i in 0..n {
            nodes.push(i);
        }
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
        BcCraver {
            n,
            nodes,
            g_orig: g.clone(),
            memo_cache: HashSet::new(),
            best_path: None,
            all_edges,
            edge_id,
        }
    }

    fn _get_state_key(&self, locked: &HashSet<Edge>, deleted: &HashSet<Edge>) -> Vec<u64> {
        let m = self.all_edges.len();
        let num_bits = m * 2;
        let num_words = (num_bits + 63) / 64;
        let mut key = vec![0u64; num_words];
        for e in locked {
            if let Some(&id) = self.edge_id.get(e) {
                let bit_pos = id * 2;
                let word = bit_pos / 64;
                let bit = bit_pos % 64;
                key[word] |= 1u64 << bit;
            }
        }
        for e in deleted {
            if let Some(&id) = self.edge_id.get(e) {
                let bit_pos = id * 2 + 1;
                let word = bit_pos / 64;
                let bit = bit_pos % 64;
                key[word] |= 1u64 << bit;
            }
        }
        key
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
        let mut locked: HashSet<Edge> = HashSet::new();
        let mut deleted: HashSet<Edge> = HashSet::new();
        if self._search(&mut locked, &mut deleted) {
            return self.best_path.clone();
        }
        None
    }

    fn get_memo_size(&self) -> usize {
        self.memo_cache.len()
    }

    fn _search(&mut self, locked: &mut HashSet<Edge>, deleted: &mut HashSet<Edge>) -> bool {
        let state_sig = self._get_state_key(locked, deleted);
        if self.memo_cache.contains(&state_sig) {
            return false;
        }

        let mut g_avail = self.g_orig.clone();
        for e in deleted.iter() {
            let u = e.0;
            let v = e.1;
            g_avail[u].retain(|&x| x != v);
            g_avail[v].retain(|&x| x != u);
        }

        let mut changed = true;
        while changed {
            changed = false;

            if g_avail.iter().any(|adj| adj.len() < 2) {
                self.memo_cache.insert(state_sig.clone());
                return false;
            }

            let aps = self.get_articulation_points(&g_avail);
            for ap in aps {
                let mut g_temp = g_avail.clone();
                self.remove_node(&mut g_temp, ap);
                if self.number_connected_components(&g_temp) > 2 {
                    self.memo_cache.insert(state_sig.clone());
                    return false;
                }
            }

            let degree: Vec<usize> = g_avail.iter().map(|adj| adj.len()).collect();
            let mut locked_degree: Vec<usize> = vec![0; self.n];
            for e in locked.iter() {
                locked_degree[e.0] += 1;
                locked_degree[e.1] += 1;
            }
            let overloaded = locked_degree.iter().any(|&d| d > 2);
            if overloaded {
                self.memo_cache.insert(state_sig.clone());
                return false;
            }

            let mut locket_count: Vec<usize> = vec![0; self.n];
            for i in 0..self.n {
                if degree[i] == 2 {
                    for &v in &g_avail[i] {
                        locket_count[v] += 1;
                    }
                }
            }
            if locket_count.iter().any(|&c| c > 2) {
                self.memo_cache.insert(state_sig.clone());
                return false;
            }

            for &node in &self.nodes {
                let avail_edges = g_avail[node].clone();

                if avail_edges.len() == 2 && locked_degree[node] < 2 {
                    for &v in &avail_edges {
                        let e = Edge(min(node, v), max(node, v));
                        if !locked.contains(&e) {
                            locked.insert(e);
                            changed = true;
                        }
                    }
                    if avail_edges.len() == 2 {
                        let m1 = avail_edges[0];
                        let m2 = avail_edges[1];
                        if m1 != m2 {
                            let has_chord = g_avail[m1].iter().any(|&x| x == m2);
                            if has_chord {
                                let e_chord = Edge(min(m1, m2), max(m1, m2));
                                if !locked.contains(&e_chord) && !deleted.contains(&e_chord) {
                                    deleted.insert(e_chord);
                                    changed = true;
                                    let u = e_chord.0;
                                    let vv = e_chord.1;
                                    g_avail[u].retain(|&x| x != vv);
                                    g_avail[vv].retain(|&x| x != u);
                                }
                            }
                        }
                    }
                }

                if locked_degree[node] == 2 && g_avail[node].len() > 2 {
                    let current_neighbors: Vec<usize> = g_avail[node].clone();
                    let mut to_delete = vec![];
                    for &v in &current_neighbors {
                        let e = Edge(min(node, v), max(node, v));
                        if !locked.contains(&e) {
                            to_delete.push(v);
                        }
                    }
                    for &v in &to_delete {
                        let e = Edge(min(node, v), max(node, v));
                        deleted.insert(e);
                        changed = true;
                        g_avail[node].retain(|&x| x != v);
                        g_avail[v].retain(|&x| x != node);
                    }
                }
            }

            if !locked.is_empty() {
                let mut g_locked: Vec<Vec<usize>> = vec![vec![]; self.n];
                for e in locked.iter() {
                    g_locked[e.0].push(e.1);
                    g_locked[e.1].push(e.0);
                }
                if self.has_subcycle(&g_locked) {
                    self.memo_cache.insert(state_sig.clone());
                    return false;
                }
                if self.is_full_cycle(&g_locked) {
                    let path: Vec<Edge> = locked.iter().cloned().collect();
                    self.best_path = Some(path);
                    return true;
                }
            }
        }

        if locked.len() == self.n {
            let mut g_locked: Vec<Vec<usize>> = vec![vec![]; self.n];
            for e in locked.iter() {
                g_locked[e.0].push(e.1);
                g_locked[e.1].push(e.0);
            }
            if self.is_connected(&g_locked) && self.all_degree2(&g_locked) {
                let path: Vec<Edge> = locked.iter().cloned().collect();
                self.best_path = Some(path);
                return true;
            }
        }

        let mut locked_degree = vec![0usize; self.n];
        for e in locked.iter() {
            locked_degree[e.0] += 1;
            locked_degree[e.1] += 1;
        }
        let avail_deg: Vec<usize> = g_avail.iter().map(|adj| adj.len()).collect();

        let mut available_edges: Vec<Edge> = vec![];
        for u in 0..self.n {
            for &v in &g_avail[u] {
                if u < v {
                    let e = Edge(u, v);
                    if !locked.contains(&e) {
                        available_edges.push(e);
                    }
                }
            }
        }

        if available_edges.is_empty() {
            self.memo_cache.insert(state_sig.clone());
            return false;
        }

        available_edges.sort_by(|ea, eb| {
            let (u1, v1) = (ea.0, ea.1);
            let (u2, v2) = (eb.0, eb.1);
            let sum1 = locked_degree[u1] + locked_degree[v1];
            let sum2 = locked_degree[u2] + locked_degree[v2];
            let force1 = (if locked_degree[u1] == 1 { avail_deg[u1].saturating_sub(2) } else { 0 })
                + (if locked_degree[v1] == 1 { avail_deg[v1].saturating_sub(2) } else { 0 });
            let force2 = (if locked_degree[u2] == 1 { avail_deg[u2].saturating_sub(2) } else { 0 })
                + (if locked_degree[v2] == 1 { avail_deg[v2].saturating_sub(2) } else { 0 });
            let score1 = (sum1 as u32) * 100 + (force1 as u32);
            let score2 = (sum2 as u32) * 100 + (force2 as u32);
            score2.cmp(&score1)
        });

        let guess_edge = available_edges[0];

        {
            let mut locked1 = locked.clone();
            locked1.insert(guess_edge);
            let mut deleted1 = deleted.clone();
            if self._search(&mut locked1, &mut deleted1) {
                *locked = locked1;
                *deleted = deleted1;
                return true;
            }
        }

        {
            let mut locked2 = locked.clone();
            let mut deleted2 = deleted.clone();
            deleted2.insert(guess_edge);
            if self._search(&mut locked2, &mut deleted2) {
                *locked = locked2;
                *deleted = deleted2;
                return true;
            }
        }

        self.memo_cache.insert(state_sig);
        false
    }

    fn is_bipartite(&self) -> bool {
        let mut color: Vec<i32> = vec![-1; self.n];
        for i in 0..self.n {
            if color[i] == -1 {
                if !self.bfs_color(i, &mut color) {
                    return false;
                }
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
        while !q.is_empty() {
            let u = q.pop_front().unwrap();
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
        let mut disc: Vec<i32> = vec![-1; self.n];
        let mut low: Vec<i32> = vec![-1; self.n];
        let mut parent: Vec<i32> = vec![-1; self.n];
        let mut time_stamp = 0;
        let mut bridges: Vec<Edge> = vec![];
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
        let mut visited: Vec<bool> = vec![false; self.n];
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
        let mut visited: Vec<bool> = vec![false; self.n];
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
        let mut disc: Vec<i32> = vec![-1; self.n];
        let mut low: Vec<i32> = vec![-1; self.n];
        let mut parent: Vec<i32> = vec![-1; self.n];
        let mut ap: Vec<bool> = vec![false; self.n];
        let mut time_stamp = 0;
        for i in 0..self.n {
            if disc[i] == -1 {
                self.dfs_ap(i, g, &mut disc, &mut low, &mut parent, &mut time_stamp, &mut ap);
            }
        }
        let mut aps: Vec<usize> = vec![];
        for i in 0..self.n {
            if ap[i] {
                aps.push(i);
            }
        }
        aps
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
        let mut visited: Vec<bool> = vec![false; self.n];
        for i in 0..self.n {
            if !visited[i] {
                let mut component: Vec<usize> = vec![];
                self.dfs_component(i, g_locked, &mut visited, &mut component);
                let comp_size = component.len();
                let mut is_cycle = true;
                for &u in &component {
                    if g_locked[u].len() != 2 {
                        is_cycle = false;
                        break;
                    }
                }
                if is_cycle && comp_size < self.n {
                    return true;
                }
            }
        }
        false
    }

    fn is_full_cycle(&self, g_locked: &Vec<Vec<usize>>) -> bool {
        if !self.is_connected(g_locked) {
            return false;
        }
        self.all_degree2(g_locked)
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
        for i in 0..self.n {
            if g[i].len() != 2 {
                return false;
            }
        }
        true
    }
}

fn validate_cycle(g: &Vec<Vec<usize>>, path_edges: &Option<Vec<Edge>>) -> bool {
    if let Some(edges) = path_edges {
        if edges.len() != g.len() {
            return false;
        }
        let n = g.len();
        let mut g_res: Vec<Vec<usize>> = vec![vec![]; n];
        for e in edges {
            g_res[e.0].push(e.1);
            g_res[e.1].push(e.0);
        }
        if !all_degree2(&g_res, n) {
            return false;
        }
        if !is_connected(&g_res, n) {
            return false;
        }
        true
    } else {
        false
    }
}

fn all_degree2(g: &Vec<Vec<usize>>, n: usize) -> bool {
    for i in 0..n {
        if g[i].len() != 2 {
            return false;
        }
    }
    true
}

fn is_connected(g: &Vec<Vec<usize>>, n: usize) -> bool {
    let mut visited: Vec<bool> = vec![false; n];
    dfs(0, g, &mut visited);
    visited.iter().all(|&v| v)
}

fn dfs(u: usize, g: &Vec<Vec<usize>>, visited: &mut Vec<bool>) {
    visited[u] = true;
    for &v in &g[u] {
        if !visited[v] {
            dfs(v, g, visited);
        }
    }
}

fn get_tutte_graph() -> Vec<Vec<usize>> {
    let n = 46;
    let mut g: Vec<Vec<usize>> = vec![vec![]; n];
    let edges = vec![
        (0,1), (0,2), (0,3), (1,4), (1,26), (2,10), (2,11), (3,18), (3,19), (4,5), (4,33), (5,6), (5,29), (6,7), (6,27), (7,8), (7,14), (8,9), (8,38), (9,10), (9,37), (10,39), (11,12), (11,39), (12,13), (12,35), (13,14), (13,15), (14,34), (15,16), (15,22), (16,17), (16,44), (17,18), (17,43), (18,45), (19,20), (19,45), (20,21), (20,41), (21,22), (21,23), (22,40), (23,24), (23,27), (24,25), (24,32), (25,26), (25,31), (26,33), (27,28), (28,29), (28,32), (29,30), (30,31), (30,33), (31,32), (34,35), (34,38), (35,36), (36,37), (36,39), (37,38), (40,41), (40,44), (41,42), (42,43), (42,45), (43,44)
    ];
    for &(u, v) in &edges {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

fn get_petersen_graph() -> Vec<Vec<usize>> {
    let n = 10;
    let mut g: Vec<Vec<usize>> = vec![vec![]; n];
    let edges = vec![
        (0,1), (1,2), (2,3), (3,4), (4,0), (5,7), (7,9), (9,6), (6,8), (8,5), (0,5), (1,6), (2,7), (3,8), (4,9)
    ];
    for &(u, v) in &edges {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

fn get_heawood_graph() -> Vec<Vec<usize>> {
    let n = 14;
    let mut g: Vec<Vec<usize>> = vec![vec![]; n];
    let lines: Vec<Vec<usize>> = vec![
        vec![0,1,2], vec![0,3,5], vec![0,4,6], vec![1,3,6], vec![1,4,5], vec![2,3,4], vec![2,5,6]
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
    let mut g: Vec<Vec<usize>> = vec![vec![]; n];
    let edges = vec![
        (0,1), (0,5), (0,19), (1,2), (1,16), (2,3), (2,11), (3,4), (3,14), (4,5), (4,9), (5,6), (6,7), (6,15), (7,8), (7,18), (8,9), (8,13), (9,10), (10,11), (10,19), (11,12), (12,13), (12,17), (13,14), (14,15), (15,16), (16,17), (17,18), (18,19)
    ];
    for &(u, v) in &edges {
        g[u].push(v);
        g[v].push(u);
    }
    g
}

fn get_dodecahedral_graph() -> Vec<Vec<usize>> {
    let n = 20;
    let mut g: Vec<Vec<usize>> = vec![vec![]; n];
    let adjs = vec![1,4,7, 0,2,9, 1,3,11, 2,3,13, 0,3,5, 4,6,14, 5,7,16, 0,6,8, 7,9,17, 1,8,10, 9,11,18, 2,10,12, 11,13,19, 3,12,14, 5,13,15, 14,16,19, 6,15,17, 8,16,18, 10,17,19, 12,15,18];
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
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
    for i in 0..nn {
        for j in 0..dim {
            let neigh = i ^ (1 << j);
            g[i].push(neigh);
        }
    }
    g
}

fn get_grid_graph(rows: usize, cols: usize) -> Vec<Vec<usize>> {
    let nn = rows * cols;
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
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
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
    for i in 0..nn {
        for j in i + 1..nn {
            g[i].push(j);
            g[j].push(i);
        }
    }
    g
}

fn get_wheel_graph(nn: usize) -> Vec<Vec<usize>> {
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
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
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
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
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
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
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
    for i in 1..=k {
        g[0].push(i);
        g[i].push(0);
    }
    g
}

fn get_barbell_graph(m1: usize, _m2: usize) -> Vec<Vec<usize>> {
    let nn = 2 * m1;
    let mut g: Vec<Vec<usize>> = vec![vec![]; nn];
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

fn verify_carver_integrity() {
    println!("{:<25} | {:<5} | {:<10} | {:<10} | Time (s)", "Adversarial Case", "N", "Expected", "Result");
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
            if validate_cycle(&g, &path) { "✅ PASS" } else { "❌ INVALID PATH" }
        } else {
            if expected == "UNSAT" { "✅ PASS" } else { "❌ FALSE UNSAT" }
        };
        println!("{:<25} | {:<5} | {:<10} | {:<10} | {:.5} {}", name, n, expected, result, duration, status);
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
            let p_test = p_hard;
            let mut g = get_random_graph(nn, p_test);
            while !is_connected(&g, nn) {
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
    run_bulletproof_audit(200000);
}