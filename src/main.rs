#![allow(unused_macros, unused_imports, dead_code)]
use fixedbitset::FixedBitSet;
use itertools::*;
use num::{One, Zero};
use permutohedron::LexicalPermutation;
use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaChaRng;
use std::any::TypeId;
use std::cmp::{max, min, Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::mem::swap;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};
use std::time::Instant;
//let mut rng = ChaChaRng::from_seed([0; 32]);

macro_rules! __debug_impl {
    ($x:expr) => {
        eprint!("{}={}  ", stringify!($x), &$x);
    };
    ($x:expr, $($y:expr),+) => (
        __debug_impl!($x);
        __debug_impl!($($y),+);
    );
}
macro_rules! __debug_line {
    () => {
        eprint!("L{}  ", line!());
    };
}
macro_rules! __debug_select {
    () => {
        eprintln!();
    };
    ($x:expr) => {
        __debug_line!();
        __debug_impl!($x);
        eprintln!();
    };
    ($x:expr, $($y:expr),+) => (
        __debug_line!();
        __debug_impl!($x);
        __debug_impl!($($y),+);
        eprintln!();
    );
}
macro_rules! debug {
    () => {
        if cfg!(debug_assertions) {
            __debug_select!();
        }
    };
    ($($xs:expr),+) => {
        if cfg!(debug_assertions) {
            __debug_select!($($xs),+);
        }
    };
}

mod change_min_max {
    pub trait ChangeMinMax<T> {
        fn chmin(&mut self, rhs: T) -> bool;
        fn chmax(&mut self, rhs: T) -> bool;
    }
    impl<T: PartialOrd + Copy> ChangeMinMax<T> for T {
        #[inline(always)]
        fn chmin(&mut self, rhs: T) -> bool {
            if *self > rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
        #[inline(always)]
        fn chmax(&mut self, rhs: T) -> bool {
            if *self < rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
    }
    impl<T: PartialOrd + Copy> ChangeMinMax<T> for Option<T> {
        #[inline(always)]
        fn chmin(&mut self, rhs: T) -> bool {
            if let Some(val) = *self {
                if val > rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
        #[inline(always)]
        fn chmax(&mut self, rhs: T) -> bool {
            if let Some(val) = *self {
                if val < rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
    }
}
use change_min_max::ChangeMinMax;

mod union_find {
    #[derive(Debug, Clone)]
    pub struct UnionFind {
        pub graph: Vec<Vec<usize>>,
        potential: Vec<i64>,
        parents: Vec<usize>,
        grp_sz: Vec<usize>,
        grp_num: usize,
    }

    impl UnionFind {
        pub fn new(sz: usize) -> Self {
            Self {
                graph: vec![vec![]; sz],
                potential: vec![0; sz],
                parents: (0..sz).collect::<Vec<usize>>(),
                grp_sz: vec![1; sz],
                grp_num: sz,
            }
        }
        pub fn root(&mut self, v: usize) -> usize {
            if v == self.parents[v] {
                v
            } else {
                let pv = self.parents[v];
                let rv = self.root(pv);
                self.potential[v] += self.potential[pv];
                self.parents[v] = rv;
                self.parents[v]
            }
        }
        pub fn get_delta(&mut self, v0: usize, v1: usize) -> Option<i64> {
            if !self.same(v0, v1) {
                return None;
            }
            Some(self.potential[v1] - self.potential[v0])
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.root(a) == self.root(b)
        }
        pub fn unite(&mut self, into: usize, from: usize) {
            self.unite_with_delta(into, from, 0);
        }
        pub fn unite_with_delta(&mut self, into: usize, from: usize, delta: i64) {
            self.graph[into].push(from);
            self.graph[from].push(into);
            let r_into = self.root(into);
            let r_from = self.root(from);
            if r_into != r_from {
                self.parents[r_from] = r_into;
                self.potential[r_from] = self.potential[into] - self.potential[from] + delta;
                self.grp_sz[r_into] += self.grp_sz[r_from];
                self.grp_sz[r_from] = 0;
                self.grp_num -= 1;
            }
        }
        pub fn group_num(&self) -> usize {
            self.grp_num
        }
        pub fn group_size(&mut self, a: usize) -> usize {
            let ra = self.root(a);
            self.grp_sz[ra]
        }
    }
}
use union_find::UnionFind;

mod xor_shift_64 {
    pub struct XorShift64(u64);
    impl XorShift64 {
        pub fn new() -> Self {
            XorShift64(88172645463325252_u64)
        }
        pub fn next_f64(&mut self) -> f64 {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0 as f64 * 5.421_010_862_427_522e-20
        }
        pub fn next_u64(&mut self) -> u64 {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0
        }
        pub fn next_usize(&mut self) -> usize {
            self.next_u64() as usize
        }
    }
}
use xor_shift_64::XorShift64;

mod rooted_tree {
    use std::mem::swap;

    use crate::union_find::UnionFind;
    pub struct RootedTree {
        n: usize,
        doubling_bit_width: usize,
        root: usize,
        rise_tbl: Vec<Vec<Option<usize>>>,
        dist: Vec<Option<i64>>,
        step: Vec<Option<usize>>,
        pub graph: Vec<Vec<(i64, usize)>>,
        edge_cnt: usize,
        uf: UnionFind,
    }
    impl RootedTree {
        pub fn new(n: usize, root: usize) -> RootedTree {
            let mut doubling_bit_width = 1;
            while (1 << doubling_bit_width) < n {
                doubling_bit_width += 1;
            }
            RootedTree {
                n,
                doubling_bit_width,
                root,
                rise_tbl: vec![vec![None; n]; doubling_bit_width],
                dist: vec![None; n],
                step: vec![None; n],
                graph: vec![vec![]; n],
                edge_cnt: 0,
                uf: UnionFind::new(n),
            }
        }
        pub fn unite(&mut self, a: usize, b: usize) {
            self.unite_with_distance(a, b, 1);
        }
        pub fn unite_with_distance(&mut self, a: usize, b: usize, delta: i64) {
            self.graph[a].push((delta, b));
            self.graph[b].push((delta, a));
            self.edge_cnt += 1;
            self.uf.unite(a, b);
            if self.edge_cnt >= self.n - 1 {
                if self.uf.group_num() != 1 {
                    panic!("nodes are NOT connected into one union.")
                }
                self.analyze(self.root);
            }
        }
        pub fn stepback(&self, from: usize, step: usize) -> usize {
            let mut v = from;
            for d in (0..self.doubling_bit_width - 1).rev() {
                if ((step >> d) & 1) != 0 {
                    v = self.rise_tbl[d][v].unwrap();
                }
            }
            v
        }
        fn dfs(
            v: usize,
            pre: Option<usize>,
            graph: &Vec<Vec<(i64, usize)>>,
            dist: &mut Vec<Option<i64>>,
            step: &mut Vec<Option<usize>>,
            rise_tbl: &mut Vec<Vec<Option<usize>>>,
        ) {
            for (delta, nv) in graph[v].iter() {
                if let Some(pre) = pre {
                    if *nv == pre {
                        continue;
                    }
                }
                if dist[*nv].is_none() {
                    dist[*nv] = Some(dist[v].unwrap() + *delta);
                    step[*nv] = Some(step[v].unwrap() + 1);
                    rise_tbl[0][*nv] = Some(v);
                    Self::dfs(*nv, Some(v), graph, dist, step, rise_tbl);
                }
            }
        }
        fn analyze(&mut self, root: usize) {
            self.dist[root] = Some(0);
            self.step[root] = Some(0);
            self.rise_tbl[0][root] = Some(root);
            Self::dfs(
                root,
                None,
                &self.graph,
                &mut self.dist,
                &mut self.step,
                &mut self.rise_tbl,
            );
            // doubling
            for d in (0..self.doubling_bit_width).skip(1) {
                for v in 0_usize..self.n {
                    self.rise_tbl[d][v] = self.rise_tbl[d - 1][self.rise_tbl[d - 1][v].unwrap()];
                }
            }
        }
        pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
            if self.step[a] > self.step[b] {
                swap(&mut a, &mut b);
            }
            assert!(self.step[a] <= self.step[b]);
            // bring up the deeper one to the same level of the shallower one.
            for d in (0..self.doubling_bit_width).rev() {
                let rise_v = self.rise_tbl[d][b].unwrap();
                if self.step[rise_v] >= self.step[a] {
                    b = rise_v;
                }
            }
            assert!(self.step[a] == self.step[b]);
            if a != b {
                // simultaneously rise to the previous level of LCA.
                for d in (0..self.doubling_bit_width).rev() {
                    if self.rise_tbl[d][a] != self.rise_tbl[d][b] {
                        a = self.rise_tbl[d][a].unwrap();
                        b = self.rise_tbl[d][b].unwrap();
                    }
                }
                // 1-step higher level is LCA.
                a = self.rise_tbl[0][a].unwrap();
                b = self.rise_tbl[0][b].unwrap();
            }
            assert!(a == b);
            a
        }
        pub fn distance(&self, a: usize, b: usize) -> i64 {
            let lca_v = self.lca(a, b);
            self.dist[a].unwrap() + self.dist[b].unwrap() - 2 * self.dist[lca_v].unwrap()
        }
    }
}
use rooted_tree::RootedTree;

mod btree_map_binary_search {
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Included, Unbounded};
    pub trait BTreeMapBinarySearch<K, V> {
        fn greater_equal(&self, key: &K) -> Option<(&K, &V)>;
        fn greater_than(&self, key: &K) -> Option<(&K, &V)>;
        fn less_equal(&self, key: &K) -> Option<(&K, &V)>;
        fn less_than(&self, key: &K) -> Option<(&K, &V)>;
    }
    impl<K: Ord, V> BTreeMapBinarySearch<K, V> for BTreeMap<K, V> {
        fn greater_equal(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Included(key), Unbounded)).next()
        }
        fn greater_than(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Excluded(key), Unbounded)).next()
        }
        fn less_equal(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Unbounded, Included(key))).next_back()
        }
        fn less_than(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Unbounded, Excluded(key))).next_back()
        }
    }
}
use btree_map_binary_search::BTreeMapBinarySearch;

mod btree_set_binary_search {
    use std::collections::BTreeSet;
    use std::ops::Bound::{Excluded, Included, Unbounded};
    pub trait BTreeSetBinarySearch<T> {
        fn greater_equal(&self, key: &T) -> Option<&T>;
        fn greater_than(&self, key: &T) -> Option<&T>;
        fn less_equal(&self, key: &T) -> Option<&T>;
        fn less_than(&self, key: &T) -> Option<&T>;
    }
    impl<T: Ord> BTreeSetBinarySearch<T> for BTreeSet<T> {
        fn greater_equal(&self, key: &T) -> Option<&T> {
            self.range((Included(key), Unbounded)).next()
        }
        fn greater_than(&self, key: &T) -> Option<&T> {
            self.range((Excluded(key), Unbounded)).next()
        }
        fn less_equal(&self, key: &T) -> Option<&T> {
            self.range((Unbounded, Included(key))).next_back()
        }
        fn less_than(&self, key: &T) -> Option<&T> {
            self.range((Unbounded, Excluded(key))).next_back()
        }
    }
}
use btree_set_binary_search::BTreeSetBinarySearch;

mod sort_vec_binary_search {
    static mut VEC_IS_SORTED_ONCE: bool = false;
    #[allow(clippy::type_complexity)]
    fn sorted_binary_search<'a, T: PartialOrd>(
        vec: &'a [T],
        key: &T,
        earlier: fn(&T, &T) -> bool,
    ) -> (Option<(usize, &'a T)>, Option<(usize, &'a T)>) {
        unsafe {
            if !VEC_IS_SORTED_ONCE {
                for i in 1..vec.len() {
                    assert!(vec[i - 1] <= vec[i]);
                }
                VEC_IS_SORTED_ONCE = true;
            }
        }
        if vec.is_empty() {
            return (None, None);
        }

        if !earlier(&vec[0], key) {
            (None, Some((0, &vec[0])))
        } else if earlier(vec.last().unwrap(), key) {
            (Some((vec.len() - 1, &vec[vec.len() - 1])), None)
        } else {
            let mut l = 0;
            let mut r = vec.len() - 1;
            while r - l > 1 {
                let m = (l + r) / 2;
                if earlier(&vec[m], key) {
                    l = m;
                } else {
                    r = m;
                }
            }
            (Some((l, &vec[l])), Some((r, &vec[r])))
        }
    }
    pub trait SortVecBinarySearch<T> {
        #[allow(clippy::type_complexity)]
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn greater_than(&self, key: &T) -> Option<(usize, &T)>;
        fn less_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn less_than(&self, key: &T) -> Option<(usize, &T)>;
    }
    impl<T: Ord> SortVecBinarySearch<T> for Vec<T> {
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).1
        }
        fn greater_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).1
        }
        fn less_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).0
        }
        fn less_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).0
        }
    }
}
use sort_vec_binary_search::SortVecBinarySearch;

mod map_counter {
    use std::cmp::Ord;
    use std::collections::{BTreeMap, HashMap};
    use std::hash::Hash;
    pub trait MapCounter<T> {
        fn incr(&mut self, key: T) -> bool;
        fn incr_by(&mut self, key: T, delta: usize) -> bool;
        fn decr(&mut self, key: &T) -> bool;
        fn decr_by(&mut self, key: &T, delta: usize) -> bool;
    }
    impl<T: Ord + Clone> MapCounter<T> for BTreeMap<T, usize> {
        fn incr(&mut self, key: T) -> bool {
            let stat0 = self.contains_key(&key);
            self.incr_by(key.clone(), 1);
            stat0 != self.contains_key(&key)
        }
        fn incr_by(&mut self, key: T, delta: usize) -> bool {
            let stat0 = self.contains_key(&key);
            *self.entry(key.clone()).or_insert(0) += delta;
            stat0 != self.contains_key(&key)
        }
        fn decr(&mut self, key: &T) -> bool {
            let stat0 = self.contains_key(key);
            self.decr_by(key, 1);
            stat0 != self.contains_key(key)
        }
        fn decr_by(&mut self, key: &T, delta: usize) -> bool {
            let stat0 = self.contains_key(key);
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
            stat0 != self.contains_key(key)
        }
    }
    impl<T: Clone + Hash + Eq> MapCounter<T> for HashMap<T, usize> {
        fn incr(&mut self, key: T) -> bool {
            let stat0 = self.contains_key(&key);
            self.incr_by(key.clone(), 1);
            stat0 != self.contains_key(&key)
        }
        fn incr_by(&mut self, key: T, delta: usize) -> bool {
            let stat0 = self.contains_key(&key);
            *self.entry(key.clone()).or_insert(0) += delta;
            stat0 != self.contains_key(&key)
        }
        fn decr(&mut self, key: &T) -> bool {
            let stat0 = self.contains_key(key);
            self.decr_by(key, 1);
            stat0 != self.contains_key(key)
        }
        fn decr_by(&mut self, key: &T, delta: usize) -> bool {
            let stat0 = self.contains_key(key);
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
            stat0 != self.contains_key(key)
        }
    }
}
use map_counter::MapCounter;

mod usize_move_delta {
    pub trait MoveDelta<T> {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize>;
    }
    impl<T: Copy + Into<i64>> MoveDelta<T> for usize {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize> {
            let delta: i64 = delta.into();
            let added: i64 = self as i64 + delta;
            let lim_lo: i64 = lim_lo as i64;
            let lim_hi: i64 = lim_hi as i64;
            if (lim_lo <= added) && (added <= lim_hi) {
                Some(added as usize)
            } else {
                None
            }
        }
    }
}
use usize_move_delta::MoveDelta;

fn exit_by<T: std::fmt::Display>(msg: T) {
    println!("{}", msg);
    std::process::exit(0);
}

mod flow {
    use crate::change_min_max::ChangeMinMax;
    use std::cmp::Reverse;
    use std::collections::{BinaryHeap, VecDeque};
    #[derive(Clone, Copy)]
    pub struct Edge {
        pub to: usize,
        pub rev_idx: usize, // index of paired edge at node "to".
        pub cap: i64,       // immutable capacity, s.t. flow <= cap
        pub flow: i64,      // flow can be negative.
        pub cost: i64,      // for min-cost flow
    }
    pub struct Flow {
        pub g: Vec<Vec<Edge>>,
        flow_lb_sum: i64,
        neg_cost_any: bool,
    }
    impl Flow {
        pub fn new(n: usize) -> Self {
            Self {
                g: vec![vec![]; n + 2],
                flow_lb_sum: 0,
                neg_cost_any: false,
            }
        }
        pub fn add_edge(&mut self, from: usize, to: usize, cap: i64) {
            self.add_cost_edge(from, to, cap, 0);
        }
        pub fn add_flowbound_edge(&mut self, from: usize, to: usize, cap_min: i64, cap_max: i64) {
            self.add_flowbound_cost_edge(from, to, cap_min, cap_max, 0);
        }
        pub fn add_flowbound_cost_edge(
            &mut self,
            from: usize,
            to: usize,
            cap_min: i64,
            cap_max: i64,
            cost: i64,
        ) {
            self.add_cost_edge(from, to, cap_max - cap_min, cost);
            if cap_min > 0 {
                self.flow_lb_sum += cap_min;
                let dummy_src = self.g.len() - 2;
                self.add_cost_edge(dummy_src, to, cap_min, cost);
                let dummy_dst = self.g.len() - 1;
                self.add_cost_edge(from, dummy_dst, cap_min, cost);
            }
        }
        pub fn add_cost_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) {
            let rev_idx = self.g[to].len();
            self.g[from].push(Edge {
                to,
                rev_idx,
                cap,
                flow: 0,
                cost,
            });
            let rev_idx = self.g[from].len() - 1;
            self.g[to].push(Edge {
                to: from,
                rev_idx,
                cap: 0,
                flow: 0,
                cost: -cost,
            });
            if cost < 0 {
                self.neg_cost_any = true;
            }
        }
        fn bfs(g: &[Vec<Edge>], source: usize) -> Vec<Option<usize>> {
            let mut level = vec![None; g.len()];
            level[source] = Some(0);
            let mut que = std::collections::VecDeque::new();
            que.push_back(source);
            while let Some(v) = que.pop_front() {
                let nxt_level = level[v].unwrap() + 1;
                for edge in g[v].iter().copied() {
                    if level[edge.to].is_none() && (edge.flow < edge.cap) {
                        level[edge.to] = Some(nxt_level);
                        que.push_back(edge.to);
                    }
                }
            }
            level
        }
        fn dfs(
            g: &mut [Vec<Edge>],
            v: usize,
            sink: usize,
            flow: i64,
            search_cnt: &mut [usize],
            level: &[Option<usize>],
        ) -> i64 {
            if v == sink {
                return flow;
            }
            while search_cnt[v] < g[v].len() {
                let (to, rev_idx, remain_capacity) = {
                    let edge = g[v][search_cnt[v]];
                    (edge.to, edge.rev_idx, edge.cap - edge.flow)
                };
                if let Some(nxt_level) = level[to] {
                    if (level[v].unwrap() < nxt_level) && (remain_capacity > 0) {
                        let additional_flow = Self::dfs(
                            g,
                            to,
                            sink,
                            std::cmp::min(flow, remain_capacity),
                            search_cnt,
                            level,
                        );
                        if additional_flow > 0 {
                            g[v][search_cnt[v]].flow += additional_flow;
                            g[to][rev_idx].flow -= additional_flow;
                            return additional_flow;
                        }
                    }
                }
                search_cnt[v] += 1;
            }
            0
        }
        pub fn max_flow(&mut self, src: usize, dst: usize) -> Option<i64> {
            if self.flow_lb_sum == 0 {
                return Some(self.max_flow_impl(src, dst));
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            if self.max_flow_impl(dummy_src, dummy_dst) != self.flow_lb_sum {
                return None;
            }
            Some(self.max_flow_impl(src, dst))
        }
        pub fn min_cut_split(&self, src: usize) -> Vec<bool> {
            let nm = self.g.len() - 2;
            let mut split = vec![false; nm];
            let mut que = VecDeque::new();
            que.push_back(src);
            while let Some(v) = que.pop_front() {
                for e in self.g[v].iter() {
                    if e.flow >= e.cap || split[e.to] {
                        continue;
                    }
                    split[e.to] = true;
                    que.push_back(e.to);
                }
            }
            split
        }
        fn max_flow_impl(&mut self, source: usize, sink: usize) -> i64 {
            let inf = 1i64 << 60;
            let mut flow = 0;
            loop {
                let level = Self::bfs(&self.g, source);
                if level[sink].is_none() {
                    break;
                }
                let mut search_cnt = vec![0; self.g.len()];
                loop {
                    let additional_flow =
                        Self::dfs(&mut self.g, source, sink, inf, &mut search_cnt, &level);
                    if additional_flow > 0 {
                        flow += additional_flow;
                    } else {
                        break;
                    }
                }
            }
            flow
        }
        pub fn min_cost_flow(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Option<(i64, i64)> {
            if let Some(&(cost, flow)) = self.min_cost_slope_sub(src, dst, flow_lb, flow_ub).last()
            {
                if flow_lb <= flow && flow <= flow_ub {
                    return Some((cost, flow));
                }
            }
            None
        }
        pub fn min_cost_slope(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Vec<(i64, i64)> {
            self.min_cost_slope_sub(src, dst, flow_lb, flow_ub)
        }
        fn min_cost_slope_sub(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Vec<(i64, i64)> {
            if self.flow_lb_sum == 0 {
                return self.min_cost_slope_impl(src, dst, flow_lb, flow_ub);
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            let ds2dt_cost_flow =
                self.min_cost_slope_impl(dummy_src, dummy_dst, self.flow_lb_sum, self.flow_lb_sum);
            let s2t_cost_flow = self.min_cost_slope_impl(src, dst, flow_lb, flow_ub);
            s2t_cost_flow
                .into_iter()
                .zip(ds2dt_cost_flow)
                .map(|((ds2dt_cost, _ds2dt_flow), (s2t_cost, s2t_flow))| {
                    (ds2dt_cost + s2t_cost, s2t_flow)
                })
                .collect::<Vec<_>>()
        }
        fn min_cost_slope_impl(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Vec<(i64, i64)> {
            if self.neg_cost_any {
                self.min_negcost_slope(src, dst, flow_lb, flow_ub)
            } else {
                self.min_poscost_slope(src, dst, flow_lb)
            }
        }
        fn min_negcost_slope(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Vec<(i64, i64)> {
            let mut slope = vec![];
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            loop {
                dist[source] = Some(0);
                let mut update = true;
                while update {
                    update = false;
                    for (v, to) in self.g.iter().enumerate() {
                        if dist[v].is_none() {
                            continue;
                        }
                        for (ei, e) in to.iter().enumerate() {
                            if e.flow >= e.cap {
                                continue;
                            }
                            let nd = dist[v].unwrap() + e.cost;
                            if dist[e.to].chmin(nd) {
                                prev[e.to] = Some((v, ei));
                                update = true;
                            }
                        }
                    }
                }

                if let Some(dist_sink) = dist[sink] {
                    if (flow_now >= flow_lb) && (dist_sink > 0) {
                        break;
                    }
                    let mut delta_flow = flow_ub - flow_now;
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            let e = &self.g[pv][pei];
                            delta_flow.chmin(e.cap - e.flow);
                            v = pv;
                        }
                    }
                    if delta_flow == 0 {
                        break;
                    }
                    min_cost += delta_flow * dist_sink;
                    flow_now += delta_flow;
                    slope.push((min_cost, flow_now));
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            self.g[pv][pei].flow += delta_flow;
                            let rev_idx = self.g[pv][pei].rev_idx;
                            self.g[v][rev_idx].flow -= delta_flow;
                            v = pv;
                        }
                    }
                } else {
                    break;
                }

                dist.iter_mut().for_each(|x| *x = None);
                prev.iter_mut().for_each(|x| *x = None);
            }
            slope
        }
        fn min_poscost_slope(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow;
        ) -> Vec<(i64, i64)> {
            let mut slope = vec![];
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut h = vec![0; self.g.len()];
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            while flow_now < flow_lb {
                let mut que = BinaryHeap::new();
                que.push((Reverse(0), source));
                dist[source] = Some(0);
                while let Some((Reverse(d), v)) = que.pop() {
                    if dist[v].unwrap() != d {
                        continue;
                    }
                    for (ei, e) in self.g[v].iter().enumerate() {
                        if e.flow >= e.cap {
                            continue;
                        }
                        let nd = d + e.cost + h[v] - h[e.to];
                        if dist[e.to].chmin(nd) {
                            prev[e.to] = Some((v, ei));
                            que.push((Reverse(nd), e.to));
                        }
                    }
                }
                if dist[sink].is_none() {
                    break;
                }
                h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                    if let Some(d) = d {
                        *h += d
                    }
                });
                let mut delta_flow = flow_lb - flow_now;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow.chmin(e.cap - e.flow);
                        v = pv;
                    }
                }
                min_cost += delta_flow * h[sink];
                flow_now += delta_flow;
                slope.push((min_cost, flow_now));
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }

                dist.iter_mut().for_each(|dist| *dist = None);
                prev.iter_mut().for_each(|dist| *dist = None);
            }
            slope
        }
    }
}
use flow::Flow;

mod dynamic_connectivity {
    #[derive(Clone, Copy, PartialEq)]
    enum SplayDir {
        None = 0,
        Left,
        Right,
    }
    mod euler_step {
        use super::SplayDir;
        #[derive(Clone)]
        pub struct EulerStep {
            // splay
            pub left: *mut EulerStep,
            pub right: *mut EulerStep,
            pub parent: *mut EulerStep,
            // euler tour
            pub from: usize,
            pub to: usize,
            pub size: usize,
            pub at_this_level: bool,
            pub at_this_level_subany: bool,
            pub useless_connected: bool,
            pub useless_connected_subany: bool,
            // state
            value: i64,
            value_sum: i64,
        }
        impl EulerStep {
            pub fn new(from: usize, to: usize) -> Self {
                Self {
                    // splay
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    parent: std::ptr::null_mut(),
                    // euler tour
                    from,
                    to,
                    size: if from == to { 1 } else { 0 },
                    at_this_level: from < to,
                    at_this_level_subany: from < to,
                    useless_connected: false,
                    useless_connected_subany: false,
                    value: 0,
                    value_sum: 0,
                }
            }
            fn root(&mut self) -> *mut EulerStep {
                let mut t = self as *mut Self;
                unsafe {
                    while !(*t).parent.is_null() {
                        t = (*t).parent;
                    }
                }
                t
            }
            pub fn same(s: *mut Self, t: *mut Self) -> bool {
                if s.is_null() {
                    debug_assert!(!t.is_null());
                    return false;
                }
                if t.is_null() {
                    debug_assert!(!s.is_null());
                    return false;
                }
                unsafe {
                    (*s).splay();
                    (*t).splay();
                    (*s).root() == (*t).root()
                }
            }
            pub fn update(&mut self) {
                self.size = if self.from == self.to { 1 } else { 0 };
                self.at_this_level_subany = self.at_this_level;
                self.useless_connected_subany = self.useless_connected;
                self.value_sum = self.value;
                let left = self.left;
                let right = self.right;
                unsafe {
                    if !left.is_null() {
                        self.size += (*left).size;
                        self.at_this_level_subany =
                            self.at_this_level_subany || (*left).at_this_level_subany;
                        self.useless_connected_subany =
                            self.useless_connected_subany || (*left).useless_connected_subany;
                        self.value_sum += (*left).value_sum;
                    }
                    if !right.is_null() {
                        self.size += (*right).size;
                        self.at_this_level_subany =
                            self.at_this_level_subany || (*right).at_this_level_subany;
                        self.useless_connected_subany =
                            self.useless_connected_subany || (*right).useless_connected_subany;
                        self.value_sum += (*right).value_sum;
                    }
                }
            }
            pub fn splay(&mut self) {
                while self.for_parent() != SplayDir::None {
                    unsafe {
                        let p = self.parent;
                        let p_for_pp = (*p).for_parent();
                        if p_for_pp == SplayDir::None {
                            // zig
                            self.rotate();
                        } else if p_for_pp == self.for_parent() {
                            // zig zig
                            (*p).rotate();
                            self.rotate();
                        } else {
                            // zig zag
                            self.rotate();
                            self.rotate();
                        }
                    }
                }
            }
            fn for_parent(&mut self) -> SplayDir {
                if self.parent.is_null() {
                    SplayDir::None
                } else {
                    unsafe {
                        let me = self as *mut Self;
                        if (*self.parent).left == me {
                            SplayDir::Left
                        } else {
                            debug_assert!((*self.parent).right == me);
                            SplayDir::Right
                        }
                    }
                }
            }
            fn rotate(&mut self) {
                let p = self.parent;
                debug_assert!(!p.is_null());
                let me = self as *mut Self;
                unsafe {
                    debug_assert!((*me).for_parent() != SplayDir::None);
                    let pp = (*p).parent;
                    let c;
                    if (*me).for_parent() == SplayDir::Left {
                        c = (*me).right;
                        (*me).right = p;
                        (*p).left = c;
                    } else {
                        c = (*me).left;
                        (*me).left = p;
                        (*p).right = c;
                    }
                    if !pp.is_null() {
                        if (*pp).left == p {
                            (*pp).left = me;
                        } else {
                            (*pp).right = me;
                        }
                    }
                    (*me).parent = pp;
                    (*p).parent = me;
                    if !c.is_null() {
                        (*c).parent = p;
                    }
                    (*p).update();
                }
                self.update();
            }
            pub fn merge(mut s: *mut Self, mut t: *mut Self) -> *mut Self {
                if s.is_null() {
                    debug_assert!(!t.is_null());
                    return t;
                }
                if t.is_null() {
                    debug_assert!(!s.is_null());
                    return s;
                }
                unsafe {
                    s = (*s).root();
                    t = (*t).root();
                    while !(*s).right.is_null() {
                        s = (*s).right;
                    }
                    (*s).splay();
                    (*s).right = t;
                    (*t).parent = s;
                    (*s).update();
                }
                s
            }
            pub fn split(s: *mut Self) -> (*mut Self, *mut Self) // (..s, s..)
            {
                unsafe {
                    (*s).splay();
                    let t = (*s).left;
                    if !t.is_null() {
                        (*t).parent = std::ptr::null_mut();
                    }
                    (*s).left = std::ptr::null_mut();
                    (*s).update();
                    (t, s)
                }
            }
            pub fn set_value(&mut self, value: i64) {
                self.value = value;
            }
            pub fn get_value(&self) -> i64 {
                self.value
            }
            pub fn get_sum(&self) -> i64 {
                self.value_sum
            }
        }
    }
    mod euler_tree {
        use super::euler_step::EulerStep;
        use std::collections::HashMap;
        pub struct EulerTour {
            tour: Vec<HashMap<usize, Box<EulerStep>>>,
        }
        impl EulerTour {
            pub fn new(n: usize) -> Self {
                Self {
                    tour: (0..n)
                        .map(|i| {
                            let mut mp = HashMap::new();
                            mp.insert(i, Box::new(EulerStep::new(i, i)));
                            mp
                        })
                        .collect::<Vec<_>>(),
                }
            }
            pub fn get_node(&mut self, from: usize, to: usize) -> *mut EulerStep {
                self.tour[from]
                    .entry(to)
                    .or_insert_with(|| Box::new(EulerStep::new(from, to)));
                &mut **self.tour[from].get_mut(&to).unwrap()
            }
            #[allow(unused_assignments)]
            fn re_tour(s: *mut EulerStep) {
                let (s0, s1) = EulerStep::split(s);
                EulerStep::merge(s1, s0);
            }
            pub fn same(&mut self, a: usize, b: usize) -> bool {
                let a = self.get_node(a, a);
                let b = self.get_node(b, b);
                EulerStep::same(a, b)
            }
            #[allow(unused_assignments)]
            pub fn unite(&mut self, a: usize, b: usize) -> bool {
                if self.same(a, b) {
                    return false;
                }
                let aa = self.get_node(a, a);
                Self::re_tour(aa);
                let bb = self.get_node(b, b);
                Self::re_tour(bb);

                let ab = self.get_node(a, b);
                let ba = self.get_node(b, a);
                let aa_ab = EulerStep::merge(aa, ab);
                let bb_ba = EulerStep::merge(bb, ba);
                let _ = EulerStep::merge(aa_ab, bb_ba);
                true
            }
            fn remove_split(&mut self, from: usize, to: usize) -> (*mut EulerStep, *mut EulerStep) {
                let c = self.get_node(from, to);
                unsafe {
                    (*c).splay();
                    let left = (*c).left;
                    let right = (*c).right;
                    if !left.is_null() {
                        (*left).parent = std::ptr::null_mut();
                    }
                    if !right.is_null() {
                        (*right).parent = std::ptr::null_mut();
                    }
                    assert!(self.tour[from].remove(&to).is_some());
                    (left, right)
                }
            }
            pub fn cut(&mut self, a: usize, b: usize) -> bool {
                if !self.tour[a].contains_key(&b) {
                    return false;
                }
                let (xxa, bxx) = self.remove_split(a, b);
                if EulerStep::same(xxa, self.get_node(b, a)) {
                    let (xxb, _axxa) = self.remove_split(b, a);
                    let _ = EulerStep::merge(bxx, xxb);
                } else {
                    let (_bxxb, axx) = self.remove_split(b, a);
                    let _ = EulerStep::merge(axx, xxa);
                }
                true
            }
            pub fn get_size(&mut self, a: usize) -> usize {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.size
            }
            pub fn extract_level_match(t: *mut EulerStep) -> Option<(usize, usize)> {
                unsafe {
                    if t.is_null() || !(*t).at_this_level_subany {
                        return None;
                    }
                    if (*t).at_this_level {
                        (*t).splay();
                        (*t).at_this_level = false;
                        (*t).update();
                        return Some(((*t).from, (*t).to));
                    }
                    let left = (*t).left;
                    if let Some(ret) = Self::extract_level_match(left) {
                        return Some(ret);
                    }
                    let right = (*t).right;
                    if let Some(ret) = Self::extract_level_match(right) {
                        return Some(ret);
                    }
                    None
                }
            }
            pub fn extract_useless_connected(t: *mut EulerStep) -> Option<usize> {
                unsafe {
                    if t.is_null() || !(*t).useless_connected_subany {
                        return None;
                    }
                    if (*t).useless_connected {
                        (*t).splay();
                        return Some((*t).from);
                    }
                    let left = (*t).left;
                    if let Some(ret) = Self::extract_useless_connected(left) {
                        return Some(ret);
                    }
                    let right = (*t).right;
                    if let Some(ret) = Self::extract_useless_connected(right) {
                        return Some(ret);
                    }
                    None
                }
            }
            pub fn update_useless_connected(&mut self, a: usize, b: bool) {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.useless_connected = b;
                node.update();
            }
            pub fn set_value(&mut self, a: usize, value: i64) {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.set_value(value);
                node.update();
            }
            pub fn get_value(&self, a: usize) -> i64 {
                self.tour[a][&a].get_value()
            }
            pub fn get_sum(&mut self, a: usize) -> i64 {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.get_sum()
            }
        }
    }
    use self::euler_step::EulerStep;
    use self::euler_tree::EulerTour;
    use std::collections::HashSet;
    pub struct DynamicConnectivity {
        n: usize,
        trees: Vec<EulerTour>,
        useless_edges: Vec<Vec<HashSet<usize>>>,
        grp_num: usize,
    }
    impl DynamicConnectivity {
        pub fn new(n: usize) -> Self {
            Self {
                n,
                trees: vec![EulerTour::new(n)],
                useless_edges: vec![vec![HashSet::new(); n]],
                grp_num: n,
            }
        }
        pub fn unite(&mut self, a: usize, b: usize) -> bool {
            if a == b {
                return false;
            }
            if self.trees[0].unite(a, b) {
                self.grp_num -= 1;
                return true;
            }
            assert!(self.useless_edges[0][a].insert(b));
            assert!(self.useless_edges[0][b].insert(a));
            if self.useless_edges[0][a].len() == 1 {
                self.trees[0].update_useless_connected(a, true);
            }
            if self.useless_edges[0][b].len() == 1 {
                self.trees[0].update_useless_connected(b, true);
            }
            false
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.trees[0].same(a, b)
        }
        pub fn cut(&mut self, a: usize, b: usize) -> bool {
            if a == b {
                return false;
            }
            self.trees
                .iter_mut()
                .zip(self.useless_edges.iter_mut())
                .for_each(|(tree, edges)| {
                    for (a, b) in [(a, b), (b, a)].iter().copied() {
                        if edges[a].remove(&b) && edges[a].is_empty() {
                            tree.update_useless_connected(a, false);
                        }
                    }
                });
            let org_level_len = self.trees.len();
            for level in (0..org_level_len).rev() {
                if self.trees[level].cut(a, b) {
                    // tree-connectivity changed.
                    if level == org_level_len - 1 {
                        self.trees.push(EulerTour::new(self.n));
                        self.useless_edges.push(vec![HashSet::new(); self.n]);
                    }
                    // try reconnect
                    self.trees.iter_mut().take(level).for_each(|tree| {
                        tree.cut(a, b);
                    });
                    let reconstruct = self.reconstruct_connectivity(a, b, level);
                    if !reconstruct {
                        self.grp_num += 1;
                    }
                    return !reconstruct;
                }
            }
            false
        }
        fn reconstruct_connectivity(&mut self, mut a: usize, mut b: usize, level: usize) -> bool {
            for i in (0..=level).rev() {
                if self.trees[i].get_size(a) > self.trees[i].get_size(b) {
                    std::mem::swap(&mut a, &mut b);
                }
                // edge update
                unsafe {
                    let node_a = self.trees[i].get_node(a, a);
                    (*node_a).splay();
                    while let Some((lup_a, lup_b)) = EulerTour::extract_level_match(node_a) {
                        self.trees[i + 1].unite(lup_a, lup_b);
                        (*node_a).splay();
                    }
                    // try_reconnect in euler tour
                    while let Some(x) = EulerTour::extract_useless_connected(node_a) {
                        while let Some(&y) = self.useless_edges[i][x].iter().next() {
                            for (x, y) in [(x, y), (y, x)].iter().copied() {
                                assert!(self.useless_edges[i][x].remove(&y));
                                if self.useless_edges[i][x].is_empty() {
                                    self.trees[i].update_useless_connected(x, false);
                                }
                            }
                            if self.trees[i].same(x, y) {
                                for (x, y) in [(x, y), (y, x)].iter().copied() {
                                    self.useless_edges[i + 1][x].insert(y);
                                    if self.useless_edges[i + 1][x].len() == 1 {
                                        self.trees[i + 1].update_useless_connected(x, true);
                                    }
                                }
                            } else {
                                for j in 0..=i {
                                    self.trees[j].unite(x, y);
                                }
                                return true;
                            }
                        }
                        (*node_a).splay();
                    }
                }
            }
            false
        }
        pub fn set_value(&mut self, x: usize, value: i64) {
            self.trees[0].set_value(x, value);
        }
        pub fn get_value(&self, x: usize) -> i64 {
            self.trees[0].get_value(x)
        }
        pub fn group_size(&mut self, x: usize) -> usize {
            self.trees[0].get_size(x)
        }
        pub fn group_num(&self) -> usize {
            self.grp_num
        }
        pub fn get_sum(&mut self, x: usize) -> i64 {
            self.trees[0].get_sum(x)
        }
    }
    fn get_level_num(dynamic_connectivity: &DynamicConnectivity) -> usize {
        dynamic_connectivity.trees.len()
    }
    #[cfg(test)]
    mod tests {
        use crate::dynamic_connectivity::get_level_num;

        use super::DynamicConnectivity;
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        use std::collections::BTreeSet;
        const N: usize = 10;
        fn trial(ques: Vec<(usize, usize, usize)>) {
            let mut dc = DynamicConnectivity::new(N);
            let mut g = vec![BTreeSet::new(); N];
            let mut log_n = 1usize;
            while (1usize << log_n) < N {
                log_n += 1;
            }
            for (t, a, b) in ques {
                match t {
                    0 => {
                        dc.unite(a, b);
                        g[a].insert(b);
                        g[b].insert(a);
                    }
                    1 => {
                        dc.cut(a, b);
                        g[a].remove(&b);
                        g[b].remove(&a);
                    }
                    _ => unreachable!(),
                }
                let mut uf = super::super::UnionFind::new(N);
                for a in 0..N {
                    for b in g[a].iter().copied() {
                        uf.unite(a, b);
                    }
                }
                assert_eq!(uf.group_num(), dc.group_num());
                for j in 0..N {
                    for i in 0..N {
                        assert_eq!(dc.same(i, j), uf.same(i, j));
                    }
                    assert_eq!(uf.group_size(j), dc.group_size(j));
                }
                assert!(get_level_num(&dc) <= log_n);
            }
        }
        #[test]
        fn random_operation() {
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for _ in 0..100 {
                let ques = {
                    let mut es = vec![BTreeSet::new(); N];
                    let mut ques = vec![];
                    while ques.len() < N * N {
                        let t = rng.gen::<usize>() % 2;
                        let a = rng.gen::<usize>() % N;
                        let b = (a + 1 + rng.gen::<usize>() % (N - 1)) % N;
                        match t {
                            0 => {
                                // unite
                                if es[a].contains(&b) {
                                    continue;
                                }
                                es[a].insert(b);
                                es[b].insert(a);
                                ques.push((t, a, b));
                            }
                            1 => {
                                // cut
                                if !es[a].contains(&b) {
                                    continue;
                                }
                                es[a].remove(&b);
                                es[b].remove(&a);
                                ques.push((t, a, b));
                            }
                            _ => unreachable!(),
                        }
                    }
                    ques
                };
                trial(ques);
            }
        }
    }
}
use dynamic_connectivity::DynamicConnectivity;

mod procon_reader {
    use std::fmt::Debug;
    use std::io::Read;
    use std::str::FromStr;
    pub fn read<T: FromStr>() -> T
    where
        <T as FromStr>::Err: Debug,
    {
        let stdin = std::io::stdin();
        let mut stdin_lock = stdin.lock();
        let mut u8b: [u8; 1] = [0];
        loop {
            let mut buf: Vec<u8> = Vec::with_capacity(16);
            loop {
                let res = stdin_lock.read(&mut u8b);
                if res.unwrap_or(0) == 0 || u8b[0] <= b' ' {
                    break;
                } else {
                    buf.push(u8b[0]);
                }
            }
            if !buf.is_empty() {
                let ret = String::from_utf8(buf).unwrap();
                return ret.parse().unwrap();
            }
        }
    }
    pub fn read_vec<T: std::str::FromStr>(n: usize) -> Vec<T>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..n).map(|_| read::<T>()).collect::<Vec<T>>()
    }
    pub fn read_mat<T: std::str::FromStr>(h: usize, w: usize) -> Vec<Vec<T>>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..h).map(|_| read_vec::<T>(w)).collect::<Vec<_>>()
    }
}
use procon_reader::*;
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

fn main() {
    //solver::Solver::random_search();
    solver::Solver::new().solve();
}

mod solver {
    use super::*;
    type Set<K> = BTreeSet<K>;
    type Map<K, V> = BTreeMap<K, V>;
    const RIGHT: usize = 0;
    const UPPER: usize = 1;
    const LEFT: usize = 2;
    const LOWER: usize = 3;
    const ROT: [[usize; 4]; 4] = [
        // RIGHT ->
        [0, 1, 2, 1],
        // UPPER ->
        [1, 0, 1, 2],
        // LEFT ->
        [2, 1, 0, 1],
        // LOWER ->
        [1, 2, 1, 0],
    ];
    mod state {
        use super::*;
        #[derive(Clone, Debug, PartialEq)]
        pub struct State {
            pub rem: Vec<u32>,
            pub tgt: Vec<u32>,
            pub dir: Vec<usize>,
            pub cap: Vec<u16>,
        }
        impl State {
            pub fn empty(n: usize, arm_num: usize) -> Self {
                State {
                    rem: vec![0; n],
                    tgt: vec![0; n],
                    dir: vec![0; arm_num],
                    cap: vec![0; arm_num],
                }
            }
            pub fn fin(&self) -> bool {
                self.rem.iter().all(|x| *x == 0)
                    && self.tgt.iter().all(|x| *x == 0)
                    && self.cap.iter().all(|&x| x == 0)
            }
            pub fn move_and_update(
                &mut self,
                n: usize,
                arm_shapes: &[ArmShape],
                y: usize,
                x: usize,
            ) -> (usize, usize, Vec<Vec<(usize, u16)>>) {
                let mut rot_and_caprel_cost = vec![0; self.cap.len()];
                let mut gain = 0;
                let mut dir_upd = vec![vec![]; self.cap.len()];
                loop {
                    let mut upd = false;
                    // arm loop
                    for (((arm_cost, dir), (arm_shape, cap)), dir_upd) in rot_and_caprel_cost
                        .iter_mut()
                        .zip(self.dir.iter_mut())
                        .zip(arm_shapes.iter().zip(self.cap.iter_mut()))
                        .zip(dir_upd.iter_mut())
                    {
                        // one arm
                        let mut best_eval = (0, Reverse(0));
                        let mut best_reform = None;
                        // one arm
                        for reform in arm_shape.reforms(*dir) {
                            let mut cap_rsv = Set::new();
                            let mut rel_rsv = Set::new();
                            let mut reform_gain = 0;
                            let mut flips = vec![];
                            for &(rv, (dy, dx)) in reform.pts.iter() {
                                debug_assert!(rv > 0);
                                debug_assert!(arm_shape.g[rv].is_empty());
                                if y as i32 + dy < 0
                                    || y as i32 + dy >= n as i32
                                    || x as i32 + dx < 0
                                    || x as i32 + dx >= n as i32
                                {
                                    continue;
                                }
                                let ny = (y as i32 + dy) as usize;
                                let nx = (x as i32 + dx) as usize;
                                if (((*cap >> rv) & 1) == 0)
                                    && (((self.rem[ny] >> nx) & 1) != 0)
                                    && !cap_rsv.contains(&(ny, nx))
                                {
                                    // capture.
                                    reform_gain += 1;
                                    flips.push((rv, (ny, nx)));
                                    cap_rsv.insert((ny, nx));
                                } else if (((*cap >> rv) & 1) != 0)
                                    && (((self.tgt[ny] >> nx) & 1) != 0)
                                    && !rel_rsv.contains(&(ny, nx))
                                {
                                    // release
                                    reform_gain += 1;
                                    flips.push((rv, (ny, nx)));
                                    rel_rsv.insert((ny, nx));
                                }
                            }
                            if best_eval.chmax((reform_gain, Reverse(reform.cost))) {
                                best_reform = Some((reform, flips));
                            }
                        }
                        if let Some((reform, flips)) = best_reform {
                            upd = true;
                            let mut flip = 0;
                            debug_assert!(!flips.is_empty());
                            for (flip_rv, (y, x)) in flips {
                                if ((*cap >> flip_rv) & 1) == 0 {
                                    debug_assert!(((self.rem[y] >> x) & 1) != 0);
                                    self.rem[y] &= !(1 << x);
                                } else {
                                    debug_assert!(((*cap >> flip_rv) & 1) == 1);
                                    debug_assert!(((self.tgt[y] >> x) & 1) != 0);
                                    self.tgt[y] &= !(1 << x);
                                }
                                flip |= 1u16 << flip_rv;
                            }
                            *cap ^= flip;
                            *arm_cost += max(1, reform.cost);
                            *dir = reform.dir;
                            gain += best_eval.0;
                            dir_upd.push((reform.dir, flip));
                        }
                    }
                    if !upd {
                        break;
                    }
                }
                (
                    gain,
                    rot_and_caprel_cost.into_iter().max().unwrap(),
                    dir_upd,
                )
            }
        }
    }
    use num::PrimInt;
    use state::State;
    mod arm_shape {
        use super::*;
        #[derive(Clone, Debug, PartialEq)]
        pub struct Reform {
            pub pts: Vec<(usize, (i32, i32))>,
            pub cost: usize,
            pub dir: usize,
        }
        pub struct ArmShape {
            reforms: Map<usize, Vec<Reform>>,
            pub g: Vec<Vec<(usize, i32)>>,
            pub par: Vec<(usize, i32)>,
            pub abs_vs: Vec<usize>,
            terminal: u16,
            len: usize,
        }
        impl ArmShape {
            pub fn new(sz: usize, v_next_root: usize, g0: &[Vec<(usize, i32)>]) -> Self {
                let (g, par, abs_vs, terminal, len) = {
                    let mut g = vec![vec![]; sz];
                    let mut par = vec![(0, 0)];
                    let mut terminal = 0;
                    let mut len = 0;
                    let mut abs_vs = vec![0];
                    let mut abs_vs_rev = vec![0; sz];
                    let mut que = vec![0];
                    while let Some(abs_v0) = que.pop() {
                        let v0 = abs_vs_rev[abs_v0];
                        if g0[abs_v0].is_empty() {
                            terminal |= 1u16 << v0;
                        }
                        for &(abs_v1, d) in g0[abs_v0].iter() {
                            if (abs_v0 == 0) && (abs_v1 != v_next_root) {
                                continue;
                            }
                            len += 1;
                            debug_assert_eq!(len, par.len());
                            par.push((v0, d));
                            g[v0].push((len, d));
                            que.push(abs_v1);
                            abs_vs.push(abs_v1);
                            abs_vs_rev[abs_v1] = len;
                        }
                    }
                    (g, par, abs_vs, terminal, len)
                };
                fn dir_to_point(
                    dir: usize,
                    par: &[(usize, i32)],
                    terminal: u16,
                ) -> Vec<(usize, (i32, i32))> {
                    let mut termintals = vec![];
                    let mut pos = vec![(0, 0); par.len()];
                    for (v1, &(v0, d)) in par.iter().enumerate().skip(1) {
                        let dir = ArmShape::extract_dir1(dir, v1);
                        let (mut y, mut x) = pos[v0];
                        match dir {
                            RIGHT => {
                                x += d;
                            }
                            LEFT => {
                                x -= d;
                            }
                            UPPER => {
                                y -= d;
                            }
                            LOWER => {
                                y += d;
                            }
                            _ => unreachable!(),
                        }
                        pos[v1] = (y, x);
                        if ((terminal >> v1) & 1) != 0 {
                            termintals.push((v1, pos[v1]));
                        }
                    }
                    termintals
                }
                let points = (0..(1 << (2 * len)))
                    .map(|dir| (dir, dir_to_point(dir, &par, terminal)))
                    .collect_vec();
                let reforms = points
                    .iter()
                    .map(|(dir0, _)| {
                        (
                            *dir0,
                            points
                                .iter()
                                .map(|(dir, pts)| {
                                    let cost = Self::rot_cost(&g, *dir0, *dir);
                                    Reform {
                                        pts: pts.clone(),
                                        cost,
                                        dir: *dir,
                                    }
                                })
                                .collect_vec(),
                        )
                    })
                    .collect::<Map<_, _>>();
                Self {
                    reforms,
                    g,
                    par,
                    abs_vs,
                    terminal,
                    len,
                }
            }
            #[inline(always)]
            fn extract_dir1(dirs: usize, v: usize) -> usize {
                (dirs >> (2 * (v - 1))) & 3
            }
            #[inline(always)]
            pub fn rot_cmd(&self, dir0: usize, dir1: usize) -> (&[usize], Vec<Vec<char>>) {
                let mut cmd = vec![vec![]; 1 + self.len()];
                let mut que = vec![0];
                while let Some(v0) = que.pop() {
                    for &(v1, _) in self.g[v0].iter() {
                        let d0 = if v0 == 0 {
                            dir0 & 3
                        } else {
                            let pd0 = Self::extract_dir1(dir0, v0);
                            let nd0 = Self::extract_dir1(dir0, v1);
                            let del0 = (nd0 + 4 - pd0) % 4;
                            let pd1 = Self::extract_dir1(dir1, v0);
                            (pd1 + del0) % 4
                        };
                        let d1 = Self::extract_dir1(dir1, v1);
                        let t = (d1 + 4 - d0) % 4;
                        cmd[v1] = match t {
                            0 => vec![],
                            1 => vec!['L'],
                            2 => vec!['R'; 2],
                            3 => vec!['R'],
                            _ => unreachable!(),
                        };
                        que.push(v1);
                    }
                }
                (&self.abs_vs, cmd)
            }
            #[inline(always)]
            pub fn len(&self) -> usize {
                self.len
            }
            #[inline(always)]
            pub fn reforms(&self, dir: usize) -> &[Reform] {
                &self.reforms[&dir]
            }
            //#[inline(always)]
            pub fn rot_cost(g: &[Vec<(usize, i32)>], dir0: usize, dir1: usize) -> usize {
                let mut cost = 0;
                let mut que = vec![0];
                while let Some(v0) = que.pop() {
                    for &(v1, _) in g[v0].iter() {
                        let d0 = if v0 == 0 {
                            dir0 & 3
                        } else {
                            let pd0 = Self::extract_dir1(dir0, v0);
                            let nd0 = Self::extract_dir1(dir0, v1);
                            let del0 = (nd0 + 4 - pd0) % 4;
                            let pd1 = Self::extract_dir1(dir1, v0);
                            (pd1 + del0) % 4
                        };
                        let d1 = Self::extract_dir1(dir1, v1);
                        cost.chmax(ROT[d0][d1]);
                        que.push(v1);
                    }
                }
                cost
            }
            pub fn set_shape(&self, shape: &mut [(usize, i32)]) {
                for v1 in 1..self.par.len() {
                    let (v0, d) = self.par[v1];
                    shape[self.abs_vs[v1]] = (self.abs_vs[v0], d);
                }
            }
        }
    }
    use arm_shape::ArmShape;
    const NMIN: usize = 15;
    const NMAX: usize = 30;
    const VMIN: usize = 5;
    const VMAX: usize = 15;
    const PRESOL: usize = 20;
    const PMIN: usize = PRESOL / 10;
    const PMAX: usize = PRESOL / 2;
    pub struct Solver {
        t0: Instant,
        n: usize,
        m: usize,
        v: usize,
        s: Vec<u32>,
        t: Vec<u32>,
        cmd_base: Vec<Vec<Vec<char>>>,
    }
    impl Solver {
        pub fn new() -> Self {
            let t0 = Instant::now();
            let n = read::<usize>();
            let mut m = read::<usize>();
            let v = read::<usize>();
            let mut s = vec![0; n];
            for y in 0..n {
                for (x, v) in read::<String>().chars().enumerate() {
                    if v == '1' {
                        s[y] |= 1 << x;
                    }
                }
            }
            let mut t = vec![0; n];
            for y in 0..n {
                for (x, v) in read::<String>().chars().enumerate() {
                    if v == '1' {
                        t[y] |= 1 << x;
                    }
                }
            }
            let mut cmd_base = vec![vec![vec![]; 4]; 4];
            for d0 in 0..4 {
                for d1 in 0..4 {
                    match ROT[d0][d1] {
                        0 => {
                            //
                        }
                        1 => {
                            if (d0 == RIGHT && d1 == LOWER)
                                || (d0 == LOWER && d1 == LEFT)
                                || (d0 == LEFT && d1 == UPPER)
                                || (d0 == UPPER && d1 == RIGHT)
                            {
                                cmd_base[d0][d1].push('R');
                            } else if (d0 == RIGHT && d1 == UPPER)
                                || (d0 == UPPER && d1 == LEFT)
                                || (d0 == LEFT && d1 == LOWER)
                                || (d0 == LOWER && d1 == RIGHT)
                            {
                                cmd_base[d0][d1].push('L');
                            } else {
                                unreachable!()
                            }
                        }
                        2 => {
                            cmd_base[d0][d1].push('R');
                            cmd_base[d0][d1].push('R');
                        }
                        _ => unreachable!(),
                    }
                }
            }
            for y in 0..n {
                for x in 0..n {
                    if ((s[y] >> x) & 1) != 0 && ((t[y] >> x) & 1) != 0 {
                        s[y] &= !(1 << x);
                        t[y] &= !(1 << x);
                        m -= 1;
                    }
                }
            }
            use num::PrimInt;
            debug_assert_eq!(m, s.iter().map(|x| x.count_ones() as usize).sum::<usize>());
            debug_assert_eq!(m, t.iter().map(|x| x.count_ones() as usize).sum::<usize>());
            Self {
                t0,
                n,
                m,
                v,
                s,
                t,
                cmd_base,
            }
        }
        fn gen_ini(&self) -> (usize, usize) {
            let mut y_sum = 0;
            let mut x_sum = 0;
            for y in 0..self.n {
                for x in 0..self.n {
                    if ((self.s[y] >> x) & 1) != 0 {
                        y_sum += y;
                        x_sum += x;
                    }
                    if ((self.t[y] >> x) & 1) != 0 {
                        y_sum += y;
                        x_sum += x;
                    }
                }
            }
            let y_ave = y_sum / (2 * self.m);
            let x_ave = x_sum / (2 * self.m);
            (y_ave, x_ave)
        }
        pub fn random_search() {
            fn power(x: f64, mut p: u64) -> f64 {
                let mut ret = 1.0;
                let mut mul = x;
                while p > 0 {
                    if (p & 1) != 0 {
                        ret *= mul;
                    }
                    p >>= 1;
                    mul = mul * mul;
                }
                ret
            }
            fn evaluate(
                n: usize,
                p: f64,
                g: &[Vec<(usize, i32)>],
                to: &mut [Vec<u64>],
                to_cnt: &mut u64,
                to1: &mut [Vec<u64>],
                to1_cnt: &mut u64,
            ) -> Option<(f64, i32, i32)> {
                fn dfs(
                    n: usize,
                    q: f64,
                    nv0: usize,
                    v0: usize,
                    g: &[Vec<(usize, i32)>],
                    pos: &mut [(i32, i32)],
                    to_cnt: u64,
                    to: &mut [Vec<u64>],
                    to1_cnt: u64,
                    to1: &mut [Vec<u64>],
                    depth: &[u64],
                    eval0: &mut f64,
                    eval1: &mut i32,
                    terminal_ok: &mut u16,
                ) {
                    let (y0, x0) = pos[v0];
                    if g[v0].is_empty() {
                        // terminal
                        if y0 <= 0 || x0 < 0 {
                            return;
                        }
                        if y0 >= n as i32 || x0 >= n as i32 {
                            return;
                        }
                        if to1[y0 as usize][x0 as usize].chmax(to1_cnt) {
                            *eval0 += 1.0 - power(q, depth[v0]);
                        }
                        if to[y0 as usize][x0 as usize].chmax(to_cnt) {
                            *eval1 += 1;
                        }
                        if (x0 as usize <= n / 2) && (y0 as usize <= n / 2) {
                            *terminal_ok |= 1u16 << v0;
                        }
                    }
                    for &(v1, d) in g[v0].iter() {
                        if v0 == 0 && v1 != nv0 {
                            continue;
                        }
                        for nd in 0..4 {
                            pos[v1] = match nd {
                                0 => (x0 + d, y0),
                                1 => (x0 - d, y0),
                                2 => (x0, y0 + d),
                                3 => (x0, y0 - d),
                                _ => unreachable!(),
                            };
                            dfs(
                                n,
                                q,
                                nv0,
                                v1,
                                g,
                                pos,
                                to_cnt,
                                to,
                                to1_cnt,
                                to1,
                                depth,
                                eval0,
                                eval1,
                                terminal_ok,
                            );
                        }
                    }
                }
                let q = 1.0 - p * 0.5;
                let mut eval0 = 0.0;
                let mut eval1 = 0;
                let mut depth = vec![0u64; g.len()];
                let mut pos = vec![(0, 0); g.len()];
                let mut que = vec![0];
                while let Some(v0) = que.pop() {
                    for &(v1, _d) in g[v0].iter() {
                        depth[v1] = depth[v0] + 1;
                        que.push(v1);
                    }
                }
                let depth = depth;
                let mut terminal_ok = 0;
                *to_cnt += 1;
                for &(nv0, _d0) in g[0].iter() {
                    *to1_cnt += 1;
                    dfs(
                        n,
                        q,
                        nv0,
                        0,
                        &g,
                        &mut pos,
                        *to_cnt,
                        to,
                        *to1_cnt,
                        to1,
                        &depth,
                        &mut eval0,
                        &mut eval1,
                        &mut terminal_ok,
                    );
                }
                for vi in 1..g.len() {
                    if !g[vi].is_empty() {
                        continue;
                    }
                    if ((terminal_ok >> vi) & 1) == 0 {
                        return None;
                    }
                }
                let mut eval2 = None;
                for (y0, to0) in to.iter().take(n).enumerate() {
                    for (x0, _to0) in to0.iter().take(n).filter(|&&to| to == *to_cnt).enumerate() {
                        if (y0, x0) != (0, 0) {
                            eval2.chmin((y0 + x0) as i32);
                        }
                        for (y1, to1) in to.iter().take(n).enumerate() {
                            for (x1, _to1) in
                                to1.iter().take(n).filter(|&&to| to == *to_cnt).enumerate()
                            {
                                if (y0, x0) == (y1, x1) {
                                    continue;
                                }
                                let ev =
                                    (y0 as i32 - y1 as i32).abs() + (x0 as i32 - x1 as i32).abs();
                                eval2.chmin(ev);
                            }
                        }
                    }
                }
                let eval2 = if let Some(eval2) = eval2 { eval2 } else { 0 };
                Some((eval0, eval1, eval2))
            }
            let mut rand = XorShift64::new();
            let mut to = vec![vec![0; NMAX]; NMAX];
            let mut to1 = vec![vec![0; NMAX]; NMAX];
            let mut to_cnt = 0u64;
            let mut to1_cnt = 0u64;
            let mut best =
                vec![vec![vec![None; PMAX - PMIN + 1]; VMAX - VMIN + 1]; NMAX - NMIN + 1];
            let mut best_g = (NMIN..=NMAX)
                .map(|n| {
                    (VMIN..=VMAX)
                        .map(|v| {
                            (PMIN..=PMAX)
                                .map(|pi| {
                                    let mut ls = vec![];
                                    let mut used = 1;
                                    let mut max_sz = 0;
                                    for sz in 1.. {
                                        let nused = used + sz;
                                        if nused > v {
                                            break;
                                        }
                                        used = nused;
                                        ls.push(vec![1; sz]);
                                        max_sz.chmax(sz);
                                    }
                                    let unit = n / max_sz;
                                    debug_assert!(unit <= n);
                                    ls.iter_mut().for_each(|ls| {
                                        ls.iter_mut().for_each(|l| {
                                            *l = unit as i32;
                                        })
                                    });
                                    {
                                        let mut que = BinaryHeap::new();
                                        for (i, ls) in ls.iter().cloned().enumerate() {
                                            que.push((ls[0], Reverse(i), ls));
                                        }
                                        while used < v {
                                            let Some((_, Reverse(i), ls0)) = que.pop() else {
                                                break;
                                            };
                                            let len0 = ls0.len();
                                            let sm = ls0.into_iter().sum::<i32>();
                                            let len1 = len0 + 1;
                                            let unit = sm / len1 as i32;
                                            if unit == 0 {
                                                continue;
                                            }
                                            let mut ls1 = vec![unit; len1];
                                            let rem = sm - unit * len1 as i32;
                                            for j in 0..rem as usize {
                                                ls1[j] += 1;
                                            }
                                            debug_assert!(ls1.iter().all(|&l| l > 0));
                                            debug_assert_eq!(sm, ls1.iter().sum::<i32>());
                                            ls[i] = ls1.clone();
                                            que.push((ls1[0], Reverse(i), ls1));
                                            used += 1;
                                        }
                                    }
                                    let mut g = vec![vec![]; v];
                                    let mut nxt = 0;
                                    for ls in ls {
                                        for (i, l) in ls.into_iter().enumerate() {
                                            let pre = if i == 0 { 0 } else { nxt };
                                            nxt += 1;
                                            g[pre].push((nxt, l));
                                        }
                                    }
                                    best[n - NMIN][v - VMIN][pi - PMIN] = Some(
                                        evaluate(
                                            n,
                                            (pi as f64 + 0.5) / PRESOL as f64,
                                            &g,
                                            &mut to,
                                            &mut to_cnt,
                                            &mut to1,
                                            &mut to1_cnt,
                                        )
                                        .unwrap(),
                                    );
                                    g
                                })
                                .collect_vec()
                        })
                        .collect_vec()
                })
                .collect_vec();
            for li in 1.. {
                let mut upd = false;
                for (ni, (best, best_g)) in best.iter_mut().zip(best_g.iter_mut()).enumerate() {
                    let n = NMIN + ni;
                    for (vi, (best, best_g)) in best.iter_mut().zip(best_g.iter_mut()).enumerate() {
                        let v = VMIN + vi;
                        for (pi, (best, best_g)) in
                            best.iter_mut().zip(best_g.iter_mut()).enumerate()
                        {
                            let mut g = vec![vec![]; v];
                            let mut uf = UnionFind::new(v);
                            for i in 1..v {
                                let mut pi = rand.next_usize() % i;
                                while uf.group_size(pi) > 3 {
                                    pi = rand.next_usize() % i;
                                }
                                let d = 1 + (rand.next_usize() % (n - 1)) as i32;
                                g[pi].push((i, d));
                                if pi != 0 {
                                    uf.unite(pi, i);
                                }
                            }
                            let p = ((PMIN + pi) as f64 + 0.5) / PRESOL as f64;
                            let Some(eval) =
                                evaluate(n, p, &g, &mut to, &mut to_cnt, &mut to1, &mut to1_cnt)
                            else {
                                continue;
                            };
                            if best.chmax(eval) {
                                *best_g = g.clone();
                                upd = true;
                            }
                        }
                    }
                }
                if upd {
                    eprintln!("{li}");
                }
                if li % 10000 == 0 {
                    let path = std::path::PathBuf::from(format!(r"tbl_g\tbl{}.txt", li));
                    let mut f = std::fs::File::create(&path).unwrap();
                    let mut el = false;
                    for (ni, best_g) in best_g.iter().enumerate() {
                        let n = NMIN + ni;
                        for (vi, best_g) in best_g.iter().enumerate() {
                            let v = VMIN + vi;
                            for (pi, best_g) in best_g.iter().enumerate() {
                                assert!(!best_g.is_empty());
                                let p = PMIN + pi;
                                use std::io::Write;
                                if el {
                                    write!(&mut f, "else ").unwrap();
                                } else {
                                    el = true;
                                }
                                write!(&mut f, "if n=={n}&&v=={v}&&pi=={p}").unwrap();
                                write!(&mut f, "{{").unwrap();
                                {
                                    write!(&mut f, "g=vec![").unwrap();
                                    for g in best_g.iter() {
                                        write!(&mut f, "vec![").unwrap();
                                        for &(i, d) in g.iter() {
                                            write!(&mut f, "({i},{d}),").unwrap();
                                        }
                                        write!(&mut f, "],").unwrap();
                                    }
                                    write!(&mut f, "];").unwrap();
                                }
                                writeln!(&mut f, "}}").unwrap();
                            }
                        }
                    }
                }
            }
        }
        fn gen_tree(&self) -> Vec<Vec<(usize, i32)>> {
            let mut g = vec![];
            let n = self.n;
            let m = self.m;
            let v = self.v;
            let pi = ((PRESOL * m) / (n * n)).clamp(PMIN, PMAX);
            assert!(g.len() == self.v);
            return g;
        }
        fn gen_arm_shapes(&self) -> (Vec<ArmShape>, usize) {
            let g = self.gen_tree();
            let arms = g[0]
                .iter()
                .map(|&(nv0, _)| ArmShape::new(self.v, nv0, &g))
                .collect_vec();
            println!("{}", self.v);
            let mut shape = vec![(0, 0); self.v];
            for arm in arms.iter() {
                arm.set_shape(&mut shape);
            }
            for (p, d) in shape.into_iter().skip(1) {
                println!("{p} {d}");
            }
            (arms, self.v)
        }
        fn add_cmd(
            &self,
            arm_shapes: &[ArmShape],
            used: usize,
            state: &State,
            dir_upd: &[Vec<(usize, u16)>],
            dyx: (i32, i32),
        ) -> Vec<String> {
            let mut cmd = vec![];
            let mut add = |cy: usize, cx: usize, c: char| {
                while cmd.len() <= cy {
                    cmd.push(vec!['.'; 2 * used]);
                }
                cmd[cy][cx] = c;
            };
            add(
                0,
                0,
                match dyx {
                    (0, 1) => 'R',
                    (0, -1) => 'L',
                    (1, 0) => 'D',
                    (-1, 0) => 'U',
                    (0, 0) => '.',
                    _ => unreachable!(),
                },
            );
            for (arm_shape, (&dir0, dir_upd)) in
                arm_shapes.iter().zip(state.dir.iter().zip(dir_upd.iter()))
            {
                // one arm
                let mut dir = dir0;
                // repeao
                let mut cmd_y = 0;
                for &(dir1, flip) in dir_upd.iter() {
                    let (abs_vs, cs) = arm_shape.rot_cmd(dir, dir1);
                    let mut cmd_delta = 0;
                    for (&abs_v, cs) in abs_vs.iter().zip(cs.iter()).skip(1) {
                        let mut cmd_y_of_v = cmd_y;
                        let cmd_x = abs_v;
                        for &c in cs.iter() {
                            add(cmd_y_of_v, cmd_x, c);
                            cmd_y_of_v += 1;
                        }
                        cmd_delta.chmax(cs.len());
                    }
                    for (rel_v, abs_v) in abs_vs.into_iter().enumerate().skip(1) {
                        if ((flip >> rel_v) & 1) != 0 {
                            add(cmd_y + cmd_delta.saturating_sub(1), used + abs_v, 'P');
                        }
                    }

                    //cmd_y_of_v += 1;
                    //
                    dir = dir1;
                    cmd_y += max(1, cmd_delta);
                }
            }
            if cmd.is_empty() {
                cmd.push(vec!['.'; 2 * used]);
            }
            cmd.into_iter()
                .map(|vc| vc.into_iter().collect::<String>())
                .collect_vec()
        }
        pub fn solve(&self) {
            let (arm_shapes, used) = self.gen_arm_shapes();
            let (mut y_now, mut x_now) = self.gen_ini();
            println!("{y_now} {x_now}");

            let mut ans = vec![];
            let mut cum_cost = 0;
            let state0 = State {
                rem: self.s.clone(),
                tgt: self.t.clone(),
                dir: vec![0; arm_shapes.len()],
                cap: vec![0; arm_shapes.len()],
            };
            let mut state = state0.clone();
            let (_dgain, dcost, dir_upd) = state.move_and_update(self.n, &arm_shapes, y_now, x_now);
            cum_cost += dcost;
            for cmd in self.add_cmd(&arm_shapes, used, &state0, &dir_upd, (0, 0)) {
                ans.push(cmd);
            }

            let mut dp = vec![vec![State::empty(self.n, arm_shapes.len()); self.n]; self.n];
            dp[y_now][x_now] = state.clone();
            let mut pre = vec![vec![(0, 0, vec![]); self.n]; self.n];
            for _li in 0.. {
                let mut eval = vec![vec![None; self.n]; self.n];
                eval[y_now][x_now] = Some(0.0);
                let mut dist = vec![vec![self.n * self.n; self.n]; self.n];
                dist[y_now][x_now] = 0;
                let mut cost = vec![vec![0; self.n]; self.n];
                let mut gain = vec![vec![0; self.n]; self.n];
                let mut best = None;
                let mut best_pt = (0, 0);
                let mut que = VecDeque::new();
                que.push_back((y_now, x_now));
                while let Some((y0, x0)) = que.pop_front() {
                    let d0 = dist[y0][x0];
                    let d1 = d0 + 1;
                    for (dy, dx) in [(1, 0), (0, 1), (-1, 0), (0, -1)] {
                        if y0 as i32 + dy < 0
                            || y0 as i32 + dy >= self.n as i32
                            || x0 as i32 + dx < 0
                            || x0 as i32 + dx >= self.n as i32
                        {
                            continue;
                        }
                        let y1 = (y0 as i32 + dy) as usize;
                        let x1 = (x0 as i32 + dx) as usize;
                        let mut nstate = dp[y0][x0].clone();
                        let (dgain, dcost, dir_upd) =
                            nstate.move_and_update(self.n, &arm_shapes, y1, x1);
                        let gain1 = gain[y0][x0] + dgain;
                        let cost1 = cost[y0][x0] + max(1, dcost);
                        let eval1 = gain1 as f64 / cost1 as f64;
                        if dist[y1][x1].chmin(d1) {
                            que.push_back((y1, x1));
                            eval[y1][x1] = Some(eval1);
                            cost[y1][x1] = cost1;
                            gain[y1][x1] = gain1;
                            dp[y1][x1] = nstate;
                            pre[y1][x1] = (y0, x0, dir_upd);
                            if best.chmax(eval1) {
                                best_pt = (y1, x1);
                            }
                        } else if dist[y1][x1] == d1 && eval[y1][x1].chmax(eval1) {
                            cost[y1][x1] = cost1;
                            gain[y1][x1] = gain1;
                            dp[y1][x1] = nstate;
                            pre[y1][x1] = (y0, x0, dir_upd);
                            if best.chmax(eval1) {
                                best_pt = (y1, x1);
                            }
                        }
                    }
                }
                debug_assert!(best.is_some());
                // record
                {
                    let mut path = vec![];
                    let (mut y, mut x) = best_pt;
                    while (y, x) != (y_now, x_now) {
                        let (y_pre, x_pre, dir_upd) = &pre[y][x];
                        path.push(((*y_pre, *x_pre), (y, x), dir_upd));
                        (y, x) = (*y_pre, *x_pre);
                    }
                    for ((y0, x0), (y1, x1), dir_upd) in path.into_iter().rev() {
                        let dy = y1 as i32 - y0 as i32;
                        let dx = x1 as i32 - x0 as i32;
                        for cmd in self.add_cmd(&arm_shapes, used, &dp[y0][x0], dir_upd, (dy, dx)) {
                            ans.push(cmd);
                        }
                    }
                }
                (y_now, x_now) = best_pt;
                state = dp[y_now][x_now].clone();
                cum_cost += cost[y_now][x_now];
                if state.fin() {
                    break;
                }
            }
            for ans in ans {
                println!("{ans}");
            }
            eprintln!("{cum_cost}");
        }
    }
}
