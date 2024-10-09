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

mod gcd {
    use num::{One, Zero};
    use std::cmp::{PartialEq, PartialOrd};
    use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign};
    pub fn gcd<T: Copy + Rem<Output = T> + PartialEq + Zero>(a: T, b: T) -> T {
        if b == T::zero() {
            a
        } else {
            gcd(b, a % b)
        }
    }
    // returns (p, q) s. t. ap + bq = gcd(a, b)
    #[inline(always)]
    pub fn ext_gcd<
        T: Eq
            + Copy
            + Sub<Output = T>
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + Zero
            + One,
    >(
        a: T,
        b: T,
    ) -> (T, T) {
        if a == T::zero() {
            return (T::zero(), T::one());
        }
        // (b % a) * x + a * y = gcd(a, b)
        // b % a = b - (b / a) * a
        // ->
        // (b - (b / a) * a) * x + a * y = gcd(a, b)
        // a * (y - (b / a) * x) + b * x = gcd(a, b)
        let (x, y) = ext_gcd(b % a, a);
        (y - b / a * x, x)
    }
    // Chinese Remainder Theorem
    // when exists, returns (lcm(m1, m2), x) s.t. x = r1 (mod  m1) and x = r2 (mod m2)
    fn chinese_rem_elem2<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign
            + Zero
            + One,
    >(
        m1: T,
        r1: T,
        m2: T,
        r2: T,
    ) -> Option<(T, T)> {
        let (p, _q) = ext_gcd(m1, m2);
        let g = gcd(m1, m2);
        if (r2 - r1) % g != T::zero() {
            None
        } else {
            let lcm = m1 * (m2 / g);
            let mut r = r1 + m1 * ((r2 - r1) / g) * p;
            if r < T::zero() {
                let dv = (-r + lcm - T::one()) / lcm;
                r += dv * lcm;
            }
            r %= lcm;
            Some((lcm, r))
        }
    }
    // Chinese Remainder Theorem
    // when exists, returns (lcm(mods), x) s.t. x = r_i (mod  m_i) for all i.
    pub fn chinese_rem<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign
            + One
            + Zero,
    >(
        mods: &[T],
        rems: &[T],
    ) -> Option<(T, T)> {
        debug_assert!(mods.len() == rems.len());
        let mut lcm = T::one();
        let mut rem = T::zero();
        for (m, r) in mods.iter().copied().zip(rems.iter().copied()) {
            if let Some((nlcm, nrem)) = chinese_rem_elem2(lcm, rem, m, r) {
                lcm = nlcm;
                rem = nrem;
            } else {
                return None;
            }
        }
        Some((lcm, rem))
    }
}
use gcd::*;

fn factorial_impl<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T>,
>(
    p: usize,
    memo: *mut Vec<usize>,
    update_op: fn(T, T) -> T,
) -> T {
    unsafe {
        while (*memo).len() < 2_usize {
            (*memo).push(1_usize);
        }
        while (*memo).len() <= p + 1 {
            let last_val: T = T::from(*(*memo).last().unwrap());
            (*memo).push(update_op(last_val, T::from((*memo).len())).into());
        }
        T::from((*memo)[p])
    }
}

fn factorial<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    factorial_impl(p, unsafe { std::ptr::addr_of_mut!(MEMO) }, |x: T, y: T| {
        x * y
    })
}

fn factorial_inv<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    factorial_impl(p, unsafe { std::ptr::addr_of_mut!(MEMO) }, |x: T, y: T| {
        x / y
    })
}

fn combination<
    T: Clone
        + Copy
        + From<usize>
        + Into<usize>
        + Mul<Output = T>
        + Div<Output = T>
        + One
        + Zero
        + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if n < k {
        return T::zero();
    }
    if k == 0 {
        return T::one();
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return (T::from(n) * T::from(n - 1)) / T::from(2);
    }

    factorial::<T>(n) * factorial_inv::<T>(k) * factorial_inv::<T>(n - k)
}

fn permutation<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + One + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::one();
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return T::from(n) * T::from(n - 1);
    }

    factorial::<T>(n) * factorial_inv::<T>(n - k)
}

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

mod segment_tree {
    use std::ops::{Add, Sub};
    #[derive(Debug, Clone)]
    pub struct SegmentTree<T> {
        n: usize,
        n2: usize,
        height: usize,
        width: Vec<usize>,
        dat: Vec<T>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Clone> SegmentTree<T> {
        pub fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            Self::from_vec(pair_op, vec![ini_val; n])
        }
        pub fn from_vec(pair_op: fn(T, T) -> T, ini_values: Vec<T>) -> Self {
            let n = ini_values.len();
            let mut n2 = 1;
            let mut height = 1;
            while n2 < n {
                n2 *= 2;
                height += 1;
            }
            let width = (0..height)
                .scan(2 * n, |cum, _| {
                    *cum = (*cum + 1) / 2;
                    Some(*cum)
                })
                .collect::<Vec<_>>();
            let mut dat = vec![ini_values[0].clone(); n2 + n];
            dat.iter_mut()
                .skip(n2)
                .zip(ini_values)
                .for_each(|(dat, ini)| {
                    *dat = ini;
                });
            for hi in 1..height {
                let beg = n2 >> hi;
                let cend = (n2 >> (hi - 1)) + width[hi - 1];
                for p in (beg..).take(width[hi]) {
                    let l = p * 2;
                    let r = l + 1;
                    dat[p] = if r < cend {
                        pair_op(dat[l].clone(), dat[r].clone())
                    } else {
                        dat[l].clone()
                    };
                }
            }
            Self {
                n,
                n2,
                height,
                width,
                pair_op,
                dat,
            }
        }
        pub fn set(&mut self, mut i: usize, val: T) {
            i += self.n2;
            self.dat[i] = val;
            for hi in 1..self.height {
                let p = i >> hi;
                let l = p * 2;
                let r = l + 1;
                let cend = (self.n2 >> (hi - 1)) + self.width[hi - 1];
                self.dat[p] = if r < cend {
                    (self.pair_op)(self.dat[l].clone(), self.dat[r].clone())
                } else {
                    self.dat[l].clone()
                };
            }
        }
        pub fn get(&self, pos: usize) -> T {
            self.dat[pos + self.n2].clone()
        }
        pub fn query_all(&mut self) -> T {
            self.query(0, self.n - 1)
        }
        pub fn query_left(&self, r: usize) -> T {
            self.query(0, r)
        }
        pub fn query_right(&self, l: usize) -> T {
            self.query(l, self.n - 1)
        }
        // get query value of [a, b]
        pub fn query(&self, mut l: usize, mut r: usize) -> T {
            l += self.n2;
            r += self.n2 + 1;
            let mut lcum = None;
            let mut rcum = None;
            for hi in 0..self.height {
                let end = (self.n2 >> hi) + self.width[hi];
                if l % 2 == 1 {
                    debug_assert!(l < end);
                    lcum = if let Some(lv) = lcum {
                        Some((self.pair_op)(lv, self.dat[l].clone()))
                    } else {
                        Some(self.dat[l].clone())
                    };
                    l += 1;
                }
                if r % 2 == 1 {
                    r -= 1;
                    debug_assert!(r < end);
                    rcum = if let Some(rv) = rcum {
                        Some((self.pair_op)(self.dat[r].clone(), rv))
                    } else {
                        Some(self.dat[r].clone())
                    };
                }
                l /= 2;
                r /= 2;
                if l >= r {
                    break;
                }
            }
            if let Some(lcum) = lcum {
                if let Some(rcum) = rcum {
                    (self.pair_op)(lcum, rcum)
                } else {
                    lcum
                }
            } else {
                rcum.unwrap()
            }
        }
        pub fn right_rise(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            self.right_fall(l, |x| !jdg(x))
        }
        pub fn right_fall(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            let mut v = l + self.n2;
            if !jdg(self.dat[v].clone()) {
                return Some(l);
            }
            if jdg(self.query(l, self.n - 1)) {
                return None;
            }
            let mut true_fix = None;
            loop {
                let ev = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(true_fix, self.dat[v].clone())
                } else {
                    self.dat[v].clone()
                };
                if jdg(ev.clone()) {
                    if v & 1 != 0 {
                        v += 1;
                        true_fix = Some(ev);
                    }
                    v /= 2;
                } else {
                    break;
                }
            }
            while v < self.n2 {
                let lc = v * 2;
                let rc = lc + 1;
                let ev_lc = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(true_fix, self.dat[lc].clone())
                } else {
                    self.dat[lc].clone()
                };
                if !jdg(ev_lc.clone()) {
                    v = lc;
                } else {
                    v = rc;
                    true_fix = Some(ev_lc);
                }
            }
            Some(v - self.n2)
        }
        pub fn left_rise(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            self.left_fall(r, |x| !jdg(x))
        }
        pub fn left_fall(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            let mut v = r + self.n2 + 1;
            if !jdg(self.dat[v - 1].clone()) {
                return Some(r);
            }
            if jdg(self.query(0, r)) {
                return None;
            }
            let mut true_fix = None;
            loop {
                let ev = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(self.dat[v - 1].clone(), true_fix)
                } else {
                    self.dat[v - 1].clone()
                };
                if jdg(ev.clone()) {
                    if v & 1 != 0 {
                        v -= 1;
                        true_fix = Some(ev);
                    }
                    v /= 2;
                } else {
                    break;
                }
            }
            v -= 1;
            while v < self.n2 {
                let lc = v * 2;
                let rc = lc + 1;
                let ev_rc = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(self.dat[rc].clone(), true_fix)
                } else {
                    self.dat[rc].clone()
                };
                if !jdg(ev_rc.clone()) {
                    v = rc;
                } else {
                    v = lc;
                    true_fix = Some(ev_rc);
                }
            }
            Some(v - self.n2)
        }
        pub fn right_true_max(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            if let Some(r) = self.right_fall(l, jdg) {
                if l == r {
                    None
                } else {
                    Some(r - 1)
                }
            } else {
                Some(self.n - 1)
            }
        }
        pub fn right_false_max(&self, l: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            if let Some(r) = self.right_rise(l, jdg) {
                if l == r {
                    None
                } else {
                    Some(r - 1)
                }
            } else {
                Some(self.n - 1)
            }
        }
        pub fn left_true_max(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            if let Some(l) = self.left_fall(r, jdg) {
                if l == r {
                    None
                } else {
                    Some(l + 1)
                }
            } else {
                Some(0)
            }
        }
        pub fn left_false_max(&self, r: usize, jdg: impl Fn(T) -> bool) -> Option<usize> {
            if let Some(l) = self.left_rise(r, jdg) {
                if l == r {
                    None
                } else {
                    Some(l + 1)
                }
            } else {
                Some(0)
            }
        }
    }
    impl<T: Copy + Add<Output = T> + Sub<Output = T>> SegmentTree<T> {
        pub fn add(&mut self, pos: usize, add_val: T) {
            self.set(pos, self.get(pos) + add_val);
        }
        pub fn sub(&mut self, pos: usize, sub_val: T) {
            self.set(pos, self.get(pos) - sub_val);
        }
    }
    pub mod test {
        use super::super::XorShift64;
        use super::SegmentTree;
        const T: usize = 100;
        const N: usize = 100;
        #[test]
        pub fn query() {
            let mut rand = XorShift64::new();
            for n in 1..=N {
                let mut a = vec![0; n];
                let mut seg = SegmentTree::<usize>::from_vec(std::cmp::max, a.clone());
                for _ in 0..T {
                    a.iter_mut().enumerate().for_each(|(i, a)| {
                        *a = rand.next_usize() % N;
                        seg.set(i, *a);
                    });
                    for l in 0..n {
                        for r in l..n {
                            let &expected = a[l..=r].iter().max().unwrap();
                            let actual = seg.query(l, r);
                            assert_eq!(expected, actual);
                        }
                    }
                }
            }
        }
        #[test]
        fn binary_search() {
            let mut rand = XorShift64::new();
            for n in 1..=N {
                let mut a = vec![0; n];
                let mut seg = SegmentTree::<usize>::from_vec(std::cmp::max, a.clone());
                for _ in 0..T {
                    a.iter_mut().enumerate().for_each(|(i, a)| {
                        *a = rand.next_usize() % N;
                        seg.set(i, *a);
                    });
                    for v in 0..=N {
                        let lower = |x| x < v;
                        let upper = |x| x >= v;
                        for l in 0..n {
                            let actural = seg.right_fall(l, lower);
                            assert_eq!(actural, seg.right_rise(l, upper));
                            let mut expected = None;
                            for r in l..n {
                                if upper(seg.query(l, r)) {
                                    expected = Some(r);
                                    break;
                                }
                            }
                            assert_eq!(expected, actural);
                        }
                        for r in 0..n {
                            let actural = seg.left_fall(r, lower);
                            assert_eq!(actural, seg.left_rise(r, upper));
                            let mut expected = None;
                            for l in (0..=r).rev() {
                                if upper(seg.query(l, r)) {
                                    expected = Some(l);
                                    break;
                                }
                            }
                            assert_eq!(expected, actural);
                        }
                    }
                }
            }
        }
    }
}
use segment_tree::SegmentTree;
mod segment_tree_2d {
    use std::ops::{Add, Sub};

    use crate::segment_tree::SegmentTree;
    #[derive(Debug, Clone)]
    pub struct SegmentTree2D<T> {
        h: usize,
        w: usize,
        segs: Vec<SegmentTree<T>>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Clone> SegmentTree2D<T> {
        pub fn new(h: usize, w: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            Self {
                h,
                w,
                pair_op,
                segs: vec![SegmentTree::new(w, pair_op, ini_val); 2 * h],
            }
        }
        pub fn set(&mut self, mut y: usize, x: usize, val: T) {
            y += self.h;
            self.segs[y].set(x, val);
            let mut par = y / 2;
            while par >= 1 {
                let l = par * 2;
                let r = l + 1;
                let lv = self.segs[l].get(x);
                let rv = self.segs[r].get(x);
                let v = (self.pair_op)(lv, rv);
                self.segs[par].set(x, v);
                par /= 2;
            }
        }
        pub fn get(&self, y: usize, x: usize) -> T {
            self.segs[y + self.h].get(x)
        }
        // get query value of [a, b]
        pub fn query(&self, mut y0: usize, mut y1: usize, x0: usize, x1: usize) -> T {
            y0 += self.h;
            y1 += self.h + 1;
            let mut y0val = None;
            let mut bval = None;
            while y0 < y1 {
                if y0 % 2 == 1 {
                    y0val = if let Some(aval0) = y0val {
                        Some((self.pair_op)(aval0, self.segs[y0].query(x0, x1)))
                    } else {
                        Some(self.segs[y0].query(x0, x1))
                    };
                    y0 += 1;
                }
                if y1 % 2 == 1 {
                    y1 -= 1;
                    bval = if let Some(bval0) = bval {
                        Some((self.pair_op)(self.segs[y1].query(x0, x1), bval0))
                    } else {
                        Some(self.segs[y1].query(x0, x1))
                    };
                }
                y0 /= 2;
                y1 /= 2;
            }
            if let Some(y0val) = y0val {
                if let Some(bval) = bval {
                    (self.pair_op)(y0val, bval)
                } else {
                    y0val
                }
            } else {
                bval.unwrap()
            }
        }
    }
    impl<T: Copy + Add<Output = T> + Sub<Output = T>> SegmentTree2D<T> {
        pub fn add(&mut self, y: usize, x: usize, add_val: T) {
            self.set(y, x, self.get(y, x) + add_val);
        }
        pub fn sub(&mut self, y: usize, x: usize, sub_val: T) {
            self.set(y, x, self.get(y, x) - sub_val);
        }
    }
    mod tests {
        #[test]
        fn random_test() {
            use super::super::XorShift64;
            use super::SegmentTree2D;
            use std::cmp::{max, min};
            const N: usize = 10;
            let mut rand = XorShift64::new();
            for &f in [min, max, |x, y| x + y].iter() {
                let mut raw = vec![vec![0; N]; N];
                let mut seg = SegmentTree2D::<i64>::new(N, N, f, 0);
                for y in 0..N {
                    for x in 0..N {
                        let v = rand.next_u64() as i64 % 100;
                        seg.set(y, x, v);
                        raw[y][x] = v;
                    }
                }
                for y0 in 0..N {
                    for y1 in y0..N {
                        for x0 in 0..N {
                            for x1 in x0..N {
                                let seg_v = seg.query(y0, y1, x0, x1);
                                let mut raw_v = raw[y0][x0];
                                for y in y0..=y1 {
                                    for x in x0..=x1 {
                                        if (y, x) == (y0, x0) {
                                            continue;
                                        }
                                        raw_v = f(raw_v, raw[y][x]);
                                    }
                                }
                                assert_eq!(seg_v, raw_v);
                            }
                        }
                    }
                }
            }
        }
    }
}
use segment_tree_2d::SegmentTree2D;

mod lazy_segment_tree {
    #[derive(Clone, Debug)]
    pub struct LazySegmentTree<X, M> {
        n: usize,
        n2: usize,
        height: usize,
        width: Vec<usize>,
        pair_op: fn(X, X) -> X,
        update_op: fn(X, M) -> X,
        update_concat: fn(M, M) -> M,
        dat: Vec<X>,
        lazy_ops: Vec<Option<M>>,
    }
    impl<X: Clone, M: Clone> LazySegmentTree<X, M> {
        pub fn from_vec(
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            ini_vals: Vec<X>,
        ) -> Self {
            let n = ini_vals.len();
            let mut n2 = 1;
            let mut height = 1;
            while n2 < n {
                n2 *= 2;
                height += 1;
            }
            let width = (0..height)
                .scan(2 * n, |cum, _| {
                    *cum = (*cum + 1) / 2;
                    Some(*cum)
                })
                .collect::<Vec<_>>();
            let mut dat = vec![ini_vals[0].clone(); n2 + n];
            dat.iter_mut()
                .skip(n2)
                .zip(ini_vals)
                .for_each(|(dat, ini)| {
                    *dat = ini;
                });
            for hi in 1..height {
                let beg = n2 >> hi;
                let cend = (n2 >> (hi - 1)) + width[hi - 1];
                for p in (beg..).take(width[hi]) {
                    let l = p * 2;
                    let r = l + 1;
                    dat[p] = if r < cend {
                        pair_op(dat[l].clone(), dat[r].clone())
                    } else {
                        dat[l].clone()
                    };
                }
            }
            let lazy_ops = vec![None; n2];
            Self {
                n,
                n2,
                height,
                width,
                pair_op,
                update_op,
                update_concat,
                dat,
                lazy_ops,
            }
        }
        #[inline(always)]
        fn eval_down(&mut self, hi: usize, v: usize) {
            if hi == 0 {
                // bottom
                return;
            }
            // not bottom, has childs.
            let Some(lazy) = self.lazy_ops[v].clone() else {
                return;
            };
            self.lazy_ops[v] = None;
            let x0 = self.dat[v].clone();
            self.dat[v] = (self.update_op)(x0, lazy.clone());
            let l = v * 2;
            let r = l + 1;
            let cend = (self.n2 >> (hi - 1)) + self.width[hi - 1];
            if l < self.n2 {
                self.lazy_ops[l] = if let Some(m0) = self.lazy_ops[l].clone() {
                    Some((self.update_concat)(m0, lazy.clone()))
                } else if l < cend {
                    Some(lazy.clone())
                } else {
                    None
                };
                self.lazy_ops[r] = if let Some(m0) = self.lazy_ops[r].clone() {
                    Some((self.update_concat)(m0, lazy))
                } else if r < cend {
                    Some(lazy)
                } else {
                    None
                };
            } else {
                // bottom, no childs.
                if l < self.n2 + self.n {
                    self.dat[l] = (self.update_op)(self.dat[l].clone(), lazy.clone());
                    if r < self.n2 + self.n {
                        self.dat[r] = (self.update_op)(self.dat[r].clone(), lazy);
                    }
                }
            }
        }
        #[inline(always)]
        fn sum_up(&mut self, hi: usize, v: usize) {
            if hi == 0 {
                return;
            }
            self.eval_down(hi, v);
            let l = v * 2;
            let r = l + 1;
            if hi > 0 {
                self.eval_down(hi - 1, l);
                self.eval_down(hi - 1, r);
            }
            let cend = (self.n2 >> (hi - 1)) + self.width[hi - 1];
            self.dat[v] = if l < cend {
                if r < cend {
                    (self.pair_op)(self.dat[l].clone(), self.dat[r].clone())
                } else {
                    self.dat[l].clone()
                }
            } else {
                self.dat[r].clone()
            };
        }
        pub fn get(&mut self, mut i: usize) -> X {
            i += self.n2;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, i >> hi);
            }
            self.dat[i].clone()
        }
        pub fn set(&mut self, mut i: usize, x: X) {
            i += self.n2;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, i >> hi);
            }
            self.dat[i] = x;
            for hi in 0..self.height {
                self.sum_up(hi, i >> hi);
            }
        }
        pub fn query(&mut self, mut l: usize, mut r: usize) -> X {
            l += self.n2;
            r += self.n2 + 1;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, l >> hi);
                self.eval_down(hi, (r - 1) >> hi);
            }
            let mut lcum = None;
            let mut rcum = None;
            for hi in 0..self.height {
                let end = (self.n2 >> hi) + self.width[hi];
                if l % 2 == 1 {
                    debug_assert!(l < end);
                    self.eval_down(hi, l);
                    lcum = if let Some(lv) = lcum {
                        Some((self.pair_op)(lv, self.dat[l].clone()))
                    } else {
                        Some(self.dat[l].clone())
                    };
                    l += 1;
                }
                if r % 2 == 1 {
                    r -= 1;
                    debug_assert!(r < end);
                    self.eval_down(hi, r);
                    rcum = if let Some(rv) = rcum {
                        Some((self.pair_op)(self.dat[r].clone(), rv))
                    } else {
                        Some(self.dat[r].clone())
                    };
                }
                l /= 2;
                r /= 2;
                if l >= r {
                    break;
                }
            }
            if let Some(lcum) = lcum {
                if let Some(rcum) = rcum {
                    (self.pair_op)(lcum, rcum)
                } else {
                    lcum
                }
            } else {
                rcum.unwrap()
            }
        }
        pub fn reserve(&mut self, mut l: usize, mut r: usize, m: M) {
            l += self.n2;
            r += self.n2 + 1;
            for hi in (0..self.height).rev() {
                self.eval_down(hi, l >> hi);
                self.eval_down(hi, (r - 1) >> hi);
            }
            {
                let (mut l2, mut r2) = (l, r);
                for hi in 0..self.height {
                    if l2 % 2 == 1 {
                        debug_assert!(l2 < (self.n2 >> hi) + self.width[hi]);
                        if hi > 0 {
                            self.eval_down(hi, l2);
                            self.lazy_ops[l2] = Some(m.clone());
                        } else {
                            self.dat[l2] = (self.update_op)(self.dat[l2].clone(), m.clone());
                        }
                        l2 += 1;
                    }
                    if r2 % 2 == 1 {
                        r2 -= 1;
                        debug_assert!(r2 < (self.n2 >> hi) + self.width[hi]);
                        if hi > 0 {
                            self.eval_down(hi, r2);
                            self.lazy_ops[r2] = Some(m.clone());
                        } else {
                            self.dat[r2] = (self.update_op)(self.dat[r2].clone(), m.clone());
                        }
                    }
                    l2 /= 2;
                    r2 /= 2;
                    if l2 >= r2 {
                        break;
                    }
                }
            }
            for hi in 0..self.height {
                self.sum_up(hi, l >> hi);
                self.sum_up(hi, (r - 1) >> hi);
            }
        }
        pub fn right_rise(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            self.right_fall(l, |x| !jdg(x))
        }
        pub fn right_fall(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            let mut v = l + self.n2;
            for hi in (1..self.height).rev() {
                self.eval_down(hi, v >> hi);
            }
            if !jdg(self.dat[v].clone()) {
                return Some(l);
            }
            if jdg(self.query(l, self.n - 1)) {
                return None;
            }
            let mut true_fix = None;
            let mut hi = 0;
            while hi < self.height {
                self.eval_down(hi, v);
                let ev = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(true_fix, self.dat[v].clone())
                } else {
                    self.dat[v].clone()
                };
                if !jdg(ev.clone()) {
                    break;
                }
                if v & 1 != 0 {
                    v += 1;
                    true_fix = Some(ev);
                }
                while v & 1 == 0 {
                    v /= 2;
                    hi += 1;
                }
            }
            while hi > 0 {
                let lc = v * 2;
                let rc = lc + 1;
                self.eval_down(hi - 1, lc);
                let ev_lc = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(true_fix, self.dat[lc].clone())
                } else {
                    self.dat[lc].clone()
                };
                if !jdg(ev_lc.clone()) {
                    v = lc;
                } else {
                    self.eval_down(hi - 1, rc);
                    v = rc;
                    true_fix = Some(ev_lc);
                }
                hi -= 1;
            }
            Some(v - self.n2)
        }
        pub fn left_rise(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            self.left_fall(r, |x| !jdg(x))
        }
        pub fn left_fall(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            let mut v = r + self.n2 + 1;
            for hi in (1..self.height).rev() {
                self.eval_down(hi, (v - 1) >> hi);
            }
            if !jdg(self.dat[v - 1].clone()) {
                return Some(r);
            }
            if jdg(self.query(0, r)) {
                return None;
            }
            let mut true_fix = None;
            let mut hi = 0;
            while hi < self.height {
                self.eval_down(hi, v - 1);
                let ev = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(self.dat[v - 1].clone(), true_fix)
                } else {
                    self.dat[v - 1].clone()
                };
                if !jdg(ev.clone()) {
                    break;
                }
                if v & 1 != 0 {
                    v -= 1;
                    true_fix = Some(ev);
                }
                while v & 1 == 0 {
                    v /= 2;
                    hi += 1;
                }
            }
            while hi > 0 {
                let lc = (v - 1) * 2;
                let rc = lc + 1;
                self.eval_down(hi - 1, rc);
                let ev_rc = if let Some(true_fix) = true_fix.clone() {
                    (self.pair_op)(self.dat[rc].clone(), true_fix)
                } else {
                    self.dat[rc].clone()
                };
                if !jdg(ev_rc.clone()) {
                    v = rc + 1;
                } else {
                    self.eval_down(hi - 1, lc);
                    v = lc + 1;
                    true_fix = Some(ev_rc);
                }
                hi -= 1;
            }
            Some(v - self.n2 - 1)
        }
        pub fn right_true_max(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(r) = self.right_fall(l, jdg) {
                if l == r {
                    None
                } else {
                    Some(r - 1)
                }
            } else {
                Some(self.n - 1)
            }
        }
        pub fn right_false_max(&mut self, l: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(r) = self.right_rise(l, jdg) {
                if l == r {
                    None
                } else {
                    Some(r - 1)
                }
            } else {
                Some(self.n - 1)
            }
        }
        pub fn left_true_max(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(l) = self.left_fall(r, jdg) {
                if l == r {
                    None
                } else {
                    Some(l + 1)
                }
            } else {
                Some(0)
            }
        }
        pub fn left_false_max(&mut self, r: usize, jdg: impl Fn(X) -> bool) -> Option<usize> {
            if let Some(l) = self.left_rise(r, jdg) {
                if l == r {
                    None
                } else {
                    Some(l + 1)
                }
            } else {
                Some(0)
            }
        }
    }
    mod test {
        use super::super::XorShift64;
        use super::LazySegmentTree;
        #[test]
        fn random() {
            const N: usize = 100;
            const T: usize = 1000;
            let mut rand = XorShift64::new();
            for n in 1..=N {
                let mut a = (0..n).map(|_| rand.next_usize() % 2).collect::<Vec<_>>();
                #[derive(Clone, Debug)]
                struct Node {
                    n0: usize,
                    n1: usize,
                    inner_swap: usize,
                }
                let mut seg = LazySegmentTree::<Node, bool>::from_vec(
                    |x, y| {
                        let n0 = x.n0 + y.n0;
                        let n1 = x.n1 + y.n1;
                        let inner_swap = x.inner_swap + y.inner_swap + x.n1 * y.n0;
                        Node { n0, n1, inner_swap }
                    },
                    |x, b| {
                        if !b {
                            return x;
                        }
                        let tot = x.n0 + x.n1;
                        let n0 = x.n1;
                        let n1 = x.n0;
                        let mut inner_swap = (tot * (tot - 1)) / 2;
                        inner_swap -= if n0 == 0 { 0 } else { (n0 * (n0 - 1)) / 2 };
                        inner_swap -= if n1 == 0 { 0 } else { (n1 * (n1 - 1)) / 2 };
                        inner_swap -= x.inner_swap;
                        Node { n0, n1, inner_swap }
                    },
                    |b0, b1| (b0 != b1),
                    a.iter()
                        .map(|&a| {
                            if a == 0 {
                                Node {
                                    n0: 1,
                                    n1: 0,
                                    inner_swap: 0,
                                }
                            } else {
                                Node {
                                    n0: 0,
                                    n1: 1,
                                    inner_swap: 0,
                                }
                            }
                        })
                        .collect::<Vec<_>>(),
                );
                for _ in 0..T {
                    let mut l = rand.next_usize() % n;
                    let mut r = rand.next_usize() % n;
                    if l >= r {
                        std::mem::swap(&mut l, &mut r);
                    }
                    let op = rand.next_usize() % 2;
                    if op == 0 {
                        seg.reserve(l, r, true);
                        a.iter_mut().take(r + 1).skip(l).for_each(|a| {
                            *a = 1 - *a;
                        });
                    } else {
                        let actual = seg.query(l, r).inner_swap;
                        let mut cnt = vec![0; 2];
                        let mut expected = 0;
                        for i in l..=r {
                            if a[i] == 0 {
                                expected += cnt[1];
                            }
                            cnt[a[i]] += 1;
                        }
                        assert_eq!(expected, actual);
                    }
                }
            }
        }
        #[test]
        fn binary_search() {
            const NMAX: usize = 100;
            const T: usize = 100;
            const OP: usize = 1000;
            const V: usize = 10;
            let mut rand = XorShift64::new();
            for n in 1..=NMAX {
                for _ in 0..T {
                    let mut a = (0..n).map(|_| rand.next_usize() % V).collect::<Vec<_>>();
                    let mut seg = LazySegmentTree::<(usize, usize), usize>::from_vec(
                        |x, y| (x.0 + y.0, x.1 + y.1),
                        |x, m| (x.0 + x.1 * m, x.1),
                        |m0, m1| m0 + m1,
                        a.iter().map(|&a| (a, 1)).collect::<Vec<_>>(),
                    );
                    let mut ops = vec![];
                    for _ in 0..OP {
                        let mut l = rand.next_usize() % n;
                        let mut r = rand.next_usize() % n;
                        if l > r {
                            (l, r) = (r, l);
                        }
                        let op = rand.next_usize() % 3;
                        let v = rand.next_usize() % V;
                        ops.push((op, l, r, v));
                        match op {
                            0 => {
                                (l..=r).for_each(|i| {
                                    a[i] += v;
                                });
                                seg.reserve(l, r, v);
                            }
                            1 => {
                                let mut expected_fall = None;
                                let mut cum = 0;
                                for i in l..n {
                                    cum += a[i];
                                    if cum >= v {
                                        expected_fall = Some(i);
                                        break;
                                    }
                                }
                                assert_eq!(expected_fall, seg.right_fall(l, |(x, _)| x < v));
                                assert_eq!(expected_fall, seg.right_rise(l, |(x, _)| x >= v));
                            }
                            2 => {
                                let mut expected_fall = None;
                                let mut cum = 0;
                                for i in (0..=r).rev() {
                                    cum += a[i];
                                    if cum >= v {
                                        expected_fall = Some(i);
                                        break;
                                    }
                                }
                                assert_eq!(expected_fall, seg.left_fall(r, |(x, _)| x < v));
                                assert_eq!(expected_fall, seg.left_rise(r, |(x, _)| x >= v));
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }
}
use lazy_segment_tree::LazySegmentTree;

mod modint {
    #[inline(always)]
    pub fn powmod(x: i64, mut p: usize, m: i64) -> i64 {
        let mut ret = 1;
        let mut mul = x;
        while p > 0 {
            if p & 1 != 0 {
                ret = (ret * mul) % m;
            }
            p >>= 1;
            mul = (mul * mul) % m;
        }
        ret
    }

    pub mod static_mod_int {
        use super::powmod;
        use crate::gcd::ext_gcd;
        use num::{One, Zero};
        use std::fmt;
        use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};

        #[derive(Clone, Copy, Eq, Hash, PartialEq)]
        pub struct StaticModInt<const MOD: i64> {
            x: i64,
        }
        impl<const MOD: i64> StaticModInt<MOD> {
            #[inline(always)]
            pub fn val(&self) -> i64 {
                self.x
            }
            #[inline(always)]
            pub fn new(mut sig: i64) -> Self {
                if sig < 0 {
                    let ab = (-sig + MOD - 1) / MOD;
                    sig += ab * MOD;
                    debug_assert!(sig >= 0);
                }
                Self { x: sig % MOD }
            }
            #[inline(always)]
            fn inverse(&self) -> Self {
                // x * inv_x + M * _ = gcd(x, M) = 1
                // x * inv_x = 1 (mod M)
                Self::new(ext_gcd(self.x, MOD).0)

                // [Fermat's little theorem]
                // if p is prime, for any integer a, a^p = a (mod p)
                // especially when a and b is coprime, a^(p-1) = 1 (mod p).
                // -> inverse of a is a^(p-2).

                //let mut ret = Self { x: 1 };
                //let mut mul: Self = *self;
                //let mut p = MOD() - 2;
                //while p > 0 {
                //    if p & 1 != 0 {
                //        ret *= mul;
                //    }
                //    p >>= 1;
                //    mul *= mul;
                //}
                //ret
            }
            #[inline(always)]
            pub fn pow(self, p: usize) -> Self {
                Self {
                    x: powmod(self.x, p, MOD),
                }
            }
        }
        impl<const MOD: i64> One for StaticModInt<MOD> {
            #[inline(always)]
            fn one() -> Self {
                Self { x: 1 }
            }
        }
        impl<const MOD: i64> Zero for StaticModInt<MOD> {
            #[inline(always)]
            fn zero() -> Self {
                Self { x: 0 }
            }
            #[inline(always)]
            fn is_zero(&self) -> bool {
                self.x == 0
            }
            #[inline(always)]
            fn set_zero(&mut self) {
                self.x = 0;
            }
        }
        impl<const MOD: i64> Add<Self> for StaticModInt<MOD> {
            type Output = Self;
            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                StaticModInt::new(self.x + rhs.x)
            }
        }
        impl<const MOD: i64> Sub<Self> for StaticModInt<MOD> {
            type Output = Self;
            #[inline(always)]
            fn sub(self, rhs: Self) -> Self::Output {
                StaticModInt::new(self.x - rhs.x)
            }
        }
        impl<const MOD: i64> Mul<Self> for StaticModInt<MOD> {
            type Output = Self;
            #[inline(always)]
            fn mul(self, rhs: Self) -> Self::Output {
                StaticModInt::new(self.x * rhs.x)
            }
        }
        impl<const MOD: i64> Div<Self> for StaticModInt<MOD> {
            type Output = Self;
            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn div(self, rhs: Self) -> Self::Output {
                StaticModInt::new(self.x * rhs.inverse().x)
            }
        }
        impl<const MOD: i64> AddAssign<Self> for StaticModInt<MOD> {
            #[inline(always)]
            fn add_assign(&mut self, rhs: Self) {
                *self = StaticModInt::new(self.x + rhs.x);
            }
        }
        impl<const MOD: i64> SubAssign<Self> for StaticModInt<MOD> {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: Self) {
                *self = StaticModInt::new(self.x - rhs.x);
            }
        }
        impl<const MOD: i64> MulAssign<Self> for StaticModInt<MOD> {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: Self) {
                *self = StaticModInt::new(self.x * rhs.x);
            }
        }
        impl<const MOD: i64> DivAssign<Self> for StaticModInt<MOD> {
            #[inline(always)]
            #[allow(clippy::suspicious_op_assign_impl)]
            fn div_assign(&mut self, rhs: Self) {
                *self = StaticModInt::new(self.x * rhs.inverse().x);
            }
        }
        impl<const MOD: i64> From<usize> for StaticModInt<MOD> {
            #[inline(always)]
            fn from(x: usize) -> Self {
                StaticModInt::new(x as i64)
            }
        }
        impl<const MOD: i64> From<i64> for StaticModInt<MOD> {
            #[inline(always)]
            fn from(x: i64) -> Self {
                StaticModInt::new(x)
            }
        }
        impl<const MOD: i64> std::str::FromStr for StaticModInt<MOD> {
            type Err = std::num::ParseIntError;
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s.parse::<i64>() {
                    Ok(x) => Ok(StaticModInt::from(x)),
                    Err(e) => Err(e),
                }
            }
        }
        impl<const MOD: i64> std::iter::Sum for StaticModInt<MOD> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), |cum, v| cum + v)
            }
        }
        impl<const MOD: i64> fmt::Display for StaticModInt<MOD> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.x)
            }
        }
        impl<const MOD: i64> fmt::Debug for StaticModInt<MOD> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.x)
            }
        }
    }

    pub mod dynamic_mod_int {
        use super::powmod;
        use crate::gcd::ext_gcd;
        use num::{One, Zero};
        use std::fmt;
        use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};
        static mut MOD: i64 = 2;
        #[derive(Clone, Copy, Eq, Hash, PartialEq)]
        pub struct DynModInt {
            x: i64,
        }
        impl DynModInt {
            pub fn set_mod(val: i64) {
                unsafe {
                    MOD = val;
                }
            }
            #[inline(always)]
            pub fn get_mod() -> i64 {
                unsafe { MOD }
            }
            #[inline(always)]
            pub fn val(&self) -> i64 {
                self.x
            }
            #[inline(always)]
            pub fn new(mut sig: i64) -> Self {
                if sig < 0 {
                    let m = Self::get_mod();
                    let ab = (-sig + m - 1) / m;
                    sig += ab * m;
                    debug_assert!(sig >= 0);
                }
                Self {
                    x: sig % Self::get_mod(),
                }
            }
            #[inline(always)]
            fn inverse(&self) -> Self {
                // x * inv_x + M * _ = gcd(x, M) = 1
                // x * inv_x = 1 (mod M)
                Self::new(ext_gcd(self.x, Self::get_mod()).0)

                // [Fermat's little theorem]
                // if p is prime, for any integer a, a^p = a (mod p)
                // especially when a and b is coprime, a^(p-1) = 1 (mod p).
                // -> inverse of a is a^(p-2).

                //let mut ret = Self { x: 1 };
                //let mut mul: Self = *self;
                //let mut p = Self::get_mod() - 2;
                //while p > 0 {
                //    if p & 1 != 0 {
                //        ret *= mul;
                //    }
                //    p >>= 1;
                //    mul *= mul;
                //}
                //ret
            }
            #[inline(always)]
            pub fn pow(self, p: usize) -> Self {
                Self {
                    x: powmod(self.x, p, Self::get_mod()),
                }
            }
        }
        impl One for DynModInt {
            #[inline(always)]
            fn one() -> Self {
                Self { x: 1 }
            }
        }
        impl Zero for DynModInt {
            #[inline(always)]
            fn zero() -> Self {
                Self { x: 0 }
            }
            #[inline(always)]
            fn is_zero(&self) -> bool {
                self.x == 0
            }
            #[inline(always)]
            fn set_zero(&mut self) {
                self.x = 0;
            }
        }
        impl Add<Self> for DynModInt {
            type Output = Self;
            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                DynModInt::new(self.x + rhs.x)
            }
        }
        impl Sub<Self> for DynModInt {
            type Output = Self;
            #[inline(always)]
            fn sub(self, rhs: Self) -> Self::Output {
                DynModInt::new(self.x - rhs.x)
            }
        }
        impl Mul<Self> for DynModInt {
            type Output = Self;
            #[inline(always)]
            fn mul(self, rhs: Self) -> Self::Output {
                DynModInt::new(self.x * rhs.x)
            }
        }
        impl Div<Self> for DynModInt {
            type Output = Self;
            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn div(self, rhs: Self) -> Self::Output {
                DynModInt::new(self.x * rhs.inverse().x)
            }
        }
        impl AddAssign<Self> for DynModInt {
            #[inline(always)]
            fn add_assign(&mut self, rhs: Self) {
                *self = DynModInt::new(self.x + rhs.x);
            }
        }
        impl SubAssign<Self> for DynModInt {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: Self) {
                *self = DynModInt::new(self.x - rhs.x);
            }
        }
        impl MulAssign<Self> for DynModInt {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: Self) {
                *self = DynModInt::new(self.x * rhs.x);
            }
        }
        impl DivAssign<Self> for DynModInt {
            #[inline(always)]
            #[allow(clippy::suspicious_op_assign_impl)]
            fn div_assign(&mut self, rhs: Self) {
                *self = DynModInt::new(self.x * rhs.inverse().x)
            }
        }
        impl From<usize> for DynModInt {
            fn from(x: usize) -> Self {
                DynModInt::new(x as i64)
            }
        }
        impl From<i64> for DynModInt {
            fn from(x: i64) -> Self {
                DynModInt::new(x)
            }
        }
        impl std::str::FromStr for DynModInt {
            type Err = std::num::ParseIntError;
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s.parse::<i64>() {
                    Ok(x) => Ok(DynModInt::from(x)),
                    Err(e) => Err(e),
                }
            }
        }
        impl std::iter::Sum for DynModInt {
            fn sum<I: Iterator<Item = DynModInt>>(iter: I) -> Self {
                iter.fold(Self::zero(), |cum, v| cum + v)
            }
        }
        impl fmt::Display for DynModInt {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.x)
            }
        }
        impl fmt::Debug for DynModInt {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.x)
            }
        }
    }

    pub mod carry_mod_int {
        use super::powmod;
        use crate::gcd::ext_gcd;
        use num::{One, Zero};
        use std::fmt;
        use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};
        #[derive(Clone, Copy, Eq, Hash, PartialEq)]
        pub struct CarryModInt {
            x: i64,
            m: i64,
        }
        impl CarryModInt {
            #[inline(always)]
            pub fn get_mod(&self) -> i64 {
                self.m
            }
            #[inline(always)]
            pub fn val(&self) -> i64 {
                self.x
            }
            #[inline(always)]
            pub fn new(mut sig: i64, m: i64) -> Self {
                if sig < 0 {
                    let ab = (-sig + m - 1) / m;
                    sig += ab * m;
                    debug_assert!(sig >= 0);
                }
                Self { x: sig % m, m }
            }
            #[inline(always)]
            fn inverse(&self) -> Self {
                // x * inv_x + M * _ = gcd(x, M) = 1
                // x * inv_x = 1 (mod M)
                Self::new(ext_gcd(self.x, self.get_mod()).0, self.get_mod())

                // [Fermat's little theorem]
                // if p is prime, for any integer a, a^p = a (mod p)
                // especially when a and b is coprime, a^(p-1) = 1 (mod p).
                // -> inverse of a is a^(p-2).

                //let mut ret = Self { x: 1 };
                //let mut mul: Self = *self;
                //let mut p = Self::get_mod() - 2;
                //while p > 0 {
                //    if p & 1 != 0 {
                //        ret *= mul;
                //    }
                //    p >>= 1;
                //    mul *= mul;
                //}
                //ret
            }
            #[inline(always)]
            pub fn pow(self, p: usize) -> Self {
                Self {
                    x: powmod(self.x, p, self.get_mod()),
                    m: self.get_mod(),
                }
            }
        }
        impl Add<Self> for CarryModInt {
            type Output = Self;
            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                debug_assert!(self.get_mod() == rhs.get_mod());
                CarryModInt::new(self.x + rhs.x, self.get_mod())
            }
        }
        impl Sub<Self> for CarryModInt {
            type Output = Self;
            #[inline(always)]
            fn sub(self, rhs: Self) -> Self::Output {
                debug_assert!(self.get_mod() == rhs.get_mod());
                CarryModInt::new(self.x - rhs.x, self.get_mod())
            }
        }
        impl Mul<Self> for CarryModInt {
            type Output = Self;
            #[inline(always)]
            fn mul(self, rhs: Self) -> Self::Output {
                debug_assert!(self.get_mod() == rhs.get_mod());
                CarryModInt::new(self.x * rhs.x, self.get_mod())
            }
        }
        impl Div<Self> for CarryModInt {
            type Output = Self;
            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn div(self, rhs: Self) -> Self::Output {
                debug_assert!(self.get_mod() == rhs.get_mod());
                CarryModInt::new(self.x * rhs.inverse().x, self.get_mod())
            }
        }
        impl AddAssign<Self> for CarryModInt {
            #[inline(always)]
            fn add_assign(&mut self, rhs: Self) {
                debug_assert!(self.get_mod() == rhs.get_mod());
                *self = CarryModInt::new(self.x + rhs.x, self.get_mod());
            }
        }
        impl SubAssign<Self> for CarryModInt {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: Self) {
                debug_assert!(self.get_mod() == rhs.get_mod());
                *self = CarryModInt::new(self.x - rhs.x, self.get_mod());
            }
        }
        impl MulAssign<Self> for CarryModInt {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: Self) {
                debug_assert!(self.get_mod() == rhs.get_mod());
                *self = CarryModInt::new(self.x * rhs.x, self.get_mod());
            }
        }
        impl DivAssign<Self> for CarryModInt {
            #[inline(always)]
            #[allow(clippy::suspicious_op_assign_impl)]
            fn div_assign(&mut self, rhs: Self) {
                debug_assert!(self.get_mod() == rhs.get_mod());
                *self = CarryModInt::new(self.x * rhs.inverse().x, self.get_mod())
            }
        }
        impl std::iter::Sum for CarryModInt {
            fn sum<I: Iterator<Item = CarryModInt>>(mut iter: I) -> Self {
                let mut ret = iter.next().unwrap();
                for v in iter {
                    debug_assert!(ret.get_mod() == v.get_mod());
                    ret += v;
                }
                ret
            }
        }
        impl fmt::Display for CarryModInt {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.x)
            }
        }
        impl fmt::Debug for CarryModInt {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.x)
            }
        }
    }
}
use modint::{
    carry_mod_int::CarryModInt, dynamic_mod_int::DynModInt, powmod, static_mod_int::StaticModInt,
};

mod integer_operation {
    use num::{One, Zero};
    use std::collections::BTreeMap;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem};
    pub trait IntegerOperation {
        fn into_primes(self) -> BTreeMap<Self, usize>
        where
            Self: Sized;
        fn into_divisors(self) -> Vec<Self>
        where
            Self: Sized;
        fn squared_length(&self, rhs: Self) -> Self;
        fn is_prime(&self) -> bool;
    }
    impl<
            T: Copy
                + Ord
                + AddAssign
                + MulAssign
                + DivAssign
                + Add<Output = T>
                + Mul<Output = T>
                + Div<Output = T>
                + Rem<Output = T>
                + Zero
                + One,
        > IntegerOperation for T
    {
        fn into_primes(self) -> BTreeMap<T, usize> // O(N^0.5 x logN)
        {
            #[allow(clippy::eq_op)]
            if self == T::zero() {
                panic!("Zero has no divisors.");
            }
            #[allow(clippy::eq_op)]
            let two = T::one() + T::one();
            let three = two + T::one();
            let mut n = self;
            let mut ans = BTreeMap::new();
            while n % two == T::zero() {
                *ans.entry(two).or_insert(0) += 1;
                n /= two;
            }
            {
                let mut i = three;
                while i * i <= n {
                    while n % i == T::zero() {
                        *ans.entry(i).or_insert(0) += 1;
                        n /= i;
                    }
                    i += two;
                }
            }
            if n != T::one() {
                *ans.entry(n).or_insert(0) += 1;
            }
            ans
        }
        fn is_prime(&self) -> bool // O(N^0.5 x logN)
        {
            let primes = self.into_primes();
            primes.len() == 1 && primes.iter().next().unwrap().1 == &1
        }
        fn into_divisors(self) -> Vec<T> // O(N^0.5)
        {
            if self == T::zero() {
                panic!("Zero has no primes.");
            }
            let n = self;
            let mut ret: Vec<T> = Vec::new();
            {
                let mut i = T::one();
                while i * i <= n {
                    if n % i == T::zero() {
                        ret.push(i);
                        if i * i != n {
                            ret.push(n / i);
                        }
                    }
                    i += T::one();
                }
            }
            ret.sort();
            ret
        }
        fn squared_length(&self, rhs: Self) -> Self {
            *self * *self + rhs * rhs
        }
    }
    mod test {
        use super::IntegerOperation;
        #[test]
        fn is_prime() {
            for x in 2..1e5 as usize {
                let expected = (2..x).all(|px| x % px != 0);
                let actual = x.is_prime();
                assert_eq!(expected, actual);
            }
        }
    }
}
use integer_operation::IntegerOperation;

pub trait CoordinateCompress<T> {
    fn compress_encoder(&self) -> HashMap<T, usize>;
    fn compress_decoder(&self) -> Vec<T>;
    fn compress(self) -> Vec<usize>;
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for Vec<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for BTreeSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = HashMap::new();
        for (i, &key) in self.iter().enumerate() {
            dict.insert(key, i);
        }
        dict
    }
    fn compress_decoder(&self) -> Vec<T> {
        self.iter().copied().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        (0..self.len()).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for HashSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}

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

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
struct Line2d(i64, i64, i64);
impl Line2d {
    // identify line from 2 differemt point
    fn new(y0: i64, x0: i64, y1: i64, x1: i64) -> Line2d {
        let mut b = y1 - y0;
        let mut a = x1 - x0;
        let mut c = x1 * y0 - x0 * y1;
        let r = gcd(a.abs(), gcd(b.abs(), c.abs()));
        a /= r;
        b /= r;
        c /= r;
        if (a == 0) && (b < 0) {
            a = -a;
            b = -b;
            c = -c;
        }
        if a < 0 {
            a = -a;
            b = -b;
            c = -c;
        }
        Line2d(a, b, c)
    }
}

mod strongly_connected_component {
    pub struct StronglyConnectedComponent {
        n: usize,
        pub graph: Vec<Vec<usize>>,
        bwd_graph: Vec<Vec<usize>>,
    }
    impl StronglyConnectedComponent {
        pub fn new(n: usize) -> StronglyConnectedComponent {
            StronglyConnectedComponent {
                n,
                graph: vec![vec![]; n],
                bwd_graph: vec![vec![]; n],
            }
        }
        pub fn add(&mut self, from: usize, into: usize) {
            self.graph[from].push(into);
            self.bwd_graph[into].push(from);
        }
        pub fn decompose(&mut self) -> Vec<Vec<usize>> {
            let mut scc = Vec::<Vec<usize>>::new();
            let mut fwd_seen = vec![false; self.n];
            let mut order = Vec::<usize>::new();
            for i in 0..self.n {
                if !fwd_seen[i] {
                    StronglyConnectedComponent::fwd_dfs(
                        &self.graph,
                        i,
                        None,
                        &mut fwd_seen,
                        &mut order,
                    );
                }
            }
            order.reverse();
            let mut bwd_seen = vec![false; self.n];
            for i_ in &order {
                let i = *i_;
                if !bwd_seen[i] {
                    let mut grp = Vec::<usize>::new();
                    StronglyConnectedComponent::bwd_dfs(
                        &self.bwd_graph,
                        i,
                        None,
                        &mut bwd_seen,
                        &mut grp,
                    );
                    grp.reverse();
                    scc.push(grp);
                }
            }
            scc
        }
        fn bwd_dfs(
            graph: &Vec<Vec<usize>>,
            v: usize,
            pre: Option<usize>,
            seen: &mut Vec<bool>,
            grp: &mut Vec<usize>,
        ) {
            seen[v] = true;
            for nv_ in &graph[v] {
                let nv = *nv_;
                if let Some(pre_v) = pre {
                    if nv == pre_v {
                        continue;
                    }
                }
                if !seen[nv] {
                    StronglyConnectedComponent::bwd_dfs(graph, nv, Some(v), seen, grp);
                }
            }
            grp.push(v);
        }
        fn fwd_dfs(
            graph: &Vec<Vec<usize>>,
            v: usize,
            pre: Option<usize>,
            seen: &mut Vec<bool>,
            order: &mut Vec<usize>,
        ) {
            seen[v] = true;
            for nv_ in &graph[v] {
                let nv = *nv_;
                if let Some(pre_v) = pre {
                    if nv == pre_v {
                        continue;
                    }
                }
                if !seen[nv] {
                    StronglyConnectedComponent::fwd_dfs(graph, nv, Some(v), seen, order);
                }
            }
            order.push(v);
        }
    }
}
use strongly_connected_component::StronglyConnectedComponent as Scc;

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

pub struct PermutationIterator<T> {
    v: Vec<T>,
    is_first: bool,
}
impl<T: Copy + Ord + Clone> PermutationIterator<T> {
    pub fn new(mut v: Vec<T>) -> PermutationIterator<T> {
        v.sort();
        PermutationIterator { v, is_first: true }
    }
}
impl<T: Copy + Ord + Clone> Iterator for PermutationIterator<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_first {
            self.is_first = false;
            Some(self.v.clone())
        } else if self.v.next_permutation() {
            Some(self.v.clone())
        } else {
            None
        }
    }
}

pub trait IntoPermutations<T: Copy + Ord + Clone> {
    fn into_permutations(self) -> PermutationIterator<T>;
}
// implement for ones that has IntoIterator.
impl<T: Copy + Ord + Clone, I: IntoIterator<Item = T>> IntoPermutations<T> for I {
    fn into_permutations(self) -> PermutationIterator<T> {
        PermutationIterator::new(self.into_iter().collect())
    }
}
mod add_header {
    pub trait AddHeader<T> {
        fn add_header(&mut self, add_val: T);
    }
    impl<T> AddHeader<T> for Vec<T>
    where
        Vec<T>: Clone,
    {
        fn add_header(&mut self, add_val: T) {
            let cpy = self.clone();
            self.clear();
            self.push(add_val);
            for cpy_val in cpy {
                self.push(cpy_val);
            }
        }
    }
}
use add_header::AddHeader;

mod auto_sort_vec {
    use crate::segment_tree::SegmentTree;
    pub struct AutoSortVec {
        max_val: usize,
        st: SegmentTree<usize>,
    }
    impl AutoSortVec {
        pub fn new(max_val: usize) -> AutoSortVec {
            AutoSortVec {
                max_val,
                st: SegmentTree::<usize>::new(max_val + 1, |x, y| x + y, 0),
            }
        }
        pub fn len(&self) -> usize {
            self.st.query(0, self.max_val)
        }
        pub fn push(&mut self, val: usize) {
            self.st.add(val, 1);
        }
        pub fn remove_value(&mut self, val: usize) {
            self.st.sub(val, 1);
        }
        pub fn value_to_index(&self, val: usize) -> usize {
            if val == 0 {
                0
            } else {
                self.st.query(0, val - 1)
            }
        }
        pub fn at(&self, idx: usize) -> usize {
            let idx1 = idx + 1;
            if self.st.get(0) >= idx1 {
                0
            } else if self.st.query(0, self.max_val - 1) < idx1 {
                self.max_val
            } else {
                let mut l = 0;
                let mut r = self.max_val;
                while r - l > 1 {
                    let m = (r + l) / 2;
                    let sm = self.st.query(0, m);
                    if sm < idx1 {
                        l = m;
                    } else {
                        r = m;
                    }
                }
                r
            }
        }
    }
}
use auto_sort_vec::AutoSortVec;

mod my_string {
    use std::ops::{Index, IndexMut};
    use std::slice::SliceIndex;
    #[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct Str {
        vc: Vec<char>,
    }
    impl Str {
        pub fn new() -> Self {
            Self { vc: vec![] }
        }
        pub fn from(s: &str) -> Self {
            Self {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            }
        }
        pub fn len(&self) -> usize {
            self.vc.len()
        }
        pub fn clear(&mut self) {
            self.vc.clear()
        }
        pub fn is_empty(&self) -> bool {
            self.vc.is_empty()
        }
        pub fn first(&self) -> Option<&char> {
            self.vc.first()
        }
        pub fn last(&self) -> Option<&char> {
            self.vc.last()
        }
        pub fn push(&mut self, c: char) {
            self.vc.push(c);
        }
        pub fn push_str(&mut self, s: &str) {
            for c in s.to_string().chars().collect::<Vec<char>>().into_iter() {
                self.push(c);
            }
        }
        pub fn pop(&mut self) -> Option<char> {
            self.vc.pop()
        }
        pub fn into_iter(self) -> std::vec::IntoIter<char> {
            self.vc.into_iter()
        }
        pub fn iter(&self) -> std::slice::Iter<char> {
            self.vc.iter()
        }
        pub fn iter_mut(&mut self) -> std::slice::IterMut<char> {
            self.vc.iter_mut()
        }
        pub fn swap(&mut self, a: usize, b: usize) {
            self.vc.swap(a, b);
        }
        pub fn reverse(&mut self) {
            self.vc.reverse();
        }
        pub fn find(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.find(&p)
        }
        pub fn rfind(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.rfind(&p)
        }
        pub fn into_usize(self, base: char, offset: usize) -> Vec<usize> {
            self.vc
                .into_iter()
                .map(|c| (c as u8 - base as u8) as usize + offset)
                .collect::<Vec<usize>>()
        }
        pub fn sort(&mut self) {
            self.vc.sort();
        }
        pub fn remove(&mut self, index: usize) -> char {
            self.vc.remove(index)
        }
    }
    impl std::str::FromStr for Str {
        type Err = ();
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Str {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            })
        }
    }
    impl<Idx: SliceIndex<[char]>> Index<Idx> for Str {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vc[i]
        }
    }
    impl<Idx: SliceIndex<[char]>> IndexMut<Idx> for Str {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vc[index]
        }
    }
    impl std::ops::Add<Str> for Str {
        type Output = Str;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            for c in rhs.into_iter() {
                ret.vc.push(c);
            }
            ret
        }
    }
    impl std::ops::AddAssign<Str> for Str {
        fn add_assign(&mut self, rhs: Self) {
            for c in rhs.into_iter() {
                self.vc.push(c);
            }
        }
    }
    impl std::ops::Add<char> for Str {
        type Output = Str;
        fn add(self, rhs: char) -> Self::Output {
            let mut ret = self;
            ret.vc.push(rhs);
            ret
        }
    }
    impl std::ops::AddAssign<char> for Str {
        fn add_assign(&mut self, rhs: char) {
            self.vc.push(rhs);
        }
    }
    impl std::fmt::Display for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
    impl std::fmt::Debug for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
}
use my_string::Str;

mod rolling_hash {
    use u64 as htype;
    const MODS: [htype; 2] = [1000000007, 998244353];
    pub struct RollingHash {
        cum_hashes: Vec<Vec<htype>>,
        base: usize,
        base_powers: Vec<Vec<htype>>,
        base_powers_inv: Vec<Vec<htype>>,
    }
    pub struct RollingHashValue<'a> {
        org: &'a RollingHash,
        i0: usize,
        i1: usize,
    }
    pub trait GenRollingHash {
        fn rolling_hash(&self, base: usize) -> RollingHash;
    }
    impl GenRollingHash for Vec<usize> {
        fn rolling_hash(&self, base: usize) -> RollingHash {
            RollingHash::new(self, base)
        }
    }
    impl RollingHash {
        pub fn new(values: &[usize], base: usize) -> RollingHash {
            let n = values.len();

            let mut base_powers = vec![vec![1; n]; 2];
            for m in 0..2 {
                for p in 1..n {
                    base_powers[m][p] = (base_powers[m][p - 1] * base as htype) % MODS[m];
                }
            }

            let calc_inv_base = |md: u64, base: htype| -> htype {
                let mut p = md - 2;
                let mut ret: htype = 1;
                let mut mul = base;
                while p > 0 {
                    if p & 1 != 0 {
                        ret = (ret * mul) % md;
                    }
                    p >>= 1;
                    mul = (mul * mul) % md;
                }
                ret
            };
            let inv_bases = (0..2)
                .map(|m| calc_inv_base(MODS[m], base as htype))
                .collect::<Vec<_>>();

            let mut base_powers_inv = vec![vec![1; n]; 2];
            for m in 0..2 {
                for p in 1..n {
                    base_powers_inv[m][p] = (base_powers_inv[m][p - 1] * inv_bases[m]) % MODS[m];
                }
            }

            let mut cum_hashes = (0..2)
                .map(|m| {
                    (0..n)
                        .map(|i| (values[i] as htype * base_powers[m][i]) % MODS[m])
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<Vec<_>>>();

            for m in 0..2 {
                for i in 1..n {
                    cum_hashes[m][i] += cum_hashes[m][i - 1];
                    cum_hashes[m][i] %= MODS[m];
                }
            }

            Self {
                cum_hashes,
                base,
                base_powers,
                base_powers_inv,
            }
        }
        // hash value of array range (closed interval, [i0, i1])
        pub fn hash(&self, i0: usize, i1: usize) -> RollingHashValue {
            RollingHashValue { org: self, i0, i1 }
        }
    }
    impl<'a> RollingHashValue<'a> {
        fn get(&'a self) -> (htype, htype) {
            let retv = if self.i0 > 0 {
                (0..2)
                    .map(|m| {
                        ((MODS[m] + self.org.cum_hashes[m][self.i1]
                            - self.org.cum_hashes[m][self.i0 - 1])
                            * self.org.base_powers_inv[m][self.i0])
                            % MODS[m]
                    })
                    .collect::<Vec<_>>()
            } else {
                (0..2)
                    .map(|m| self.org.cum_hashes[m][self.i1])
                    .collect::<Vec<_>>()
            };
            (retv[0], retv[1])
        }
    }
    impl PartialEq for RollingHashValue<'_> {
        fn eq(&self, other: &Self) -> bool {
            debug_assert!(self.i1 - self.i0 == other.i1 - other.i0);
            self.get() == other.get()
        }
    }
}
use rolling_hash::*;

mod rational {
    use crate::gcd::gcd;
    use std::cmp::Ordering;
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Rational {
        pub num: i64,
        pub denom: i64,
    }
    impl Rational {
        pub fn new(num: i64, denom: i64) -> Self {
            if num == 0 {
                if denom == 0 {
                    panic!("0/0 is indefinite.")
                } else {
                    Self { num: 0, denom: 1 }
                }
            } else if denom == 0 {
                Self { num: 1, denom: 0 }
            } else {
                let (num, denom) = {
                    if denom < 0 {
                        (-num, -denom)
                    } else {
                        (num, denom)
                    }
                };
                let g = gcd(num.abs(), denom.abs());
                debug_assert!(denom >= 0);
                Self {
                    num: num / g,
                    denom: denom / g,
                }
            }
        }
    }
    impl AddAssign<Self> for Rational {
        fn add_assign(&mut self, rhs: Self) {
            let d0 = self.denom.abs();
            let d1 = rhs.denom.abs();
            let denom = d0 * (d1 / gcd(d0, d1));
            let n0 = self.num * (denom / d0);
            let n1 = rhs.num * (denom / d1);
            *self = Self::new(n0 + n1, denom);
        }
    }
    impl Add<Self> for Rational {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret += rhs;
            ret
        }
    }
    impl SubAssign<Self> for Rational {
        fn sub_assign(&mut self, rhs: Self) {
            *self += Self::new(-rhs.num, rhs.denom);
        }
    }
    impl Sub<Self> for Rational {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret -= rhs;
            ret
        }
    }
    impl MulAssign<Self> for Rational {
        fn mul_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.num, self.denom * rhs.denom);
        }
    }
    impl Mul<Self> for Rational {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret *= rhs;
            ret
        }
    }
    impl DivAssign<Self> for Rational {
        fn div_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.denom, rhs.num * self.denom);
        }
    }
    impl Div<Self> for Rational {
        type Output = Self;
        fn div(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret /= rhs;
            ret
        }
    }
    impl Neg for Rational {
        type Output = Self;
        fn neg(self) -> Self::Output {
            Self::new(-self.num, self.denom)
        }
    }
    impl PartialOrd for Rational {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(i64::cmp(
                &(self.num * other.denom),
                &(self.denom * other.num),
            ))
        }
    }
    impl Ord for Rational {
        fn cmp(&self, other: &Self) -> Ordering {
            Self::partial_cmp(self, other).unwrap()
        }
    }
    impl fmt::Display for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
    impl fmt::Debug for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
}
use rational::Rational;

fn z_algo(s: &[usize]) -> Vec<usize> {
    // https://www.youtube.com/watch?v=f6ct5PQHqM0
    let n = s.len();
    let mut last_match = None;
    let mut ret = vec![0; n];
    ret[0] = n;
    for i in 1..n {
        let mut match_delta = 0;
        if let Some((m0, m1)) = last_match {
            if i < m1 {
                // reuse calculated info.
                if i + ret[i - m0] != m1 {
                    // built from old one, and finish.
                    ret[i] = min(ret[i - m0], m1 - i);
                    continue;
                } else {
                    // skip known range, and continues.
                    match_delta = m1 - i;
                }
            }
        }
        // expand until unmatch is found.
        while i + match_delta < n {
            if s[match_delta] == s[i + match_delta] {
                match_delta += 1;
            } else {
                break;
            }
        }
        // set header-match lentgh.
        ret[i] = match_delta;
        // update last match range for future use.
        if let Some((_m0, m1)) = last_match {
            if i + match_delta <= m1 {
                continue;
            }
        }
        last_match = Some((i, i + match_delta));
    }
    ret
}

mod convex_hull {
    use super::{ChangeMinMax, Rational};
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    pub struct ConvexHull {
        x_ys: BTreeMap<i64, Vec<i64>>,
    }
    impl ConvexHull {
        pub fn new() -> Self {
            Self {
                x_ys: BTreeMap::new(),
            }
        }
        pub fn add(&mut self, y: i64, x: i64) {
            self.x_ys.entry(x).or_default().push(y);
        }
        pub fn convex_hull(&self) -> Vec<(i64, i64)> {
            let mut x_ys = self
                .x_ys
                .iter()
                .map(|(x, ys)| (*x, ys.clone()))
                .collect::<Vec<_>>();
            // lower
            x_ys.iter_mut().for_each(|(_x, ys)| {
                ys.sort();
            });
            let lower_yx = Self::weakly_monotone_tangents(&x_ys);
            // upper
            x_ys.iter_mut().for_each(|(_x, ys)| {
                ys.reverse();
            });
            x_ys.reverse();
            let upper_yx = Self::weakly_monotone_tangents(&x_ys);
            let mut ret = vec![];
            let mut seen = BTreeSet::new();
            for (y, x) in lower_yx.into_iter().chain(upper_yx.into_iter()) {
                if seen.contains(&(y, x)) {
                    continue;
                }
                ret.push((y, x));
                seen.insert((y, x));
            }
            ret
        }
        fn weakly_monotone_tangents(x_ys: &[(i64, Vec<i64>)]) -> VecDeque<(i64, i64)> {
            let mut vs = VecDeque::new();
            for (x, ys) in x_ys.iter() {
                let x = *x;
                let y = ys[0];
                if vs.is_empty() {
                    vs.push_back((y, x));
                    continue;
                }
                while vs.len() >= 2 {
                    let (y0, x0) = vs.pop_back().unwrap();
                    let (y1, x1) = vs.pop_back().unwrap();
                    let t0 = Rational::new(y0 - y, x0 - x);
                    let t1 = Rational::new(y1 - y, x1 - x);
                    if t0 < t1 {
                        vs.push_back((y1, x1));
                    } else {
                        vs.push_back((y1, x1));
                        vs.push_back((y0, x0));
                        break;
                    }
                }
                vs.push_back((y, x));
            }
            if let Some((x, ys)) = x_ys.last() {
                let x = *x;
                for &y in ys.iter().skip(1) {
                    vs.push_back((y, x))
                }
            }
            if let Some((x, ys)) = x_ys.first() {
                let x = *x;
                for &y in ys.iter().skip(1) {
                    vs.push_front((y, x))
                }
            }
            vs
        }
    }
}
use convex_hull::ConvexHull;

mod matrix {
    use num::{One, Zero};
    use std::iter::Sum;
    use std::ops::{Add, Index, IndexMut, Mul, MulAssign, Sub};
    use std::slice::SliceIndex;
    #[derive(Clone)]
    pub struct Matrix<T> {
        h: usize,
        w: usize,
        vals: Vec<Vec<T>>,
    }
    impl<T: Clone + Copy + One + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + Zero + One>
        Matrix<T>
    {
        pub fn new(h: usize, w: usize) -> Self {
            Self {
                h,
                w,
                vals: vec![vec![T::zero(); w]; h],
            }
        }
        pub fn identity(h: usize, w: usize) -> Self {
            debug_assert!(h == w);
            let mut vals = vec![vec![T::zero(); w]; h];
            for (y, line) in vals.iter_mut().enumerate() {
                for (x, val) in line.iter_mut().enumerate() {
                    *val = if y == x { T::one() } else { T::zero() };
                }
            }
            Self { h, w, vals }
        }
        pub fn pow(&self, mut p: usize) -> Self {
            let mut ret = Self::identity(self.h, self.w);
            let mut mul = self.clone();
            while p > 0 {
                if p & 1 != 0 {
                    ret = ret.clone() * mul.clone();
                }
                p >>= 1;
                mul = mul.clone() * mul.clone();
            }
            ret
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> Index<Idx> for Matrix<T> {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vals[i]
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> IndexMut<Idx> for Matrix<T> {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vals[index]
        }
    }
    impl<T: Clone + Copy + One + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + Zero + One>
        Mul<Matrix<T>> for Matrix<T>
    {
        type Output = Matrix<T>;
        fn mul(self, rhs: Matrix<T>) -> Self::Output {
            debug_assert!(self.w == rhs.h);
            let mut ret = Self::new(self.h, rhs.w);
            for y in 0..ret.h {
                for x in 0..ret.w {
                    ret[y][x] = (0..self.w).map(|i| self[y][i] * rhs[i][x]).sum::<T>();
                }
            }
            ret
        }
    }
    impl<T: Clone + Copy + Mul + Sum<<T as Mul>::Output>> Mul<Vec<T>> for Matrix<T> {
        type Output = Vec<T>;
        fn mul(self, rhs: Vec<T>) -> Self::Output {
            debug_assert!(self.w == rhs.len());
            (0..self.h)
                .map(|y| (0..self.w).map(|x| self[y][x] * rhs[x]).sum::<T>())
                .collect::<Vec<_>>()
        }
    }
    impl<T: Clone + Copy + Mul + Sum<<T as Mul>::Output>> Mul<Matrix<T>> for Vec<T> {
        type Output = Vec<T>;
        fn mul(self, rhs: Matrix<T>) -> Self::Output {
            debug_assert!(self.len() == rhs.h);
            (0..rhs.w)
                .map(|x| (0..rhs.h).map(|y| self[y] * rhs[y][x]).sum::<T>())
                .collect::<Vec<_>>()
        }
    }
    impl<
            T: Clone
                + Copy
                + One
                + Add<Output = T>
                + Sub<Output = T>
                + Mul
                + Sum<<T as Mul>::Output>
                + Zero
                + One,
        > Add<Matrix<T>> for Matrix<T>
    {
        type Output = Matrix<T>;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = Matrix::<T>::new(self.h, self.w);
            for y in 0..self.h {
                for x in 0..self.w {
                    ret[y][x] = self[y][x] + rhs[y][x];
                }
            }
            ret
        }
    }
    impl<T: Clone + Copy + One + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + Zero + One>
        MulAssign<Matrix<T>> for Matrix<T>
    {
        fn mul_assign(&mut self, rhs: Matrix<T>) {
            *self = self.clone() * rhs;
        }
    }
}
use matrix::Matrix;

mod suffix_array {
    use std::cmp::Ordering;
    use std::mem::swap;
    fn compare(pos_to_ord: &[i64], i: usize, j: usize, k: usize, n: usize) -> Ordering {
        let ri0 = pos_to_ord[i];
        let rj0 = pos_to_ord[j];
        let ri1 = if i + k <= n { pos_to_ord[i + k] } else { -1 };
        let rj1 = if j + k <= n { pos_to_ord[j + k] } else { -1 };
        (ri0, ri1).cmp(&(rj0, rj1))
    }
    fn construct_suffix_array(s: &[usize]) -> Vec<usize> {
        let n = s.len();
        let mut ord_to_pos = vec![0usize; n + 1];
        let mut pos_to_ord = vec![0i64; n + 1];
        let mut pos_to_ord_nxt = vec![0i64; n + 1];
        for i in 0..=n {
            ord_to_pos[i] = i;
            pos_to_ord[i] = if i < n { s[i] as i64 } else { -1 };
        }
        let mut k = 1;
        while k <= n {
            ord_to_pos.sort_by(|&i, &j| compare(&pos_to_ord, i, j, k, n));
            pos_to_ord_nxt[ord_to_pos[0]] = 0;
            for ord in 1..=n {
                pos_to_ord_nxt[ord_to_pos[ord]] = pos_to_ord_nxt[ord_to_pos[ord - 1]]
                    + if compare(&pos_to_ord, ord_to_pos[ord - 1], ord_to_pos[ord], k, n)
                        == Ordering::Less
                    {
                        1
                    } else {
                        0
                    };
            }
            //
            k *= 2;
            swap(&mut pos_to_ord, &mut pos_to_ord_nxt);
        }
        ord_to_pos
    }
    fn construct_longest_common_prefix(s: &[usize], ord_to_pos: &[usize]) -> Vec<usize> {
        let n = s.len();
        debug_assert_eq!(ord_to_pos.len(), n + 1);
        let pos_to_ord = {
            let mut pos_to_ord = vec![0; ord_to_pos.len()];
            for (ord, &pos) in ord_to_pos.iter().enumerate() {
                pos_to_ord[pos] = ord;
            }
            pos_to_ord
        };
        let mut lcp_now = 0usize;
        let mut lcp = vec![0; n];
        for pos in 0..n {
            let pre_ord = pos_to_ord[pos] - 1;
            let pre_ord_pos = ord_to_pos[pre_ord];
            lcp_now = lcp_now.saturating_sub(1);
            while pre_ord_pos + lcp_now < n && pos + lcp_now < n {
                if s[pre_ord_pos + lcp_now] == s[pos + lcp_now] {
                    lcp_now += 1;
                } else {
                    break;
                }
            }
            lcp[pre_ord] = lcp_now;
        }
        lcp
    }
    pub trait ToSuffixArray {
        fn suffix_array(&self) -> (Vec<usize>, Vec<usize>);
    }
    impl ToSuffixArray for Vec<usize> {
        fn suffix_array(&self) -> (Vec<usize>, Vec<usize>) {
            let ord_to_pos = construct_suffix_array(self);
            let lcp = construct_longest_common_prefix(self, &ord_to_pos);
            (ord_to_pos, lcp)
        }
    }
    mod test {
        const T: usize = 100;
        const N: usize = 100;
        const C: usize = 26;
        use super::super::XorShift64;
        use super::ToSuffixArray;
        #[test]
        fn suffix_array() {
            let mut rand = XorShift64::new();
            for n in 1..=N {
                for _ in 0..T {
                    let a = (0..n).map(|_| rand.next_usize() % C).collect::<Vec<_>>();
                    let sa_expected = {
                        let mut sa_expected = (0..=n).collect::<Vec<_>>();
                        sa_expected.sort_by(|&i, &j| a[i..].cmp(&a[j..]));
                        sa_expected
                    };
                    let lcp_expected = (0..n)
                        .map(|i| {
                            (0..)
                                .take_while(|&d| {
                                    (sa_expected[i] + d < n)
                                        && (sa_expected[i + 1] + d < n)
                                        && a[sa_expected[i] + d] == a[sa_expected[i + 1] + d]
                                })
                                .count()
                        })
                        .collect::<Vec<_>>();
                    let (sa_actual, lcp_actual) = a.suffix_array();
                    assert_eq!(sa_expected, sa_actual);
                    assert_eq!(lcp_expected, lcp_actual);
                }
            }
        }
    }
}
use suffix_array::ToSuffixArray;

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

/*
mod convolution {
    // https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
    use crate::{modint::ModInt as mint, IntegerOperation};
    pub fn convolution(arga: &[mint], argb: &[mint]) -> Vec<mint> {
        let n = arga.len();
        let m = argb.len();
        let z = 1 << ceil_pow2(n + m - 1);
        let mut a = vec![mint::from(0); z];
        let mut b = vec![mint::from(0); z];
        for (a, &arga) in a.iter_mut().zip(arga.iter()) {
            *a = arga;
        }
        butterfly(&mut a);
        for (b, &argb) in b.iter_mut().zip(argb.iter()) {
            *b = argb;
        }
        butterfly(&mut b);
        for (a, b) in a.iter_mut().zip(b.into_iter()) {
            *a *= b;
        }
        butterfly_inv(&mut a);
        while a.len() > n + m - 1 {
            a.pop();
        }
        let iz = mint::from(1) / mint::from(z);
        for a in a.iter_mut() {
            *a *= iz;
        }
        a
    }
    // returns 'r' s.t. 'r^(m - 1) == 1 (mod m)'
    fn primitive_root(m: i64) -> i64 {
        debug_assert!(is_prime(m));
        if m == 2 {
            return 1;
        }
        if m == 167772161 {
            return 3;
        }
        if m == 469762049 {
            return 3;
        }
        if m == 754974721 {
            return 11;
        }
        if m == 998244353 {
            return 3;
        }
        if m == 1000000007 {
            return 5;
        }
        let divs = ((m - 1) / 2).into_primes();

        for g in 2.. {
            let mut ok = true;
            for (&div, _) in divs.iter() {
                fn pow_mod(x: i64, mut p: i64, m: i64) -> i64 {
                    let mut ret = 1;
                    let mut mul = x % m;
                    while p > 0 {
                        if p & 1 != 0 {
                            ret *= mul;
                            ret %= m;
                        }
                        p >>= 1;
                        mul *= mul;
                        mul %= m;
                    }
                    ret
                }

                if pow_mod(g, (m - 1) / div, m) == 1 {
                    ok = false;
                    break;
                }
            }
            if ok {
                return g;
            }
        }
        unreachable!();
    }
    fn is_prime(x: i64) -> bool {
        if x == 1 {
            return false;
        }
        for i in 2.. {
            if i * i > x {
                return true;
            }
            if x % i == 0 {
                return false;
            }
        }
        unreachable!();
    }
    struct FFTinfo {
        root: Vec<mint>,  // root[i]^(2^i) == 1
        iroot: Vec<mint>, // root[i] * iroot[i] == 1
        rate2: Vec<mint>,
        irate2: Vec<mint>,
        rate3: Vec<mint>,
        irate3: Vec<mint>,
    }
    // returns minimum non-negative `x` s.t. `(n & (1 << x)) != 0`
    fn bsf(n: usize) -> usize {
        let mut x = 0;
        while (n & (1 << x)) == 0 {
            x += 1;
        }
        x
    }
    impl FFTinfo {
        fn new() -> Self {
            let rank2 = bsf((mint::get_mod() - 1) as usize);
            let mut root = vec![mint::from(0); rank2 + 1];
            let mut iroot = vec![mint::from(0); rank2 + 1];
            let mut rate2 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut irate2 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut rate3 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];
            let mut irate3 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];

            let g = primitive_root(mint::get_mod());
            root[rank2] = mint::from(g).pow((mint::get_mod() as usize - 1) >> rank2);
            iroot[rank2] = mint::from(1) / root[rank2];
            for i in (0..rank2).rev() {
                root[i] = root[i + 1] * root[i + 1];
                iroot[i] = iroot[i + 1] * iroot[i + 1];
            }

            {
                let mut prod = mint::from(1);
                let mut iprod = mint::from(1);
                for i in 0..=(rank2 - 2) {
                    rate2[i] = root[i + 2] * prod;
                    irate2[i] = iroot[i + 2] * iprod;
                    prod *= iroot[i + 2];
                    iprod *= root[i + 2];
                }
            }
            {
                let mut prod = mint::from(1);
                let mut iprod = mint::from(1);
                for i in 0..=(rank2 - 3) {
                    rate3[i] = root[i + 3] * prod;
                    irate3[i] = iroot[i + 3] * iprod;
                    prod *= iroot[i + 3];
                    iprod *= root[i + 3];
                }
            }

            Self {
                root,
                iroot,
                rate2,
                irate2,
                rate3,
                irate3,
            }
        }
    }
    fn ceil_pow2(n: usize) -> usize {
        let mut x = 0;
        while (1 << x) < n {
            x += 1;
        }
        x
    }
    fn butterfly(a: &mut [mint]) {
        let n = a.len();
        let h = ceil_pow2(n);

        let info = FFTinfo::new();

        let mut len = 0; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
        while len < h {
            if h - len == 1 {
                let p = 1 << (h - len - 1);
                let mut rot = mint::from(1);
                for s in 0..(1 << len) {
                    let offset = s << (h - len);
                    for i in 0..p {
                        let l = a[i + offset];
                        let r = a[i + offset + p] * rot;
                        a[i + offset] = l + r;
                        a[i + offset + p] = l - r;
                    }
                    if s + 1 != (1 << len) {
                        rot *= info.rate2[bsf(!s)];
                    }
                }
                len += 1;
            } else {
                // 4-base
                let p = 1 << (h - len - 2);
                let mut rot = mint::from(1);
                let imag = info.root[2];
                for s in 0..(1 << len) {
                    let rot2 = rot * rot;
                    let rot3 = rot2 * rot;
                    let offset = s << (h - len);
                    for i in 0..p {
                        let mod2 = mint::get_mod() * mint::get_mod();
                        let a0 = a[i + offset].val();
                        let a1 = a[i + offset + p].val() * rot.val();
                        let a2 = a[i + offset + 2 * p].val() * rot2.val();
                        let a3 = a[i + offset + 3 * p].val() * rot3.val();
                        let a1na3imag = mint::from(a1 + mod2 - a3).val() * imag.val();
                        let na2 = mod2 - a2;
                        a[i + offset] = mint::from(a0 + a2 + a1 + a3);
                        a[i + offset + p] = mint::from(a0 + a2 + (2 * mod2 - (a1 + a3)));
                        a[i + offset + 2 * p] = mint::from(a0 + na2 + a1na3imag);
                        a[i + offset + 3 * p] = mint::from(a0 + na2 + (mod2 - a1na3imag));
                    }
                    if s + 1 != (1 << len) {
                        rot *= info.rate3[bsf(!s)];
                    }
                }
                len += 2;
            }
        }
    }
    fn butterfly_inv(a: &mut [mint]) {
        let n = a.len();
        let h = ceil_pow2(n);

        let info = FFTinfo::new();

        let mut len = h; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
        while len > 0 {
            if len == 1 {
                let p = 1 << (h - len);
                let mut irot = mint::from(1);
                for s in 0..(1 << (len - 1)) {
                    let offset = s << (h - len + 1);
                    for i in 0..p {
                        let l = a[i + offset];
                        let r = a[i + offset + p];
                        a[i + offset] = l + r;
                        a[i + offset + p] =
                            mint::from((mint::get_mod() + l.val() - r.val()) * irot.val());
                    }
                    if s + 1 != (1 << (len - 1)) {
                        irot *= info.irate2[bsf(!s)];
                    }
                }
                len -= 1;
            } else {
                // 4-base
                let p = 1 << (h - len);
                let mut irot = mint::from(1);
                let iimag = info.iroot[2];
                for s in 0..(1 << (len - 2)) {
                    let irot2 = irot * irot;
                    let irot3 = irot2 * irot;
                    let offset = s << (h - len + 2);
                    for i in 0..p {
                        let a0 = a[i + offset].val();
                        let a1 = a[i + offset + p].val();
                        let a2 = a[i + offset + 2 * p].val();
                        let a3 = a[i + offset + 3 * p].val();
                        let a2na3iimag =
                            mint::from((mint::get_mod() + a2 - a3) * iimag.val()).val();
                        a[i + offset] = mint::from(a0 + a1 + a2 + a3);
                        a[i + offset + p] =
                            mint::from((a0 + (mint::get_mod() - a1) + a2na3iimag) * irot.val());
                        a[i + offset + 2 * p] = mint::from(
                            (a0 + a1 + (mint::get_mod() - a2) + (mint::get_mod() - a3))
                                * irot2.val(),
                        );
                        a[i + offset + 3 * p] = mint::from(
                            (a0 + (mint::get_mod() - a1) + (mint::get_mod() - a2na3iimag))
                                * irot3.val(),
                        );
                    }
                    if s + 1 != (1 << (len - 2)) {
                        irot *= info.irate3[bsf(!s)];
                    }
                }
                len -= 2;
            }
        }
    }
}
use convolution::convolution;
*/

mod manhattan_mst {
    use crate::change_min_max::ChangeMinMax;
    use crate::{segment_tree::SegmentTree, CoordinateCompress, UnionFind};
    use std::cmp::{min, Reverse};
    use std::collections::BinaryHeap;
    pub struct ManhattanMST {
        points: Vec<(usize, (i64, i64))>,
    }
    impl ManhattanMST {
        pub fn new() -> Self {
            Self { points: vec![] }
        }
        pub fn push(&mut self, pt: (i64, i64)) {
            self.points.push((self.points.len(), pt));
        }
        fn mst(mut edges: Vec<(i64, usize, usize)>, n: usize) -> Vec<Vec<(i64, usize)>> {
            let mut uf = UnionFind::new(n);
            let mut g = vec![vec![]; n];
            edges.sort();
            for (delta, i, j) in edges {
                if !uf.same(i, j) {
                    uf.unite(i, j);
                    g[i].push((delta, j));
                    g[j].push((delta, i));
                }
            }
            g
        }
        pub fn minimum_spanning_tree(&mut self) -> Vec<Vec<(i64, usize)>> {
            let n = self.points.len();
            let mut edges = vec![];
            let inf = 1i64 << 60;
            for h0 in 0..2 {
                for h1 in 0..2 {
                    let y_enc = self
                        .points
                        .iter()
                        .map(|&(_i, (y, _x))| y)
                        .collect::<Vec<_>>()
                        .compress_encoder();
                    for h2 in 0..2 {
                        let mut st = SegmentTree::<(usize, i64)>::new(
                            n,
                            |(i0, ypx0), (i1, ypx1)| {
                                if ypx0 < ypx1 {
                                    (i0, ypx0)
                                } else {
                                    (i1, ypx1)
                                }
                            },
                            (0, inf),
                        );
                        self.points
                            .sort_by(|(_i0, (y0, x0)), (_i1, (y1, x1))| (y0 - x0).cmp(&(y1 - x1)));
                        for &(i, (y, x)) in self.points.iter() {
                            let ey = y_enc[&y];
                            let q = st.query(ey, n - 1);
                            if q.1 != inf {
                                let delta = q.1 - (y + x);
                                debug_assert!(delta >= 0);
                                edges.push((delta, i, q.0));
                            }
                            //
                            if st.get(ey).1 > y + x {
                                st.set(ey, (i, y + x));
                            }
                        }
                        if h2 == 0 {
                            self.points.iter_mut().for_each(|(_i, (_y, x))| *x = -(*x));
                        }
                    }
                    if h1 == 0 {
                        self.points.iter_mut().for_each(|(_i, (y, _x))| *y = -(*y));
                    }
                }
                if h0 == 0 {
                    self.points
                        .iter_mut()
                        .for_each(|(_i, (y, x))| std::mem::swap(x, y));
                }
            }
            Self::mst(edges, n)
        }
    }
}
use manhattan_mst::ManhattanMST;

mod mo {
    use std::iter::{Chain, Rev};
    use std::ops::{Range, RangeInclusive};
    use std::vec::IntoIter;
    pub struct Mo {
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    pub struct MoIterator {
        index_iter: IntoIter<usize>,
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    impl Mo {
        pub fn new() -> Self {
            Self {
                ls: vec![],
                rs: vec![],
            }
        }
        pub fn add_range_queue(&mut self, l: usize, r: usize) {
            self.ls.push(l);
            self.rs.push(r);
        }
        pub fn into_iter(self) -> MoIterator {
            let n = self.rs.iter().max().unwrap() + 1;
            let q = self.rs.len();
            let d = n / ((q as f64).sqrt() as usize + 1) + 1;
            let mut indexes = (0..q).collect::<Vec<_>>();
            indexes.sort_by_cached_key(|&i| {
                let div = self.ls[i] / d;
                if div % 2 == 0 {
                    (div, self.rs[i])
                } else {
                    (div, n - self.rs[i])
                }
            });
            MoIterator {
                index_iter: indexes.into_iter(),
                ls: self.ls,
                rs: self.rs,
            }
        }
        pub fn add_chain(
            l0: usize,
            r0: usize,
            l1: usize,
            r1: usize,
        ) -> Chain<Rev<Range<usize>>, RangeInclusive<usize>> {
            (l1..l0).rev().chain(r0 + 1..=r1)
        }
        pub fn remove_chain(
            l0: usize,
            r0: usize,
            l1: usize,
            r1: usize,
        ) -> Chain<Range<usize>, Rev<RangeInclusive<usize>>> {
            (l0..l1).chain(((r1 + 1)..=r0).rev())
        }
    }
    impl Iterator for MoIterator {
        type Item = (usize, (usize, usize));
        fn next(&mut self) -> Option<Self::Item> {
            if let Some(i) = self.index_iter.next() {
                Some((i, (self.ls[i], self.rs[i])))
            } else {
                None
            }
        }
    }
}
use mo::*;

mod heavy_light_decomposition {
    use crate::ChangeMinMax;
    use crate::UnionFind;

    // use entry order as inclusive array range, for segment-tree.
    pub struct Hld {
        entry_order: Vec<usize>, // order of entrying each node
        leave_order: Vec<usize>, // order of leaving each node
        head_of: Vec<usize>,     // the shallowest node of heavy path that the node belongs to.
        sub_size: Vec<usize>,    // subtree size.
        g: Vec<Vec<usize>>,      // linked-list graph.
        root: usize,             // root of whole tree
        uf: UnionFind,           // for a trigger of auto build
        par: Vec<usize>,         // parent for each node
        depth: Vec<usize>,       // step distance from root
    }
    impl Hld {
        pub fn new(n: usize, root: usize) -> Self {
            Self {
                entry_order: vec![n; n],
                leave_order: vec![n; n],
                head_of: vec![n; n],
                sub_size: vec![n + 1; n],
                g: vec![vec![]; n],
                root,
                uf: UnionFind::new(n),
                par: vec![n; n],
                depth: vec![n; n],
            }
        }
        pub fn add_edge(&mut self, a: usize, b: usize) {
            self.g[a].push(b);
            self.g[b].push(a);
            self.uf.unite(a, b);
            if self.uf.group_num() == 1 {
                self.build();
            }
        }
        fn build(&mut self) {
            self.depth[self.root] = 0;
            self.dfs_sz(self.root, self.g.len());
            self.dfs_hld(self.root, self.g.len(), self.root, &mut 0);
        }
        fn dfs_sz(&mut self, v: usize, pre: usize) {
            self.sub_size[v] = 1;
            for nv in self.g[v].clone() {
                if nv == pre {
                    continue;
                }
                self.par[nv] = v;
                self.depth[nv] = self.depth[v] + 1;
                self.dfs_sz(nv, v);
                self.sub_size[v] += self.sub_size[nv];
            }
        }
        fn dfs_hld(&mut self, v: usize, pre: usize, head: usize, vis_cnt: &mut usize) {
            self.head_of[v] = head;
            self.entry_order[v] = *vis_cnt;
            *vis_cnt += 1;
            let mut sub_size_max = None;
            let mut sub_size_max_ei = 0;
            for (ei, nv) in self.g[v].iter().copied().enumerate() {
                if nv == pre {
                    continue;
                }
                if sub_size_max.chmax(self.sub_size[nv]) {
                    sub_size_max_ei = ei;
                }
            }
            if sub_size_max.is_some() {
                // set heavy child at g[v][0]
                if sub_size_max_ei != 0 {
                    self.g[v].swap(0, sub_size_max_ei);
                }

                for (ei, nv) in self.g[v].clone().into_iter().enumerate() {
                    if nv == pre {
                        continue;
                    }
                    let nhead = if ei == 0 { head } else { nv };
                    self.dfs_hld(nv, v, nhead, vis_cnt);
                }
            }
            self.leave_order[v] = *vis_cnt;
        }
        pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
            while self.head_of[a] != self.head_of[b] {
                if self.entry_order[self.head_of[a]] > self.entry_order[self.head_of[b]] {
                    a = self.par[self.head_of[a]];
                } else {
                    b = self.par[self.head_of[b]];
                }
            }
            if self.depth[a] < self.depth[b] {
                a
            } else {
                b
            }
        }
        pub fn edges_to_arrayranges(&self, mut a: usize, mut b: usize) -> Vec<(usize, usize)> {
            let mut ret = vec![];
            while self.head_of[a] != self.head_of[b] {
                if self.entry_order[self.head_of[a]] > self.entry_order[self.head_of[b]] {
                    ret.push((self.entry_order[self.head_of[a]], self.entry_order[a]));
                    a = self.par[self.head_of[a]];
                } else {
                    ret.push((self.entry_order[self.head_of[b]], self.entry_order[b]));
                    b = self.par[self.head_of[b]];
                }
            }
            match self.depth[a].cmp(&self.depth[b]) {
                std::cmp::Ordering::Less => {
                    ret.push((self.entry_order[self.g[a][0]], self.entry_order[b]));
                }
                std::cmp::Ordering::Greater => {
                    ret.push((self.entry_order[self.g[b][0]], self.entry_order[a]));
                }
                _ => {}
            }
            ret
        }
        pub fn nodes_to_arrayranges(&self, a: usize, b: usize) -> Vec<(usize, usize)> {
            let mut ret = self.edges_to_arrayranges(a, b);
            let l = self.lca(a, b);
            ret.push((self.entry_order[l], self.entry_order[l]));
            ret
        }
        pub fn subnodes_to_arrayrange(&self, subroot: usize) -> (usize, usize) {
            (self.entry_order[subroot], self.leave_order[subroot])
        }
    }
}
use heavy_light_decomposition::Hld;

// construct XOR basis.
// Some XOR combination of these can make every element of the array.
// When msb of a[i] is b-th, b-th bit of all the other element is zero.
fn xor_basis(a: &[usize]) -> Vec<usize> {
    let mut basis: Vec<usize> = vec![];
    for mut a in a.iter().copied() {
        for &base in basis.iter() {
            a.chmin(a ^ base);
        }
        for base in basis.iter_mut() {
            base.chmin(a ^ *base);
        }
        if a > 0 {
            basis.push(a);
        }
    }
    basis.sort();
    basis
}

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

mod pair {
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    pub struct Pair<TA, TB> {
        a: TA,
        b: TB,
    }
    impl<TA: Clone + Copy, TB: Clone + Copy> Pair<TA, TB> {
        pub fn from(a: TA, b: TB) -> Self {
            Self { a, b }
        }
    }
    impl<TA: AddAssign, TB: AddAssign> AddAssign for Pair<TA, TB> {
        fn add_assign(&mut self, rhs: Self) {
            self.a += rhs.a;
            self.b += rhs.b;
        }
    }
    impl<TA: Add<Output = TA>, TB: Add<Output = TB>> Add for Pair<TA, TB> {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            Self {
                a: self.a + rhs.a,
                b: self.b + rhs.b,
            }
        }
    }
    impl<TA: SubAssign, TB: SubAssign> SubAssign for Pair<TA, TB> {
        fn sub_assign(&mut self, rhs: Self) {
            self.a -= rhs.a;
            self.b -= rhs.b;
        }
    }
    impl<TA: Sub<Output = TA>, TB: Sub<Output = TB>> Sub for Pair<TA, TB> {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            Self {
                a: self.a - rhs.a,
                b: self.b - rhs.b,
            }
        }
    }
    impl<TA: Neg<Output = TA>, TB: Neg<Output = TB>> Neg for Pair<TA, TB> {
        type Output = Self;
        fn neg(self) -> Self::Output {
            Self {
                a: -self.a,
                b: -self.b,
            }
        }
    }
    impl<T: Clone + Copy, TA: MulAssign<T> + Clone + Copy, TB: MulAssign<T> + Clone + Copy>
        MulAssign<T> for Pair<TA, TB>
    {
        fn mul_assign(&mut self, rhs: T) {
            self.a *= rhs;
            self.b *= rhs;
        }
    }
    impl<
            T: Clone + Copy,
            TA: Mul<T, Output = TA> + Clone + Copy,
            TB: Mul<T, Output = TB> + Clone + Copy,
        > Mul<T> for Pair<TA, TB>
    {
        type Output = Self;
        fn mul(self, rhs: T) -> Self::Output {
            Self {
                a: self.a * rhs,
                b: self.b * rhs,
            }
        }
    }
    impl<T: Clone + Copy, TA: DivAssign<T> + Clone + Copy, TB: DivAssign<T> + Clone + Copy>
        DivAssign<T> for Pair<TA, TB>
    {
        fn div_assign(&mut self, rhs: T) {
            self.a /= rhs;
            self.b /= rhs;
        }
    }
    impl<
            T: Clone + Copy,
            TA: Div<T, Output = TA> + Clone + Copy,
            TB: Div<T, Output = TB> + Clone + Copy,
        > Div<T> for Pair<TA, TB>
    {
        type Output = Self;
        fn div(self, rhs: T) -> Self::Output {
            Self {
                a: self.a / rhs,
                b: self.b / rhs,
            }
        }
    }
}
use pair::Pair;

mod deletable_binary_heap {
    use std::collections::BinaryHeap;
    #[derive(Clone)]
    pub struct DeletableBinaryHeap<T> {
        que: BinaryHeap<T>,
        del_rsv: BinaryHeap<T>,
    }
    impl<T: Clone + PartialOrd + Ord> DeletableBinaryHeap<T> {
        pub fn new() -> Self {
            Self {
                que: BinaryHeap::<T>::new(),
                del_rsv: BinaryHeap::<T>::new(),
            }
        }
        pub fn pop(&mut self) -> Option<T> {
            self.lazy_eval();
            self.que.pop()
        }
        pub fn push(&mut self, v: T) {
            self.lazy_eval();
            self.que.push(v)
        }
        pub fn peek(&mut self) -> Option<&T> {
            self.lazy_eval();
            self.que.peek()
        }
        pub fn remove(&mut self, del_v: &T) {
            self.del_rsv.push(del_v.clone());
            debug_assert!(self.que.iter().any(|v| v == del_v));
        }
        fn lazy_eval(&mut self) {
            while let Some(del_v) = self.del_rsv.peek() {
                if let Some(v) = self.que.peek() {
                    if del_v == v {
                        self.que.pop();
                        self.del_rsv.pop();
                    } else {
                        break;
                    }
                } else {
                    unreachable!()
                }
            }
        }
    }
}
use deletable_binary_heap::DeletableBinaryHeap;

mod point {
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    #[derive(Clone, Copy)]
    pub struct Point<T> {
        pub y: T,
        pub x: T,
    }
    impl<T: Clone> Point<T> {
        pub fn new(y: T, x: T) -> Self {
            Self { y, x }
        }
    }
    impl<T: Add<Output = T>> Add for Point<T> {
        type Output = Point<T>;
        fn add(self, rhs: Self) -> Self::Output {
            Self {
                y: self.y.add(rhs.y),
                x: self.x.add(rhs.x),
            }
        }
    }
    impl<T: AddAssign> AddAssign for Point<T> {
        fn add_assign(&mut self, rhs: Self) {
            self.y.add_assign(rhs.y);
            self.x.add_assign(rhs.x);
        }
    }
    impl<T: Sub<Output = T>> Sub for Point<T> {
        type Output = Point<T>;
        fn sub(self, rhs: Self) -> Self::Output {
            Self {
                y: self.y.sub(rhs.y),
                x: self.x.sub(rhs.x),
            }
        }
    }
    impl<T: SubAssign> SubAssign for Point<T> {
        fn sub_assign(&mut self, rhs: Self) {
            self.y.sub_assign(rhs.y);
            self.x.sub_assign(rhs.x);
        }
    }
    impl<T: Clone + Mul<Output = T>> Mul<T> for Point<T> {
        type Output = Self;
        fn mul(self, rhs: T) -> Self::Output {
            Self {
                y: self.y.mul(rhs.clone()),
                x: self.x.mul(rhs),
            }
        }
    }
    impl<T: Clone + Div<Output = T>> Div<T> for Point<T> {
        type Output = Self;
        fn div(self, rhs: T) -> Self::Output {
            Self {
                y: self.y.div(rhs.clone()),
                x: self.x.div(rhs),
            }
        }
    }
}

mod transpose {
    pub trait Transpose<T> {
        fn transpose(self) -> Vec<Vec<T>>;
    }
    impl<T: Clone> Transpose<T> for Vec<Vec<T>> {
        fn transpose(self) -> Vec<Vec<T>> {
            (0..self[0].len())
                .map(|x| {
                    (0..self.len())
                        .map(|y| self[y][x].clone())
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        }
    }
}
use transpose::Transpose;

mod wavelet_matrix {
    mod bit_vector {
        const W: usize = 64;
        const LOG_W: usize = 6;
        #[derive(Clone)]
        pub struct BitVector {
            bits: Vec<u64>,
            cum_ones: Vec<u32>,
            zero_num: usize,
        }
        impl BitVector {
            pub fn from_vec(a: &[u64], di: usize) -> Self {
                let ln = a.len() / W + 1;
                let mut bits = vec![0; ln];
                for (i, &a) in a.iter().enumerate() {
                    let d = i >> LOG_W;
                    let r = i & (W - 1);
                    bits[d] |= ((a >> di) & 1) << r;
                }
                let cum_ones = bits
                    .iter()
                    .map(|&bit| bit.count_ones())
                    .scan(0, |cum: &mut u32, x: u32| {
                        *cum += x;
                        Some(*cum)
                    })
                    .collect::<Vec<_>>();
                let zero_num = a.len() - cum_ones[ln - 1] as usize;
                Self {
                    bits,
                    cum_ones,
                    zero_num,
                }
            }
            // count 1 in 0..i
            #[inline(always)]
            pub fn rank1(&self, i: usize) -> usize {
                let d = i >> LOG_W;
                let r = i & (W - 1);
                (if d == 0 {
                    (self.bits[d] & ((1u64 << r) - 1)).count_ones()
                } else {
                    self.cum_ones[d - 1] + (self.bits[d] & ((1u64 << r) - 1)).count_ones()
                }) as usize
            }
            #[inline(always)]
            pub fn zero_num(&self) -> usize {
                self.zero_num
            }
            // count 0 in 0..i
            #[inline(always)]
            pub fn rank0(&self, i: usize) -> usize {
                i - self.rank1(i)
            }
            #[inline(always)]
            pub fn get(&self, i: usize) -> bool {
                let d = i >> LOG_W;
                let r = i & (W - 1);
                (self.bits[d] >> r) & 1 != 0
            }
        }
        mod test {
            use super::super::super::XorShift64;
            use super::BitVector;
            use super::W;
            #[test]
            fn random_test() {
                let mut rand = XorShift64::new();
                const N: usize = W * 3;
                const D: usize = 10;
                for n in 1..W * 5 {
                    let a = (0..n)
                        .map(|_| rand.next_u64() % (1u64 << D))
                        .collect::<Vec<_>>();
                    let bit_vectors = (0..D)
                        .map(|di| BitVector::from_vec(&a, di))
                        .collect::<Vec<_>>();
                    let mut rank0 = vec![0; D];
                    let mut rank1 = vec![0; D];
                    for i in 0..n {
                        for di in 0..D {
                            if ((a[i] >> di) & 1) != 0 {
                                rank1[di] += 1;
                            } else {
                                rank0[di] += 1;
                            }
                            assert_eq!(((a[i] >> di) & 1) != 0, bit_vectors[di].get(i));
                            assert_eq!(0, bit_vectors[di].rank0(0));
                            assert_eq!(0, bit_vectors[di].rank1(0));
                            assert_eq!(rank0[di], bit_vectors[di].rank0(i + 1));
                            assert_eq!(rank1[di], bit_vectors[di].rank1(i + 1));
                        }
                    }
                }
            }
        }
    }
    use bit_vector::BitVector;

    #[derive(Clone)]
    pub struct WaveletMatrix {
        bit_vectors: Vec<BitVector>,
    }
    impl WaveletMatrix {
        // construct. O(N * log(ValueMax))
        pub fn new(mut a: Vec<u64>) -> Self {
            let &mx = a.iter().max().unwrap();
            let mut d = 0;
            while mx & !((1u64 << d) - 1) != 0 {
                d += 1;
            }
            let mut bit_vectors = vec![];
            for di in (0..d).rev() {
                // calc
                let bit_vector = BitVector::from_vec(&a, di);
                // sort a
                a = a
                    .iter()
                    .filter(|&a| ((a >> di) & 1) == 0)
                    .copied()
                    .chain(a.iter().filter(|&a| ((a >> di) & 1) != 0).copied())
                    .collect::<Vec<_>>();
                // record
                bit_vectors.push(bit_vector);
            }
            bit_vectors.reverse();
            Self { bit_vectors }
        }
        // get a[i]. O(log(ValueMax))
        pub fn get(&self, mut i: usize) -> u64 {
            let mut val = 0;
            for (di, bit_vector) in self.bit_vectors.iter().enumerate().rev() {
                if bit_vector.get(i) {
                    val |= 1u64 << di;
                    i = bit_vector.zero_num() + bit_vector.rank1(i);
                } else {
                    i = bit_vector.rank0(i);
                }
            }
            val
        }
        // count value s.t. lower <= value < upper, in a[l..r]. O(log(ValueMax))
        pub fn range_freq(&self, lower: u64, upper: u64, l: usize, r: usize) -> usize {
            self.low_freq(upper, l, r) - self.low_freq(lower, l, r)
        }
        // count value s.t. value < upper, in a[l..r]. O(log(ValueMax))
        fn low_freq(&self, upper: u64, mut l: usize, mut r: usize) -> usize {
            if upper & !((1u64 << self.bit_vectors.len()) - 1) != 0 {
                return r - l;
            }
            let mut lows = 0;
            for (di, bit_vector) in self.bit_vectors.iter().enumerate().rev() {
                let c0_left = bit_vector.rank0(l);
                let c1_left = bit_vector.rank1(l);
                let c0_in = bit_vector.rank0(r) - c0_left;
                let c1_in = bit_vector.rank1(r) - c1_left;
                if ((upper >> di) & 1) == 0 {
                    // next0
                    l = c0_left;
                    r = c0_left + c0_in;
                } else {
                    lows += c0_in;
                    // next 1
                    let zero_num = bit_vector.zero_num();
                    l = zero_num + c1_left;
                    r = zero_num + c1_left + c1_in;
                }
                if l >= r {
                    break;
                }
            }
            lows
        }
        // get k-th smallest value in a[l..r]. O(log(ValueMax))
        fn range_kth_smallest(&self, mut l: usize, mut r: usize, mut k: usize) -> u64 {
            let mut val = 0;
            for (di, bit_vector) in self.bit_vectors.iter().enumerate().rev() {
                let c0_left = bit_vector.rank0(l);
                let c1_left = bit_vector.rank1(l);
                let c0_in = bit_vector.rank0(r) - c0_left;
                let c1_in = bit_vector.rank1(r) - c1_left;
                if c0_in > k {
                    // next0
                    l = c0_left;
                    r = c0_left + c0_in;
                } else {
                    // next 1
                    let zero_num = bit_vector.zero_num();
                    l = zero_num + c1_left;
                    r = zero_num + c1_left + c1_in;
                    k -= c0_in;
                    val |= 1u64 << di;
                }
                if l >= r {
                    break;
                }
            }
            val
        }
    }
    mod wavelet_matrix_test {
        use super::super::*;
        use super::*;
        const T: usize = 300;
        const N: usize = 30;
        const UPPER: u64 = 30;
        #[test]
        fn get() {
            let mut r = XorShift64::new();
            for _ in 0..T {
                let a = (0..N)
                    .map(|_| r.next_usize() as u64 % UPPER)
                    .collect::<Vec<_>>();
                let wm = WaveletMatrix::new(a.clone());
                for (i, a) in a.into_iter().enumerate() {
                    let chk = wm.get(i);
                    assert_eq!(a, chk);
                }
            }
        }
        #[test]
        fn low_freq() {
            let mut r = XorShift64::new();
            for _ in 0..T {
                let a = (0..N)
                    .map(|_| r.next_usize() as u64 % UPPER)
                    .collect::<Vec<_>>();
                let wm = WaveletMatrix::new(a.clone());
                for l in 0..N {
                    for r in l..=N {
                        for upper in 0..=UPPER {
                            let exp = (l..r).map(|i| a[i]).filter(|&a| a < upper).count();
                            let act = wm.low_freq(upper, l, r);
                            assert_eq!(act, exp);
                        }
                    }
                }
            }
        }
        #[test]
        fn range_freq() {
            let mut r = XorShift64::new();
            for _ in 0..T {
                let a = (0..N)
                    .map(|_| r.next_usize() as u64 % UPPER)
                    .collect::<Vec<_>>();
                let wm = WaveletMatrix::new(a.clone());
                for l in 0..N {
                    for r in l..N {
                        for lower in 0..UPPER {
                            for upper in lower..=UPPER {
                                let exp = (l..r)
                                    .map(|i| a[i])
                                    .filter(|&a| lower <= a && a < upper)
                                    .count();
                                let act = wm.range_freq(lower, upper, l, r);
                                assert_eq!(act, exp);
                            }
                        }
                    }
                }
            }
        }
        #[test]
        fn range_kth_smallest() {
            let mut r = XorShift64::new();
            for _ in 0..T {
                let a = (0..N)
                    .map(|_| r.next_usize() as u64 % UPPER)
                    .collect::<Vec<_>>();
                let wm = WaveletMatrix::new(a.clone());
                for l in 0..N {
                    for r in l..=N {
                        let mut sub = (l..r).map(|i| a[i]).collect::<Vec<_>>();
                        sub.sort();
                        for (k, exp) in sub.into_iter().enumerate() {
                            let act = wm.range_kth_smallest(l, r, k);
                            assert_eq!(act, exp);
                        }
                    }
                }
            }
        }
    }

    #[derive(Clone)]
    pub struct WaveletMatrix2D {
        h: usize,
        w: usize,
        pos_vectors: Vec<WaveletMatrix>,
    }
    impl WaveletMatrix2D {
        pub fn new(a: Vec<Vec<u64>>) -> Self {
            let h = a.len();
            let w = a[0].len();
            let &mx = a.iter().map(|org| org.iter().max().unwrap()).max().unwrap();
            let mut d = 0;
            while mx & !((1u64 << d) - 1) != 0 {
                d += 1;
            }
            let mut xa = vec![];
            for a in a {
                for (x1, val) in a.into_iter().enumerate() {
                    xa.push((x1, val));
                }
            }
            let mut pos_vectors = vec![];
            for di in (0..d).rev() {
                // calc
                let wm1 = WaveletMatrix::new(
                    xa.iter()
                        .map(|&(x, a)| if ((a >> di) & 1) == 0 { x } else { w } as u64)
                        .collect::<Vec<_>>(),
                );
                // sort a
                xa = xa
                    .iter()
                    .filter(|(_x, a)| ((a >> di) & 1) == 0)
                    .copied()
                    .chain(xa.iter().filter(|(_x, a)| ((a >> di) & 1) != 0).copied())
                    .collect::<Vec<_>>();
                // record
                pos_vectors.push(wm1);
            }
            pos_vectors.reverse();
            Self { h, w, pos_vectors }
        }
        // get k-th smallest value in a[y0..y1][x0..x1]. O(log(ValueMax) * log(W))
        fn range_kth_smallest(
            &self,
            y0: usize,
            y1: usize,
            x0: usize,
            x1: usize,
            mut k: usize,
        ) -> u64 {
            let mut val = 0;
            let mut l = y0 * self.w;
            let mut r = y1 * self.w;
            for (di, pos_vector) in self.pos_vectors.iter().enumerate().rev() {
                let c0_left = pos_vector.range_freq(0, self.w as u64, 0, l);
                let c0val_left = pos_vector.range_freq(x0 as u64, x1 as u64, 0, l);
                let c1_left = l - c0_left;
                debug_assert!(c0val_left <= c0_left);
                let c0_in = pos_vector.range_freq(0, self.w as u64, l, r);
                let c0val_in = pos_vector.range_freq(x0 as u64, x1 as u64, l, r);
                debug_assert!(c0val_in <= c0_in);
                let c1_in = (r - l) - c0_in;
                if c0val_in > k {
                    // next0
                    l = c0_left;
                    r = c0_left + c0_in;
                } else {
                    // next 1
                    k -= c0val_in;
                    let zero_num = pos_vector.range_freq(0, self.w as u64, 0, self.h * self.w);
                    l = zero_num + c1_left;
                    r = zero_num + c1_left + c1_in;
                    val |= 1u64 << di;
                }
                if l >= r {
                    break;
                }
            }
            val
        }
        // count value s.t. lower <= value < upper, in a[y0..y1][x0..x1]. O(log(ValueMax) * log(W))
        fn range_freq(
            &self,
            y0: usize,
            y1: usize,
            x0: usize,
            x1: usize,
            lower: u64,
            upper: u64,
        ) -> usize {
            self.low_freq(y0, y1, x0, x1, upper) - self.low_freq(y0, y1, x0, x1, lower)
        }
        // count value s.t. value < upper, in a[y0..y1][x0..x1]. O(log(ValueMax) * log(W))
        fn low_freq(&self, y0: usize, y1: usize, x0: usize, x1: usize, upper: u64) -> usize {
            if upper & !((1u64 << self.pos_vectors.len()) - 1) != 0 {
                return (y1 - y0) * (x1 - x0);
            }
            let area = self.h * self.w;
            let mut cnt = 0;
            let mut l = y0 * self.w;
            let mut r = y1 * self.w;
            for (di, pos_vector) in self.pos_vectors.iter().enumerate().rev() {
                let c0_left = pos_vector.range_freq(0, self.w as u64, 0, l);
                let c1_left = l - c0_left;
                let c0_in = pos_vector.range_freq(0, self.w as u64, l, r);
                let c0val_in = pos_vector.range_freq(x0 as u64, x1 as u64, l, r);
                debug_assert!(c0val_in <= c0_in);
                let c1_in = (r - l) - c0_in;
                if ((upper >> di) & 1) == 0 {
                    // next0
                    l = c0_left;
                    r = c0_left + c0_in;
                } else {
                    cnt += c0val_in;
                    // next 1
                    let zero_num = pos_vector.range_freq(0, self.w as u64, 0, area);
                    l = zero_num + c1_left;
                    r = zero_num + c1_left + c1_in;
                }
                if l >= r {
                    break;
                }
            }
            cnt
        }
    }
    mod wavelet_matrix_2d_test {
        use super::super::XorShift64;
        use super::WaveletMatrix2D;
        const HMAX: usize = 8;
        const WMAX: usize = 8;
        const UPPER: u64 = 8;
        #[test]
        fn range_kth_smallest() {
            let mut r = XorShift64::new();
            for h in 1..=HMAX {
                for w in 1..=WMAX {
                    let a = (0..h)
                        .map(|_| {
                            (0..w)
                                .map(|_| r.next_usize() as u64 % UPPER)
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    let wm = WaveletMatrix2D::new(a.clone());
                    for y0 in 0..h {
                        for y1 in y0..=h {
                            for x0 in 0..w {
                                for x1 in x0..=w {
                                    let mut v = vec![];
                                    for y in y0..y1 {
                                        for x in x0..x1 {
                                            v.push(a[y][x]);
                                        }
                                    }
                                    v.sort();
                                    for (k, expected) in v.into_iter().enumerate() {
                                        let actual = wm.range_kth_smallest(y0, y1, x0, x1, k);
                                        assert_eq!(expected, actual);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        #[test]
        fn range_freq() {
            let mut r = XorShift64::new();
            for h in 1..=HMAX {
                for w in 1..=WMAX {
                    let a = (0..h)
                        .map(|_| {
                            (0..w)
                                .map(|_| r.next_usize() as u64 % UPPER)
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    let wm = WaveletMatrix2D::new(a.clone());
                    for y0 in 0..h {
                        for y1 in y0..=h {
                            for x0 in 0..w {
                                for x1 in x0..=w {
                                    let mut seg = super::super::SegmentTree::<usize>::new(
                                        UPPER as usize,
                                        |x, y| x + y,
                                        0,
                                    );
                                    for y in y0..y1 {
                                        for x in x0..x1 {
                                            seg.add(a[y][x] as usize, 1);
                                        }
                                    }
                                    for lower in 0..UPPER {
                                        for upper in lower..=UPPER {
                                            let low_expected = if upper == 0 {
                                                0
                                            } else {
                                                seg.query(0, upper as usize - 1)
                                            };
                                            let low_actual = wm.low_freq(y0, y1, x0, x1, upper);
                                            assert_eq!(low_actual, low_expected);
                                            let range_expected = if lower == upper {
                                                0
                                            } else {
                                                seg.query(lower as usize, upper as usize - 1)
                                            };
                                            let range_actual =
                                                wm.range_freq(y0, y1, x0, x1, lower, upper);
                                            assert_eq!(range_actual, range_expected);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
use wavelet_matrix::WaveletMatrix;

mod aho_corasick {
    use std::cmp::Eq;
    use std::collections::{HashMap, VecDeque};
    use std::hash::Hash;
    #[derive(Clone, Debug)]
    pub struct AhoCoarsick<T> {
        trie: Vec<HashMap<T, usize>>,
        hit_keyword_num: Vec<usize>,
        failure: Vec<usize>,
    }
    impl<T: Eq + Hash + Copy> AhoCoarsick<T> {
        pub fn new(keywords: Vec<Vec<T>>) -> Self {
            let (trie, mut hit_keyword_num) = {
                let mut trie = vec![HashMap::new()];
                let mut hit_keyword_num = vec![0];
                for keyword in keywords.into_iter() {
                    let mut v = 0;
                    for val in keyword {
                        let nv = if let Some(&nv) = trie[v].get(&val) {
                            nv
                        } else {
                            let nv = trie.len();
                            trie.push(HashMap::new());
                            hit_keyword_num.push(0);
                            trie[v].insert(val, nv);
                            nv
                        };
                        v = nv;
                    }
                    hit_keyword_num[v] += 1;
                }
                (trie, hit_keyword_num)
            };
            let failure = {
                let mut failure = vec![0; trie.len()];
                let mut que = VecDeque::new();
                for (_c, &nv) in trie[0].iter() {
                    que.push_back(nv);
                }
                while let Some(v) = que.pop_front() {
                    for (&c, &nv) in trie[v].iter() {
                        failure[nv] = Self::next_impl(&trie, &failure, failure[v], c);
                        hit_keyword_num[nv] += hit_keyword_num[failure[nv]];
                        que.push_back(nv);
                    }
                }
                failure
            };
            Self {
                trie,
                hit_keyword_num,
                failure,
            }
        }
        pub fn next(&self, from: usize, c: T) -> usize {
            Self::next_impl(&self.trie, &self.failure, from, c)
        }
        fn next_impl(trie: &[HashMap<T, usize>], failure: &[usize], from: usize, c: T) -> usize {
            let mut now = from;
            loop {
                if let Some(&to) = trie[now].get(&c) {
                    // trie has next node.
                    return to;
                } else if now != failure[now] {
                    // proceed failure
                    // retry from failure-link.
                    now = failure[now];
                } else {
                    // proceed failure at root.
                    debug_assert!(now == 0);
                    return 0;
                }
            }
        }
        // count num of keyword, that end at this node.
        pub fn hit_keyword_num(&self, node: usize) -> usize {
            self.hit_keyword_num[node]
        }
    }
    pub mod test {
        use super::super::XorShift64;
        use super::AhoCoarsick;
        #[test]
        pub fn random() {
            let mut rand = XorShift64::new();
            const NMAX: usize = 50;
            const C: usize = 10;
            const K: usize = NMAX;
            const T: usize = 1000;
            for n in 1..=NMAX {
                for _ in 0..T {
                    let s = (0..n).map(|_| rand.next_usize() % C).collect::<Vec<_>>();
                    let keywords = (0..K)
                        .map(|_| {
                            let keyword_len = 1 + rand.next_usize() % n;
                            (0..keyword_len)
                                .map(|_| rand.next_usize() % C)
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    let ac = AhoCoarsick::new(keywords.clone());
                    let mut v = 0;
                    for (i, &c) in s.iter().enumerate() {
                        let expected_hit_num = keywords
                            .iter()
                            .filter(|keyword| {
                                if i < keyword.len() - 1 {
                                    false
                                } else {
                                    &&s[i - (keyword.len() - 1)..=i] == keyword
                                }
                            })
                            .count();
                        v = ac.next(v, c);
                        let actual_hit_num = ac.hit_keyword_num(v);
                        assert_eq!(expected_hit_num, actual_hit_num);
                    }
                }
            }
        }
    }
}
use aho_corasick::AhoCoarsick;

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
                const MX: usize = 100;
                let tot = 1usize << (2 * len);
                let points = (0..(1 << (2 * len)))
                    .step_by(max(1, tot / MX))
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
            pub fn best_split(n: usize, m: usize, v: usize) -> Vec<usize> {
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
                let p = 0.5 * (m as f64 / (n * n) as f64);
                let q = 1.0 - p;
                let used = v - 1;
                let ex = (0..=used)
                    .map(|now| 1.0 - power(q, 4u64.pow(now as u32)))
                    .collect_vec();
                let mut best_eval = None;
                let mut best_bit = 0;
                for bit in 0..(1 << (used - 1)) {
                    let mut eval = 0.0;
                    let mut now = 0;
                    for i in 0..(used - 1) {
                        now += 1;
                        if ((bit >> i) & 1) != 0 {
                            eval += ex[now];
                            now = 0;
                        }
                    }
                    {
                        now += 1;
                        eval += ex[now];
                    }
                    if best_eval.chmax(eval) {
                        best_bit = bit;
                    }
                }
                assert!(best_eval.is_some());
                let best_bit = best_bit;
                let mut ret = vec![];
                let mut now = 0;
                for i in 0..(used - 1) {
                    now += 1;
                    if ((best_bit >> i) & 1) != 0 {
                        ret.push(now);
                        now = 0;
                    }
                }
                {
                    now += 1;
                    ret.push(now);
                }
                ret
            }
        }
    }
    use arm_shape::ArmShape;
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
        fn gen_tree_shape(&self) -> Vec<Vec<usize>> {
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
            let p = 0.5 * (self.m as f64 / (self.n * self.n) as f64);
            let q = 1.0 - p;
            let ex = (0..self.v)
                .map(|depth| 1.0 - power(q, 4u64.pow(depth as u32)))
                .collect_vec();
            let mut rand = XorShift64::new();
            let mut best_g = vec![];
            let mut best_eval = None;
            //while self.t0.elapsed().as_millis() < 750 {
            for li in 0..100 {
                let mut g = vec![vec![]; self.v];
                let mut d = vec![0; self.v];
                for i in 1..self.v {
                    let pi = rand.next_usize() % i;
                    g[pi].push(i);
                    d[i] = d[pi] + 1;
                }
                let mut eval = 0.0;
                for i in 1..self.v {
                    if !g[i].is_empty() {
                        continue;
                    }
                    eval += ex[d[i]];
                }
                if best_eval.chmax(eval) {
                    best_g = g;
                }
            }
            best_g
        }
        fn gen_tree(&self) -> Vec<Vec<(usize, i32)>> {
            let g = self.gen_tree_shape();
            let nv0s = g[0].clone();
            fn get_depth(v0: usize, d0: usize, g: &[Vec<(usize, i32)>]) -> usize {
                let mut ret = d0;
                let d1 = d0 + 1;
                for (nv, _) in g[v0].iter() {
                    ret.chmax(get_depth(*nv, d1, g));
                }
                ret
            }
            let mut g = g
                .into_iter()
                .map(|g| g.into_iter().map(|v| (v, 1)).collect_vec())
                .collect_vec();
            for nv0 in nv0s {
                let depth = get_depth(nv0, 1, &g);
                let ln = max(1, self.n / (2 * depth)) as i32;
                g[0].iter_mut().for_each(|(v, d)| {
                    if *v == nv0 {
                        *d = ln;
                    }
                });
                let mut que = vec![nv0];
                while let Some(v0) = que.pop() {
                    g[v0].iter_mut().for_each(|(_, d)| {
                        *d = ln;
                    });
                    for (v1, _) in g[v0].iter() {
                        que.push(*v1);
                    }
                }
            }
            g
        }
        fn gen_arm_shapes(&self) -> (Vec<ArmShape>, usize) {
            /*
            let mut ls = vec![];
            let mut used = 1;
            let mut max_sz = 0;
            for sz in 1.. {
                let nused = used + sz;
                if nused > self.v {
                    break;
                }
                used = nused;
                ls.push(vec![1; sz]);
                max_sz.chmax(sz);
            }
            let unit = self.n / max_sz;
            debug_assert!(unit <= self.n);
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
                while used < self.v {
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
            let mut g = vec![vec![]; self.v];
            let mut nxt = 0;
            for ls in ls {
                for (i, d) in ls.iter().copied().enumerate() {
                    let from = if i == 0 { 0 } else { nxt + i };
                    g[from].push((nxt + i + 1, d));
                }
                nxt += ls.len();
            }
             */
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
                        if (y0, x0, y1, x1) == (1, 1, 2, 1) {
                            eprintln!();
                        }
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
