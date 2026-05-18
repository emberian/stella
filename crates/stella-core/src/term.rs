//! Hash-consed first-order terms over a polarised signature.
//!
//! Eng §B.1.2 defines a *signature* `S = (V, F, ar, ⊂)`.
//! §48.2 defines a *polarised signature* that partitions `F` into
//! `F₊ ⊎ F₋ ⊎ F₀` (positive, negative, neutral).
//!
//! ## Representation
//!
//! - **`Var`**: an interned variable name, stored as a `u32` key from a
//!   process-global `ThreadedRodeo`.  `Copy`, `Eq`, `Hash`.
//! - **`Sym`**: a function symbol with `name: SymName` (interned u32 key) and
//!   `pol: Polarity`.  `Copy`, `Eq`, `Hash`.
//! - **`TermId`**: a handle into the global hash-cons table.  `Copy`, `Eq`, `Hash`.
//!   Structural equality ≡ `TermId` equality.
//! - **`TermData`**: the actual node — either `Var(Var)` or `App(Sym, Arc<[TermId]>)`.
//!   The backing store is a process-global sharded hash-cons table
//!   ([`ShardedStore`]): dedup is `SHARDS` independent `RwLock<FxHashMap>`s
//!   routed by content hash; the `id → (TermData, ground)` read path is a
//!   pair of grow-only lock-free `boxcar::Vec`s (publish-after-init
//!   Release/Acquire ⇒ no torn read). See [`ShardedStore`] for the full
//!   invariant/soundness argument.
//!
//! ## Polarity (§48.2)
//!
//! | Prefix in source | `Polarity` variant |
//! |---|---|
//! | `+name` | `Pos` |
//! | `-name` | `Neg` |
//! | `name`  | `Neu` |
//!
//! `parse_sym_str` reads the prefix ONCE at construction.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, LazyLock, RwLock};

use lasso::ThreadedRodeo;
use rustc_hash::{FxHashMap, FxHasher};

// ─────────────────────────────────────────────────────────────────────────────
// Interning stores (process-global, thread-safe)
// ─────────────────────────────────────────────────────────────────────────────

static VAR_INTERNER: LazyLock<ThreadedRodeo> = LazyLock::new(ThreadedRodeo::default);
static SYM_INTERNER: LazyLock<ThreadedRodeo> = LazyLock::new(ThreadedRodeo::default);

// ─────────────────────────────────────────────────────────────────────────────
// Polarity (§48.2)
// ─────────────────────────────────────────────────────────────────────────────

/// The polarity of a function symbol in a polarised signature (§48.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Polarity {
    /// Positive `F₊` (prefix `+`).
    Pos,
    /// Negative `F₋` (prefix `−`).
    Neg,
    /// Neutral / uncoloured `F₀` (no prefix).
    Neutral,
}

// ─────────────────────────────────────────────────────────────────────────────
// Var — interned variable name
// ─────────────────────────────────────────────────────────────────────────────

/// A first-order (unification) variable (§B.1.2).
///
/// Two representations, both `Copy` with cheap `Eq`/`Hash`/`Ord`:
///
/// - **`Named(Spur)`** — an interned source name from the process-global
///   `ThreadedRodeo`.  Produced by the parser, by `Var::intern`, and by every
///   pre-existing call site.  The reference engine's *named* path is built out
///   of these and is left semantically intact.
/// - **`Idx(u32)`** — a *canonical-index* / generation variable.  Created by
///   freshening (`subst::freshen` / `interactive::alpha_rename_star`) as a
///   pure integer: a monotone generation `base` plus the variable's local
///   ordinal.  No `format!`, no global interner lock — the freshening of a Φ
///   star is `O(#distinct vars)` integer work and the per-step cost the
///   profiler attributed to `freshen`/`Var::intern` disappears.
///
/// `Idx` lives in a namespace disjoint from any `Named` var (different enum
/// variant ⇒ never equal), so a freshened copy is automatically
/// variable-disjoint from the Ψ it fuses against, exactly as the old
/// string-prefix scheme guaranteed — provided generation `base`s never repeat
/// (the role the old `counter` played, preserved).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Var {
    /// An interned source name (the original named path).
    Named(lasso::Spur),
    /// A canonical generation-index variable (cheap freshening).
    Idx(u32),
}

impl Var {
    /// Intern a variable name (always yields a [`Var::Named`]).
    pub fn intern(name: &str) -> Self {
        Var::Named(VAR_INTERNER.get_or_intern(name))
    }

    /// Construct a canonical-index variable directly (O(1), no interning).
    #[inline]
    pub fn idx(n: u32) -> Self {
        Var::Idx(n)
    }

    /// Retrieve the string for this variable.
    ///
    /// `Named` resolves from the interner in `O(1)`.  `Idx(n)` has no source
    /// name; it is lazily interned as `#n` *only when a string is demanded*
    /// (display, parsing round-trips, DOT export) — never on the engine hot
    /// path, which compares `Var`s by value.
    pub fn as_str(self) -> &'static str {
        match self {
            Var::Named(s) => VAR_INTERNER.resolve(&s),
            Var::Idx(n) => {
                let key = VAR_INTERNER.get_or_intern(format!("#{n}"));
                VAR_INTERNER.resolve(&key)
            }
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Var::Named(s) => write!(f, "{}", VAR_INTERNER.resolve(s)),
            Var::Idx(n) => write!(f, "#{n}"),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SymName — interned neutral name
// ─────────────────────────────────────────────────────────────────────────────

/// An interned neutral symbol name (the `|·|` underlying name, §48.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymName(pub lasso::Spur);

impl SymName {
    pub fn intern(name: &str) -> Self {
        SymName(SYM_INTERNER.get_or_intern(name))
    }
    pub fn as_str(self) -> &'static str {
        SYM_INTERNER.resolve(&self.0)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Sym — polarised function symbol (§48.2)
// ─────────────────────────────────────────────────────────────────────────────

/// A function symbol in a polarised signature (§48.2).
///
/// `Sym { name, pol }` represents:
/// - `pol=Pos` → the positive symbol `+|name|`
/// - `pol=Neg` → the negative symbol `−|name|`
/// - `pol=Neu` → the neutral symbol `|name|`
///
/// `Copy`; equality is `(name, pol)` equality (u32 + enum, no string compare).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sym {
    pub name: SymName,
    pub pol: Polarity,
}

impl Sym {
    pub fn new(name: SymName, pol: Polarity) -> Self {
        Self { name, pol }
    }

    /// Parse a symbol from a string literal: `"+foo"` → Pos, `"-foo"` → Neg, `"foo"` → Neu.
    pub fn parse(s: &str) -> Self {
        if let Some(rest) = s.strip_prefix('+') {
            Self { name: SymName::intern(rest), pol: Polarity::Pos }
        } else if let Some(rest) = s.strip_prefix('-') {
            Self { name: SymName::intern(rest), pol: Polarity::Neg }
        } else {
            Self { name: SymName::intern(s), pol: Polarity::Neutral }
        }
    }

    /// The displayed name string (e.g. `"+c"`, `"-d"`, `"f"`).
    pub fn display_name(self) -> String {
        match self.pol {
            Polarity::Pos => format!("+{}", self.name.as_str()),
            Polarity::Neg => format!("-{}", self.name.as_str()),
            Polarity::Neutral => self.name.as_str().to_string(),
        }
    }

    /// The *opposite* symbol `op(f)` (§48.3).
    pub fn opposite(self) -> Self {
        match self.pol {
            Polarity::Neutral => self,
            Polarity::Pos => Self { name: self.name, pol: Polarity::Neg },
            Polarity::Neg => Self { name: self.name, pol: Polarity::Pos },
        }
    }
}

impl fmt::Display for Sym {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TermData — unboxed node
// ─────────────────────────────────────────────────────────────────────────────

/// The structural content of a term node.
///
/// Stored in the global `TermStore`; keyed for interning by `FxHashMap<TermData, TermId>`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermData {
    /// A variable `X ∈ V` (§B.1.4).
    Var(Var),
    /// A function application `f(t₁, …, tₙ)` (§B.1.4).
    ///
    /// Args are `Arc<[TermId]>` (not `Box`): the append-only store is
    /// immutable per `TermId`, so `get` clones in `O(1)` (refcount bump, **no
    /// heap alloc**) instead of deep-copying a boxed slice on every node visit.
    /// `Arc<[_]>` hashes/eqs by content ⇒ hash-consing/interning unchanged.
    App(Sym, std::sync::Arc<[TermId]>),
}

// ─────────────────────────────────────────────────────────────────────────────
// TermId — hash-consed handle
// ─────────────────────────────────────────────────────────────────────────────

/// A handle to a hash-consed term (§B.1.4 — "hash-cons representation").
///
/// `Copy`; structural equality ≡ `TermId` equality (u32 equality).
/// Used throughout as the term type — NOT a parallel dead type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(pub u32);

/// Alias: `Term` IS `TermId`.  Every module that imported `Term` now gets `TermId`.
pub type Term = TermId;

// ─────────────────────────────────────────────────────────────────────────────
// TermStore — the hash-cons table
// ─────────────────────────────────────────────────────────────────────────────

/// Number of independent dedup shards. A `TermData` is routed to a fixed
/// shard by `hash(TermData) % SHARDS`, so the same content always lands in
/// the same shard ⇒ dedup stays exact while the per-shard `RwLock` spreads
/// what used to be one global lock across `SHARDS` independent locks. Power
/// of two so the route is a mask, not a `%`.
const SHARDS: usize = 64;

/// One interned node: its data plus its precomputed groundness bit. Kept
/// in a **single** `boxcar` slot (NOT two parallel boxcars) so that one
/// `push` atomically assigns one dense id to *both* fields — two separate
/// boxcars cannot be kept index-aligned without a shared critical section
/// across both pushes (concurrent pushes from different shards would
/// interleave their index assignments and desync data vs. ground).
struct Node {
    data: TermData,
    /// "is this term variable-free", computed once at intern time (O(1): a
    /// `Var` is non-ground; an `App` is ground iff every arg is — args are
    /// interned before their parent so their bit is already published).
    /// Lets `Substitution::apply` return a ground subterm in O(1) instead
    /// of re-walking it. Behaviour-identical.
    ground: bool,
}

/// Process-global hash-cons store, **#3-step-2 (perf-audit D-W3)**.
///
/// ## What changed vs. the single-`RwLock<TermStore>`
///
/// The old store serialised *every* `get` / `is_ground` / `mk`-hit behind
/// one `RwLock` (the profiler attributed the 73% wall↔kernel gap on galaxy
/// `[triple]` to exactly that lock + the hash-cons map under it). This
/// splits the store into two independently-synchronised concerns, each
/// chosen so reads never touch a writer lock:
///
/// 1. **`nodes` — the `id → Node{data, ground}` read path.** ONE grow-
///    only, append-only `boxcar::Vec<Node>` (a single slot carries *both*
///    the data and its ground bit — see [`Node`] for why this must be one
///    slot, not two parallel boxcars). `boxcar::push` writes the slot then
///    does a `Release` store on a per-entry `active` flag; `boxcar::get`
///    does an `Acquire` load and reads the slot **only if** `active`. That
///    Release/Acquire pair is a documented, loom-model-checked happens-
///    before: a reader either sees "not yet published" (`None`) or the
///    *fully-initialised* `Node` — **a torn read is impossible**.
///    `get`/`is_ground` take **no lock at all**.
///
/// 2. **`shards` — content dedup.** `SHARDS` independent
///    `RwLock<FxHashMap<TermData, TermId>>`. Hot path: a *shared* read
///    lock on one shard for the already-interned case. Cold path: that
///    one shard's write lock, double-checked.
///
/// ## Invariants preserved exactly
///
/// - **Append-only / immutable-per-id**: `nodes` only ever grows via
///   `push`; an entry is never removed or mutated. ✔ (boxcar is grow-
///   only; we never call any mutating op.)
/// - **`TermId` = dense `u32` insertion index, stable & bit-for-bit
///   identical to today for every single-threaded program** (every gate
///   test, the galaxy descent are single-threaded). The dedup lookup
///   short-circuits *before* any `push`, so an already-interned
///   `TermData` never advances the index; with one thread the push
///   sequence is exactly the old `vec.len()` sequence. Concurrency only
///   reorders the *first* intern of *distinct* `TermData` across threads
///   — IDs stay dense (boxcar hands out distinct dense indices) and
///   content-deduped (same `TermData` ⇒ same shard ⇒ double-checked
///   ⇒ one canonical id).
/// - **`get(id) = nodes[id].data`, `is_ground(id) = nodes[id].ground`** —
///   unchanged in meaning; one slot ⇒ they can never disagree about which
///   id they describe.
/// - **child bits set before parent**: callers build bottom-up (`mk_app`
///   args are already `TermId`s ⇒ already pushed), and we **push the full
///   `Node` before publishing the id into the shard map**, so any thread
///   that discovers an id via the map is guaranteed by boxcar's Release/
///   Acquire to observe the fully-written node *and* its ground bit.
///
/// ## The publish-after-init ordering (the soundness keystone)
///
/// In `intern_cold` the order is, strictly: (a) compute `is_ground` from
/// already-published args (each arg's `Node` is visible because we hold
/// its `TermId`, which `mk` only returns after the slot was pushed);
/// (b) `nodes.push(Node{data, ground})` → dense index `i`, ONE atomic
/// push (so data and ground share one id — concurrent pushes from other
/// shards cannot desync them); (c) **only then**
/// `shard.insert(data, TermId(i))`. A reader reaches `get(id)`/
/// `is_ground(id)` only with an `id` it already holds — ids are handed out
/// solely as the return of `mk`, which returns either a map hit (⇒ insert
/// at (c) already happened ⇒ (b) happened-before it by program order
/// + the shard lock release/acquire) or the freshly-pushed id (⇒ this
/// thread did (b)). Either way the boxcar slot for that id is fully
/// initialised before any `get`. No `unsafe` in this module; the only
/// unsafe is inside boxcar, behind its proven Release/Acquire contract.
struct ShardedStore {
    /// `nodes[id]` — the term data + ground bit, one atomic slot per id.
    /// Grow-only, lock-free reads.
    nodes: boxcar::Vec<Node>,
    /// Dedup, sharded by `hash(TermData) & (SHARDS-1)`.
    shards: [RwLock<FxHashMap<TermData, TermId>>; SHARDS],
}

impl ShardedStore {
    fn new() -> Self {
        // #3-step-1 pre-sizing is preserved as a per-shard reserve: the old
        // single map pre-sized to 64Ki; spread across SHARDS that is
        // 64Ki/SHARDS per shard (same total, kills the early reserve_rehash
        // burst). boxcar grows in geometric buckets internally — no reserve
        // needed and no rehash concept.
        const PER_SHARD_CAP: usize = (1 << 16) / SHARDS;
        Self {
            nodes: boxcar::Vec::new(),
            shards: std::array::from_fn(|_| {
                RwLock::new(FxHashMap::with_capacity_and_hasher(
                    PER_SHARD_CAP,
                    Default::default(),
                ))
            }),
        }
    }

    #[inline]
    fn shard_idx(data: &TermData) -> usize {
        // FxHasher is the same family used for the map itself; any stable
        // hash works since routing only needs "same content ⇒ same shard".
        let mut h = FxHasher::default();
        data.hash(&mut h);
        (h.finish() as usize) & (SHARDS - 1)
    }

    fn intern(&self, data: TermData) -> TermId {
        let si = Self::shard_idx(&data);
        // Hot path: shared read lock on this one shard.
        if let Some(&id) = self.shards[si].read().unwrap().get(&data) {
            return id;
        }
        self.intern_cold(si, data)
    }

    #[cold]
    fn intern_cold(&self, si: usize, data: TermData) -> TermId {
        let mut shard = self.shards[si].write().unwrap();
        // Double-check: another thread may have interned this content
        // between our read-unlock and write-lock. Same content ⇒ same
        // shard, so this check is authoritative for dedup.
        if let Some(&id) = shard.get(&data) {
            return id;
        }
        // Compute groundness from already-published args. Args were
        // interned (pushed) before this parent — their slot (incl. the
        // ground bit) is visible (boxcar Acquire) because we hold their
        // TermId, which is only ever produced after its slot was pushed.
        let is_ground = match &data {
            TermData::Var(_) => false,
            TermData::App(_, args) => args.iter().all(|a| {
                self.nodes
                    .get(a.0 as usize)
                    .expect("arg TermId must already be published")
                    .ground
            }),
        };
        // Publish-after-init, strict order: ONE atomic push of the full
        // node (data + ground) FIRST — boxcar::push returns the dense index
        // and Release-publishes the slot — THEN expose the id via the shard
        // map. A single push ⇒ data and ground share one id, no desync
        // possible even under concurrent pushes from other shards.
        let i = self.nodes.push(Node { data: data.clone(), ground: is_ground });
        let id = TermId(i as u32);
        shard.insert(data, id);
        id
    }

    #[inline]
    fn get(&self, id: TermId) -> &TermData {
        // Lock-free Acquire read. The id is only ever produced by `intern`,
        // which pushed this slot before returning it (or before exposing it
        // via the map), so `active` is set ⇒ `Some`.
        &self
            .nodes
            .get(id.0 as usize)
            .expect("TermId must index a published node (intern publishes before returning the id)")
            .data
    }

    #[inline]
    fn is_ground(&self, id: TermId) -> bool {
        self.nodes
            .get(id.0 as usize)
            .expect("TermId must index a published node")
            .ground
    }
}

static TERM_STORE: LazyLock<ShardedStore> = LazyLock::new(ShardedStore::new);

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// Intern a `TermData` into the global store and return its `TermId`.
///
/// Hot path takes only a *shared* read lock on the single shard the
/// content routes to (the already-interned case — the read-heavy engine
/// loops); cold path takes that one shard's write lock. No global lock.
pub fn mk(data: TermData) -> TermId {
    TERM_STORE.intern(data)
}

/// Retrieve the `TermData` for a `TermId`.
///
/// **Lock-free** Acquire read + `O(1)` clone (App args are `Arc` —
/// refcount bump, no heap alloc). The store is append-only so the entry is
/// immutable; the id was published after its slot was fully written
/// (boxcar Release/Acquire), so this never observes a torn entry.
pub fn get(id: TermId) -> TermData {
    TERM_STORE.get(id).clone()
}

/// `true` iff `id` is variable-free (cached per node at intern time, O(1),
/// **lock-free** Acquire read). A substitution applied to a ground term is
/// the identity, so callers may short-circuit on this without changing any
/// result.
pub fn is_ground(id: TermId) -> bool {
    TERM_STORE.is_ground(id)
}

/// Construct a variable term.
pub fn mk_var(name: &str) -> TermId {
    mk(TermData::Var(Var::intern(name)))
}

/// Construct a variable term from an interned `Var`.
pub fn mk_var_interned(v: Var) -> TermId {
    mk(TermData::Var(v))
}

/// Construct a function application term.
pub fn mk_app(sym: Sym, args: Vec<TermId>) -> TermId {
    mk(TermData::App(sym, Arc::from(args)))
}

/// Convenience: a zero-arity (constant) application with a parsed symbol name.
pub fn mk_const(name: &str) -> TermId {
    mk_app(Sym::parse(name), vec![])
}

/// Convenience: construct from a `&str` head and args — used in call sites
/// that used to write `Term::App("name".into(), args)`.
pub fn mk_app_str(head: &str, args: Vec<TermId>) -> TermId {
    mk_app(Sym::parse(head), args)
}

/// Construct from an already-interned `Sym` and args (used by `subst.rs` apply).
pub fn mk_app_interned(sym: Sym, args: Vec<TermId>) -> TermId {
    mk(TermData::App(sym, Arc::from(args)))
}

// ─────────────────────────────────────────────────────────────────────────────
// TermId methods
// ─────────────────────────────────────────────────────────────────────────────

impl TermId {
    /// Convenience constructor for a variable.
    pub fn var(name: impl AsRef<str>) -> Self {
        mk_var(name.as_ref())
    }

    /// Convenience constructor for a constant (zero-arity App).
    pub fn constant(name: impl AsRef<str>) -> Self {
        mk_const(name.as_ref())
    }

    /// Returns `true` iff this term is a variable.
    pub fn is_var(self) -> bool {
        matches!(get(self), TermData::Var(_))
    }

    /// The set of variables appearing in this term.
    pub fn vars(self) -> rustc_hash::FxHashSet<Var> {
        fn collect(id: TermId, acc: &mut rustc_hash::FxHashSet<Var>) {
            match get(id) {
                TermData::Var(v) => { acc.insert(v); }
                TermData::App(_, args) => {
                    for a in args.iter() {
                        collect(*a, acc);
                    }
                }
            }
        }
        let mut s = rustc_hash::FxHashSet::default();
        collect(self, &mut s);
        s
    }

    /// The head function symbol `Sym`, if this term is an application.
    pub fn head_sym(self) -> Option<Sym> {
        match get(self) {
            TermData::App(sym, _) => Some(sym),
            TermData::Var(_) => None,
        }
    }

    /// Head as a display string (e.g. `"+add"`, `"f"`).  Used by call sites
    /// that used to call `term.head()` returning `Option<&str>`.
    pub fn head(self) -> Option<String> {
        self.head_sym().map(|s| s.display_name())
    }

    /// The arity: 0 for variables, `args.len()` for applications.
    pub fn arity(self) -> usize {
        match get(self) {
            TermData::Var(_) => 0,
            TermData::App(_, args) => args.len(),
        }
    }

    /// Access arguments (cloned).
    pub fn args(self) -> Vec<TermId> {
        match get(self) {
            TermData::App(_, args) => args.to_vec(),
            TermData::Var(_) => vec![],
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Display
// ─────────────────────────────────────────────────────────────────────────────

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match get(*self) {
            TermData::Var(v) => write!(f, "{v}"),
            TermData::App(sym, args) if args.is_empty() => write!(f, "{sym}"),
            TermData::App(sym, args) => {
                write!(f, "{sym}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { write!(f, ",")?; }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// #3-step-2 concurrency stress (perf-audit D-W3)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod concurrency_stress {
    use super::*;
    use std::collections::HashMap;
    use std::sync::{Arc, Barrier};
    use std::thread;

    /// Many threads concurrently `mk` a large set of *overlapping* (every
    /// thread builds the same shared terms) **and** *distinct* (per-thread
    /// private terms) `TermData`, while a fraction of threads hammer
    /// `get`/`is_ground` on ids handed back. Asserts:
    ///
    ///  - no panic / no torn read (every `get` round-trips structurally;
    ///    `is_ground` agrees with a recompute),
    ///  - dedup is exact across threads: the *same* `TermData` interned on
    ///    any thread yields the *same* `TermId`,
    ///  - ids are dense (every id in `0..count` resolves).
    #[test]
    fn sharded_store_is_race_free_and_dedup_exact() {
        const THREADS: usize = 16;
        const SHARED: usize = 400; // overlapping terms every thread interns
        const PRIVATE: usize = 300; // per-thread distinct terms

        let barrier = Arc::new(Barrier::new(THREADS));

        // Build a deterministic set of shared TermData specs (constants,
        // unary, and binary apps over a small alphabet) so every thread
        // interns *byte-identical* content ⇒ must collapse to one id each.
        let shared_specs: Arc<Vec<TermData>> = Arc::new(
            (0..SHARED)
                .map(|i| {
                    let leaf = TermData::App(Sym::parse(&format!("+c{}", i % 7)), Arc::from(vec![]));
                    if i % 3 == 0 {
                        leaf
                    } else {
                        // nest so groundness must propagate through args
                        let l = mk(leaf);
                        let v = mk(TermData::Var(Var::idx(i as u32)));
                        TermData::App(
                            Sym::parse(&format!("f{}", i % 5)),
                            Arc::from(if i % 2 == 0 { vec![l, l] } else { vec![l, v] }),
                        )
                    }
                })
                .collect(),
        );

        let handles: Vec<_> = (0..THREADS)
            .map(|tid| {
                let barrier = Arc::clone(&barrier);
                let shared_specs = Arc::clone(&shared_specs);
                thread::spawn(move || {
                    barrier.wait(); // maximise the race window

                    // 1. intern all shared specs; record the ids this thread saw
                    let mut shared_ids = Vec::with_capacity(SHARED);
                    for spec in shared_specs.iter() {
                        let id = mk(spec.clone());
                        // round-trip structural identity immediately (catch
                        // a torn read at the point it would corrupt)
                        assert_eq!(
                            &get(id),
                            spec,
                            "get(mk(d)) must structurally equal d (no torn read)"
                        );
                        // groundness must equal a fresh recompute
                        let recomputed = is_ground_recompute(&get(id));
                        assert_eq!(
                            is_ground(id),
                            recomputed,
                            "cached ground bit must equal recompute"
                        );
                        shared_ids.push((spec.clone(), id));
                    }

                    // 2. intern per-thread *distinct* content (forces real
                    //    concurrent pushes into the boxcars from many shards)
                    for k in 0..PRIVATE {
                        let d = TermData::App(
                            Sym::parse(&format!("priv{tid}")),
                            Arc::from(vec![mk(TermData::Var(Var::idx(
                                1_000_000 + (tid * PRIVATE + k) as u32,
                            )))]),
                        );
                        let id = mk(d.clone());
                        assert_eq!(&get(id), &d, "private get/round-trip");
                        // re-interning the same private content is idempotent
                        assert_eq!(mk(d.clone()), id, "re-intern must be the same id");
                    }

                    // 3. hammer reads on every shared id we collected
                    for (spec, id) in &shared_ids {
                        assert_eq!(&get(*id), spec, "concurrent get must not tear");
                        let _ = is_ground(*id);
                    }

                    shared_ids
                })
            })
            .collect();

        let per_thread: Vec<Vec<(TermData, TermId)>> =
            handles.into_iter().map(|h| h.join().unwrap()).collect();

        // Dedup-exactness across threads: for each shared spec, every thread
        // must have observed the SAME canonical TermId.
        let mut canonical: HashMap<TermData, TermId> = HashMap::new();
        for thread_ids in &per_thread {
            for (spec, id) in thread_ids {
                match canonical.get(spec) {
                    Some(c) => assert_eq!(
                        c, id,
                        "same TermData must map to same TermId across all threads (dedup exact)"
                    ),
                    None => {
                        canonical.insert(spec.clone(), *id);
                    }
                }
            }
        }

        // Density: every id in 0..max must resolve (no holes), and the
        // round-trip is still structurally sound post-hoc.
        let max_id = canonical.values().map(|t| t.0).max().unwrap_or(0);
        for raw in 0..=max_id {
            let id = TermId(raw);
            // must not panic; structural self-consistency: re-interning the
            // retrieved data yields the same id (hash-cons identity holds).
            let d = get(id);
            assert_eq!(mk(d.clone()), id, "dense id {raw} must hash-cons-identity");
            assert_eq!(is_ground(id), is_ground_recompute(&d));
        }
    }

    /// Independent groundness recompute (does NOT consult the cached bit) —
    /// a `Var` is non-ground; an `App` is ground iff all args are.
    fn is_ground_recompute(d: &TermData) -> bool {
        match d {
            TermData::Var(_) => false,
            TermData::App(_, args) => args.iter().all(|a| {
                let sub = get(*a);
                is_ground_recompute(&sub)
            }),
        }
    }
}
