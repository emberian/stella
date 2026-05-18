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
//! - **`TermData`**: the actual node — either `Var(Var)` or `App(Sym, Box<[TermId]>)`.
//!   The backing store is a `LazyLock<Mutex<TermStore>>` with a `FxHashMap` for
//!   interning and a `Vec` for index-based lookup.
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
use std::sync::{Arc, LazyLock, RwLock};

use lasso::{Key, ThreadedRodeo};
use rustc_hash::FxHashMap;

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

struct TermStore {
    map: FxHashMap<TermData, TermId>,
    vec: Vec<TermData>,
    /// Per-node "is this term variable-free", computed once at intern time
    /// (O(1): a `Var` is non-ground; an `App` is ground iff every arg is —
    /// args are interned before their parent so their bit is already set).
    /// Lets `Substitution::apply` return a ground subterm in O(1) instead of
    /// re-walking it (galaxy's δ-bodies are huge ground terms). Behaviour-
    /// identical: `θ` applied to a variable-free term is that same term.
    ground: Vec<bool>,
}

impl TermStore {
    fn new() -> Self {
        // #3-step-1 (perf-audit D-W3, measured: hashbrown reserve_rehash on
        // the hash-cons map is visibly hot — galaxy/binarith intern 10⁵–10⁶
        // nodes from zero capacity ⇒ ~16+ doubling rehashes, each an
        // O(current_size) copy). Pre-size to skip that churn. **Value-
        // identical**: `TermId` = `vec.len()` (capacity-independent),
        // hash-cons semantics unchanged — purely fewer reallocations.
        // A *modest constant-factor* first increment; the substantial
        // D-W3 win is step-2 (lock-free / sharded store removing the
        // RwLock read/write serialisation). 64Ki ≈ a few MB upfront —
        // negligible for small uses, kills the early-rehash burst that
        // dominates the medium/large reductions.
        const CAP: usize = 1 << 16;
        Self {
            map: FxHashMap::with_capacity_and_hasher(CAP, Default::default()),
            vec: Vec::with_capacity(CAP),
            ground: Vec::with_capacity(CAP),
        }
    }

    fn intern(&mut self, data: TermData) -> TermId {
        if let Some(&id) = self.map.get(&data) {
            return id;
        }
        let id = TermId(self.vec.len() as u32);
        let is_ground = match &data {
            TermData::Var(_) => false,
            TermData::App(_, args) => {
                args.iter().all(|a| self.ground[a.0 as usize])
            }
        };
        self.vec.push(data.clone());
        self.ground.push(is_ground);
        self.map.insert(data, id);
        id
    }

    fn get(&self, id: TermId) -> &TermData {
        &self.vec[id.0 as usize]
    }
}

static TERM_STORE: LazyLock<RwLock<TermStore>> = LazyLock::new(|| RwLock::new(TermStore::new()));

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// Intern a `TermData` into the global store and return its `TermId`.
pub fn mk(data: TermData) -> TermId {
    // Fast path: shared read lock for the common already-interned case
    // (no writer contention among the read-heavy engine hot loops).
    if let TermData::App(..) | TermData::Var(..) = data {
        if let Some(&id) = TERM_STORE.read().unwrap().map.get(&data) {
            return id;
        }
    }
    TERM_STORE.write().unwrap().intern(data)
}

/// Retrieve the `TermData` for a `TermId`.
///
/// Shared read lock + `O(1)` clone (App args are `Arc` — refcount bump, no
/// heap alloc). The store is append-only so the entry is immutable.
pub fn get(id: TermId) -> TermData {
    TERM_STORE.read().unwrap().get(id).clone()
}

/// `true` iff `id` is variable-free (cached per node at intern time, O(1)).
/// A substitution applied to a ground term is the identity, so callers may
/// short-circuit on this without changing any result.
pub fn is_ground(id: TermId) -> bool {
    TERM_STORE.read().unwrap().ground[id.0 as usize]
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
