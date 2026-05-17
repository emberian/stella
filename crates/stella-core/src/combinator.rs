//! Binder-free combinator core — Eng's unbuilt KAM escape (subproject spec
//! `docs/05-combinator-core-and-the-kam-escape.md`, phase K1).
//!
//! Eng punted on the KAM (§57.13 "without establishing any simulation result";
//! §57.15 scoping "horrible to define"). The punt is *binding*: his floated
//! explicit-substitution rays `−i(n,X)` are unscoped (§57.16–57.19), so binder
//! re-activation has no innermost discipline. §87.2 records the escape he saw
//! but did not build: "define λ-calculus directly by encoding its term graph and
//! using the mechanisms of stellar resolution to simulate explicit
//! substitutions". Bracket-abstracted combinators have **no binders**, so the
//! capture problem cannot arise — this module instantiates that escape on the
//! fragment where it provably works (`~/dev/embershot`'s `{S,B,C,I,T,F}` basis;
//! its `galaxy.txt` is exactly this).
//!
//! ## Encoding (§57.16/§57.19 apparatus, binder machinery deleted)
//!
//! Term-graph translation, §57.16 *with the `−i` row removed* (no variables ⇒
//! no explicit-substitution rays):
//!
//! ```text
//! c•       := c                     (combinator / atom constant)
//! (M N)•    := a(M•, N•)             (verbatim §57.16)
//! ```
//!
//! By Lemma §57.18 the only free rays of `Ex(M★_α)` are the `−i(n,·)` ones;
//! with zero variables `Ex(M★_α) = [+T_α(M•)]`, and the §57.16 process
//! connector then collapses to `[+P(M• ⋆ ε)]`. So for closed binder-free
//! terms we build the initial process **directly** as `[+P(st(M•, ε))]`
//! (faithful simplification, justified by §57.18 — the term-graph `T_α` star
//! machinery only exists to thread the `−i` rays we do not have).
//!
//! Machine constellation `K★` — Eng's **Push verbatim §57.19**; Grab replaced
//! by one first-order rewrite star per combinator (the §58 label-star pattern,
//! *not* the punted `l`/`+i(X,N)` Grab):
//!
//! ```text
//! Push   [−P(a(M,N)⋆π),   +P(M⋆N·π)]                  (verbatim §57.19)
//! I      [−P(I⋆X·π),       +P(X⋆π)]
//! T(=K)  [−P(T⋆X·Y·π),     +P(X⋆π)]
//! F      [−P(F⋆X·Y·π),     +P(Y⋆π)]
//! B      [−P(B⋆X·Y·Z·π),   +P(a(X,a(Y,Z))⋆π)]
//! C      [−P(C⋆X·Y·Z·π),   +P(a(a(X,Z),Y)⋆π)]
//! S      [−P(S⋆X·Y·Z·π),   +P(a(a(X,Z),a(Y,Z))⋆π)]    ← Z duplicated
//! ```
//!
//! Every star carries **zero `i`-rays** — the binding machinery §57.15 could
//! not scope is absent by construction (K-SIM objective-fragment claim, spec §5).
//!
//! ## Execution mode
//!
//! IEx (Eng's primary Ch8 mode; the §57 process is a rewrite thread). `K★` is
//! the reference constellation `Φ` (reused every step — no copy-supply blowup,
//! unlike AEx); the process `[+P(st(M•,ε))]` is the interaction space `Ψ`.
//! Reduction runs until no machine star matches; the surviving `+P(st(v,ε))`
//! carries the call-by-name normal form `v` (combinators are confluent, so
//! call-by-name is correct; sharing is excluded from the faithful core, spec §3).

use crate::constellation::{Constellation, Star};
use crate::interactive::iex;
use crate::term::{self, TermId};

// ─────────────────────────────────────────────────────────────────────────────
// Surface terms (closed, binder-free)
// ─────────────────────────────────────────────────────────────────────────────

/// A closed binder-free combinator expression.
///
/// `Atom` is any nullary constant: a combinator (`"S"`, `"B"`, `"C"`, `"I"`,
/// `"T"`, `"F"`) or a free ground atom used as a probe in tests (e.g. `"x"`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Comb {
    Atom(&'static str),
    App(Box<Comb>, Box<Comb>),
}

/// `f a` — application.
pub fn app(f: Comb, a: Comb) -> Comb {
    Comb::App(Box::new(f), Box::new(a))
}

/// Left-associated application spine: `app_n([f, x, y, z]) = ((f x) y) z`.
pub fn app_n(parts: impl IntoIterator<Item = Comb>) -> Comb {
    let mut it = parts.into_iter();
    let mut acc = it.next().expect("app_n needs ≥1 part");
    for p in it {
        acc = app(acc, p);
    }
    acc
}

/// An atom (combinator or ground probe constant).
pub fn a_(name: &'static str) -> Comb {
    Comb::Atom(name)
}

// ─────────────────────────────────────────────────────────────────────────────
// Term constructors (the `•` encoding and machine vocabulary)
// ─────────────────────────────────────────────────────────────────────────────

fn cst(name: &str) -> TermId {
    term::mk_app_str(name, vec![])
}
fn v(name: &str) -> TermId {
    term::mk_var(name)
}
/// `a(M, N)` — application node (§57.16).
fn ap(m: TermId, n: TermId) -> TermId {
    term::mk_app_str("a", vec![m, n])
}
/// `M · π` — stack cons (right-associative, §22.6 `Stacks`).
fn dot(h: TermId, t: TermId) -> TermId {
    term::mk_app_str("dot", vec![h, t])
}
/// `ε` — the empty stack constant (§22.6).
fn eps() -> TermId {
    cst("eps")
}
/// `M ⋆ π` — the process connective (§57.16, binary infix `⋆`).
fn st(m: TermId, pi: TermId) -> TermId {
    term::mk_app_str("st", vec![m, pi])
}
/// `+P(·)` — positive process ray.
fn pp(arg: TermId) -> TermId {
    term::mk_app_str("+P", vec![arg])
}
/// `−P(·)` — negative process ray.
fn np(arg: TermId) -> TermId {
    term::mk_app_str("-P", vec![arg])
}

/// The `•` translation: surface term → its term-graph encoding (§57.16, no
/// variables — the binder-free restriction).
pub fn enc(t: &Comb) -> TermId {
    match t {
        Comb::Atom(name) => cst(name),
        Comb::App(f, x) => ap(enc(f), enc(x)),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The machine constellation K★
// ─────────────────────────────────────────────────────────────────────────────

/// `K★` — the 7 machine stars (Push §57.19 verbatim + one star per combinator).
///
/// Reused as the IEx reference constellation `Φ`; never consumed.
pub fn machine_stars() -> Constellation {
    let (m, n, x, y, z, pi) = (v("M"), v("N"), v("X"), v("Y"), v("Z"), v("Pi"));

    // Push: [−P(a(M,N)⋆π), +P(M⋆N·π)]
    let push: Star = vec![np(st(ap(m, n), pi)), pp(st(m, dot(n, pi)))];

    // I: [−P(I⋆X·π), +P(X⋆π)]
    let i: Star = vec![np(st(cst("I"), dot(x, pi))), pp(st(x, pi))];

    // T(=K): [−P(T⋆X·Y·π), +P(X⋆π)]
    let t: Star = vec![
        np(st(cst("T"), dot(x, dot(y, pi)))),
        pp(st(x, pi)),
    ];

    // F: [−P(F⋆X·Y·π), +P(Y⋆π)]
    let f: Star = vec![
        np(st(cst("F"), dot(x, dot(y, pi)))),
        pp(st(y, pi)),
    ];

    // B: [−P(B⋆X·Y·Z·π), +P(a(X,a(Y,Z))⋆π)]
    let b: Star = vec![
        np(st(cst("B"), dot(x, dot(y, dot(z, pi))))),
        pp(st(ap(x, ap(y, z)), pi)),
    ];

    // C: [−P(C⋆X·Y·Z·π), +P(a(a(X,Z),Y)⋆π)]
    let c: Star = vec![
        np(st(cst("C"), dot(x, dot(y, dot(z, pi))))),
        pp(st(ap(ap(x, z), y), pi)),
    ];

    // S: [−P(S⋆X·Y·Z·π), +P(a(a(X,Z),a(Y,Z))⋆π)]   (Z duplicated)
    let s: Star = vec![
        np(st(cst("S"), dot(x, dot(y, dot(z, pi))))),
        pp(st(ap(ap(x, z), ap(y, z)), pi)),
    ];

    vec![push, i, t, f, b, c, s]
}

/// The initial process `[+P(M• ⋆ ε)]` (justified collapse, §57.18 — see module doc).
pub fn initial_process(t: &Comb) -> Star {
    vec![pp(st(enc(t), eps()))]
}

// ─────────────────────────────────────────────────────────────────────────────
// Normalisation + readout
// ─────────────────────────────────────────────────────────────────────────────

/// Outcome of running a closed combinator term through `K★` under IEx.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CombResult {
    /// The normal-form term `v` from the surviving `+P(st(v, ε))`, if reduction
    /// reached an empty-stack normal form.
    pub value: Option<TermId>,
    /// Whether IEx reached a true normal form (vs fuel exhaustion).
    pub normal_form: bool,
    /// IEx steps taken (proper-time of the reduction).
    pub steps: usize,
}

/// Extract `v` from the unique surviving process star `[+P(st(v, ε))]`.
fn read_value(psi: &[Star]) -> Option<TermId> {
    let eps = eps();
    for star in psi {
        if star.len() != 1 {
            continue;
        }
        if let term::TermData::App(sym, args) = term::get(star[0]) {
            if sym.name.as_str() == "P" && args.len() == 1 {
                if let term::TermData::App(s2, st_args) = term::get(args[0]) {
                    if s2.name.as_str() == "st" && st_args.len() == 2 && st_args[1] == eps {
                        return Some(st_args[0]);
                    }
                }
            }
        }
    }
    None
}

/// Reduce a closed binder-free combinator term `t` under `K★` (IEx, call-by-name).
pub fn normalize(t: &Comb, fuel: usize) -> CombResult {
    let phi = machine_stars();
    let res = iex(&phi, vec![initial_process(t)], fuel);
    CombResult {
        value: read_value(&res.psi),
        normal_form: res.is_normal_form,
        steps: res.steps,
    }
}

/// Convenience: reduce and assert the normal form equals `enc(expected)`.
///
/// Closed terms reduce to closed normal forms (no free Φ-vars survive), so
/// hash-consed `TermId` equality is exact value-equality here.
pub fn normalizes_to(t: &Comb, expected: &Comb, fuel: usize) -> bool {
    normalize(t, fuel).value == Some(enc(expected))
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — Eng-grounded battery (spec §4: §22.8-style + standard combinator laws)
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    const FUEL: usize = 2000;

    /// `I x ↝ x` (the I rule; §57.19 Push then I-star).
    #[test]
    fn i_is_identity() {
        assert!(normalizes_to(&app(a_("I"), a_("x")), &a_("x"), FUEL));
    }

    /// `T x y ↝ x` — T is K (true / `const`). embershot `Primitive::T`.
    #[test]
    fn t_is_k() {
        assert!(normalizes_to(
            &app_n([a_("T"), a_("x"), a_("y")]),
            &a_("x"),
            FUEL
        ));
    }

    /// `F x y ↝ y` — F is the false / second-projection combinator.
    #[test]
    fn f_is_second() {
        assert!(normalizes_to(
            &app_n([a_("F"), a_("x"), a_("y")]),
            &a_("y"),
            FUEL
        ));
    }

    /// `S K K x ↝ x` with K = T — the classic `S K K = I` identity.
    /// Exercises the only non-linear star (S duplicates its third argument).
    #[test]
    fn skk_is_identity() {
        let skk_x = app_n([a_("S"), a_("T"), a_("T"), a_("x")]);
        assert!(normalizes_to(&skk_x, &a_("x"), FUEL));
    }

    /// `B f g x ↝ f (g x)` — composition.
    /// `B I T x y`: B I T x ↝ I (T x) ↝ T x ; then y: T x y ↝ x.
    #[test]
    fn b_is_compose() {
        let lhs = app_n([a_("B"), a_("I"), a_("T"), a_("x"), a_("y")]);
        assert!(normalizes_to(&lhs, &a_("x"), FUEL));
    }

    /// `C f x y ↝ f y x` — argument flip. `C T x y ↝ T y x ↝ y`.
    #[test]
    fn c_is_flip() {
        let lhs = app_n([a_("C"), a_("T"), a_("x"), a_("y")]);
        assert!(normalizes_to(&lhs, &a_("y"), FUEL));
    }

    /// Church-encoded list selectors fall out of the basis with NO new
    /// primitives (spec §2): embershot `Car => aa(arg, T)`, `Cdr => aa(arg, F)`,
    /// `cons a b = λs. s a b`.  Encode `cons a b := C (C I a) b` so that
    /// `cons a b T ↝ T a b ↝ a` and `cons a b F ↝ F a b ↝ b`.
    #[test]
    fn church_pair_car_cdr() {
        // pair = λa b s. s a b ; with combinators: pair a b = C (C I a) b
        let pair = |x: &'static str, y: &'static str| {
            app_n([a_("C"), app_n([a_("C"), a_("I"), a_(x)]), a_(y)])
        };
        // car (pair a b) = pair a b T ↝ a
        assert!(normalizes_to(&app(pair("a", "b"), a_("T")), &a_("a"), FUEL));
        // cdr (pair a b) = pair a b F ↝ b
        assert!(normalizes_to(&app(pair("a", "b"), a_("F")), &a_("b"), FUEL));
    }

    /// Objective-fragment claim (spec §5 / N-K3): every `K★` star is `i`-ray-free.
    /// "i-ray" = a ray whose head symbol is `i` (Eng's explicit-substitution
    /// rays §57.16) — the binding machinery §57.15 could not scope.
    #[test]
    fn k_star_has_no_i_rays() {
        for star in machine_stars() {
            for &ray in &star {
                if let term::TermData::App(sym, _) = term::get(ray) {
                    assert_ne!(
                        sym.name.as_str(),
                        "i",
                        "K★ must carry zero i-rays (binder-free escape, spec §5)"
                    );
                }
            }
        }
    }

    /// A multi-step reduction terminates at a true normal form (not fuel-out),
    /// recording proper-time. `S T T x` is 6+ steps; sanity that IEx converges.
    #[test]
    fn skk_reaches_true_normal_form() {
        let r = normalize(&app_n([a_("S"), a_("T"), a_("T"), a_("x")]), FUEL);
        assert!(r.normal_form, "should reach a true normal form, not fuel-out");
        assert_eq!(r.value, Some(enc(&a_("x"))));
        assert!(r.steps > 0);
    }
}
