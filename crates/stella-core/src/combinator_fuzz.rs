//! KT — deterministic differential fuzz hardening the stella-combinator K1 core.
//!
//! The faithfulness floor that the acceleration work will stand on: an
//! INDEPENDENT reference oracle, differentially tested against
//! [`combinator::normalize`] (the stellar `iex_fast` engine over
//! `machine_stars()`) over thousands of random closed combinator terms.
//!
//! The oracle is a tiny self-contained classical normal-order graph reducer for
//! the `{S,B,C,I,T,F}` basis (free atoms inert constants). It does NOT touch the
//! stellar engine — it is the trusted reference, deliberately a different
//! implementation strategy so a shared bug cannot mask a disagreement.
//!
//! Reduction rules implemented (must match `machine_stars()` exactly):
//! ```text
//! I x        → x
//! T x y      → x        (T = K)
//! F x y      → y
//! S x y z    → x z (y z)
//! B x y z    → x (y z)
//! C x y z    → x z y
//! ```
//!
//! Gate: whenever BOTH the stellar engine and the independent reducer reach a
//! normal form (each fuel-bounded), the two normal forms must be α-equal
//! (compared via hash-consed `combinator::enc` `TermId` equality — exact
//! value-equality for closed terms, see `combinator::normalizes_to`). If one
//! reaches NF and the other fuels out, that is allowed (different cost). Only a
//! DISAGREEMENT on a value is a failure. A healthy fraction must converge on
//! both sides so the test has teeth (not vacuously passing on fuel-outs).

#[cfg(test)]
mod tests {
    use crate::combinator::{self, a_, app, app_n, Comb};

    // ─────────────────────────────────────────────────────────────────────────
    // Deterministic LCG — reproducible fuzz, no dev-deps (same shape as
    // `polarised.rs` `matchable_fast_tests::Lcg`).
    // ─────────────────────────────────────────────────────────────────────────

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
            self.0 >> 17
        }
        fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
            &xs[(self.next() as usize) % xs.len()]
        }
    }

    /// Leaves: the 6 combinators of the basis + 3 inert ground atoms.
    const LEAVES: [&str; 9] = ["S", "B", "C", "I", "T", "F", "x", "y", "z"];

    /// Random closed combinator term, depth/size-bounded. Closed by
    /// construction: every leaf is either a basis combinator or an inert
    /// ground atom (no variables exist in this surface language).
    fn gen(rng: &mut Lcg, depth: u32) -> Comb {
        // Bias toward applications at higher depth so terms actually reduce;
        // force a leaf at depth 0.
        if depth == 0 || rng.next() % 3 == 0 {
            // `pick` yields `&&str`; `a_` takes `&str`. The deref is required —
            // clippy::explicit_auto_deref mis-fires here (no coercion site).
            #[allow(clippy::explicit_auto_deref)]
            return a_(*rng.pick(&LEAVES));
        }
        app(gen(rng, depth - 1), gen(rng, depth - 1))
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Independent classical reducer — normal-order, fuel-bounded.
    //
    // Term = Atom | App over a Box tree; free atoms are inert constants. This
    // shares NOTHING with the stellar engine. Normal-order (leftmost-outermost):
    // try to fire a redex at the root; if the head is an un-applicable atom or
    // there are too few args, recurse into subterms left-to-right.
    // ─────────────────────────────────────────────────────────────────────────

    #[derive(Clone, PartialEq, Eq)]
    enum T {
        Atom(&'static str),
        App(Box<T>, Box<T>),
    }

    fn from_comb(c: &Comb) -> T {
        match c {
            Comb::Atom(n) => T::Atom(n),
            Comb::App(f, x) => T::App(Box::new(from_comb(f)), Box::new(from_comb(x))),
        }
    }

    fn to_comb(t: &T) -> Comb {
        match t {
            T::Atom(n) => a_(n),
            T::App(f, x) => app(to_comb(f), to_comb(x)),
        }
    }

    /// Flatten an application spine into `(head, args)` where `head` is the
    /// leftmost non-application and `args` are in application order.
    fn spine(t: &T) -> (&T, Vec<&T>) {
        let mut head = t;
        let mut args: Vec<&T> = Vec::new();
        while let T::App(f, x) = head {
            args.push(x);
            head = f;
        }
        args.reverse();
        (head, args)
    }

    fn mk_app(head: T, args: &[&T]) -> T {
        let mut acc = head;
        for a in args {
            acc = T::App(Box::new(acc), Box::new((*a).clone()));
        }
        acc
    }

    /// One leftmost-outermost reduction step. Returns `Some(reduced)` if a
    /// redex was fired anywhere (root first, then into subterms), else `None`
    /// (already in normal form).
    fn step(t: &T) -> Option<T> {
        // Try a root redex first (leftmost-outermost).
        let (head, args) = spine(t);
        if let T::Atom(name) = head {
            let n = args.len();
            let fire = |body: T, consumed: usize| -> T {
                // Re-apply any leftover args beyond what the rule consumed.
                mk_app(body, &args[consumed..])
            };
            match *name {
                "I" if n >= 1 => {
                    let x = args[0].clone();
                    return Some(fire(x, 1));
                }
                "T" if n >= 2 => {
                    let x = args[0].clone();
                    return Some(fire(x, 2));
                }
                "F" if n >= 2 => {
                    let y = args[1].clone();
                    return Some(fire(y, 2));
                }
                "B" if n >= 3 => {
                    // B x y z → x (y z)
                    let x = args[0].clone();
                    let y = args[1].clone();
                    let z = args[2].clone();
                    let body = T::App(Box::new(x), Box::new(T::App(Box::new(y), Box::new(z))));
                    return Some(fire(body, 3));
                }
                "C" if n >= 3 => {
                    // C x y z → x z y
                    let x = args[0].clone();
                    let y = args[1].clone();
                    let z = args[2].clone();
                    let body = T::App(
                        Box::new(T::App(Box::new(x), Box::new(z))),
                        Box::new(y),
                    );
                    return Some(fire(body, 3));
                }
                "S" if n >= 3 => {
                    // S x y z → x z (y z)
                    let x = args[0].clone();
                    let y = args[1].clone();
                    let z = args[2].clone();
                    let xz = T::App(Box::new(x), Box::new(z.clone()));
                    let yz = T::App(Box::new(y), Box::new(z));
                    let body = T::App(Box::new(xz), Box::new(yz));
                    return Some(fire(body, 3));
                }
                _ => {}
            }
        }
        // No root redex: recurse leftmost-outermost into the spine. The spine
        // is `head a0 a1 ...`; descend into `head` first, then args in order.
        if let T::App(f, x) = t {
            if let Some(f2) = step(f) {
                return Some(T::App(Box::new(f2), x.clone()));
            }
            if let Some(x2) = step(x) {
                return Some(T::App(f.clone(), Box::new(x2)));
            }
        }
        None
    }

    /// Outcome of the independent reducer.
    struct RefOut {
        comb: Comb,
        normal_form: bool,
    }

    /// Normal-order reduce, fuel-bounded.
    fn ref_normalize(c: &Comb, fuel: usize) -> RefOut {
        let mut cur = from_comb(c);
        for _ in 0..fuel {
            match step(&cur) {
                Some(next) => cur = next,
                None => {
                    return RefOut {
                        comb: to_comb(&cur),
                        normal_form: true,
                    }
                }
            }
        }
        RefOut {
            comb: to_comb(&cur),
            normal_form: false,
        }
    }

    /// Is this combinator term a single bare atom (no application)?
    fn is_atom(c: &Comb) -> bool {
        matches!(c, Comb::Atom(_))
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The differential gate.
    //
    // SEMANTIC NOTE (established empirically while building this test, and
    // consistent with the `combinator.rs` module doc lines 50-56): the stellar
    // engine is **call-by-name with empty-stack readout**. `normalize` returns
    // `Some(v)` iff the term reduces to a process `+P(st(v, ε))` — i.e. the
    // normal form fully consumes its argument stack. For the closed terms here
    // (free atoms are inert and never consume a stack) that happens **iff the
    // normal form is a single bare atom**. When the NF is *applicative*
    // (e.g. `x y`, a free atom applied to args) the engine still reaches a true
    // normal form (`normal_form == true`) but `value == None` — by design, not
    // a bug. `read_value` only reads at `ε`.
    //
    // The independent reducer computes the FULL classical normal form. The
    // faithful cross-check is therefore two-pronged:
    //   (A) when the reference NF is a lone atom, the stellar engine MUST yield
    //       exactly that atom as its value (α-equal via hash-consed `enc`);
    //   (B) when the reference NF is applicative, the stellar engine MUST still
    //       reach a normal form but yield `None` (the documented readout).
    // A violation of EITHER prong is a real disagreement, reported loudly.
    // ─────────────────────────────────────────────────────────────────────────

    /// Run both reducers on `t`. On agreement returns one of
    /// {AtomBoth, ApplBoth, RefOnly, StellarOnly, NeitherNF}; on a disagreement
    /// returns `Err` with a diagnostic so the failing term is reported loudly.
    enum Outcome {
        /// Reference NF is a lone atom; stellar yielded the same atom (teeth).
        AtomBoth,
        /// Reference NF is applicative; stellar reached NF with `value=None`
        /// exactly as the call-by-name readout predicts (teeth).
        ApplBoth,
        /// Reference reached NF; stellar fuelled out (allowed — cost split).
        RefOnly,
        /// Stellar reached NF; reference fuelled out (allowed — cost split).
        StellarOnly,
        /// Both fuelled out (allowed).
        NeitherNF,
    }

    /// Stellar fuel is given a large multiple of the reference fuel: each
    /// combinator rule on the stellar side is a Push chain + a rewrite star, so
    /// the engine spends many IEx steps per single classical reduction. This is
    /// a COST asymmetry, not a correctness one — equalising the *budget* (not
    /// the step count) keeps the differential meaningful instead of vacuously
    /// fuel-splitting on the cheaper reducer.
    const STELLAR_FUEL_MULT: usize = 64;

    fn differential(t: &Comb, fuel: usize) -> Result<Outcome, String> {
        let stellar = combinator::normalize(t, fuel * STELLAR_FUEL_MULT);
        let reference = ref_normalize(t, fuel);

        let stellar_nf = stellar.normal_form;
        let ref_nf = reference.normal_form;

        match (stellar_nf, ref_nf) {
            (true, true) => {
                if is_atom(&reference.comb) {
                    // Prong (A): lone-atom NF — stellar MUST yield this atom.
                    let want = combinator::enc(&reference.comb);
                    match stellar.value {
                        Some(v) if v == want => Ok(Outcome::AtomBoth),
                        other => Err(format!(
                            "DISAGREEMENT (atomic NF)!\n  term            = {:?}\n  reference NF    = {:?}\n  stellar value   = {:?}\n  expected (enc)  = {:?}\n  stellar steps   = {}",
                            t, reference.comb, other, want, stellar.steps
                        )),
                    }
                } else {
                    // Prong (B): applicative NF — call-by-name readout yields
                    // no value, but the engine must still report a normal form.
                    match stellar.value {
                        None => Ok(Outcome::ApplBoth),
                        Some(v) => Err(format!(
                            "DISAGREEMENT (applicative NF but stellar produced a value)!\n  term          = {:?}\n  reference NF  = {:?} (not a bare atom)\n  stellar value = {:?}\n  stellar steps = {}",
                            t, reference.comb, crate::term::get(v), stellar.steps
                        )),
                    }
                }
            }
            (false, true) => Ok(Outcome::RefOnly),
            (true, false) => Ok(Outcome::StellarOnly),
            (false, false) => Ok(Outcome::NeitherNF),
        }
    }

    /// Fixed regression points, including confluence cases. Each must AGREE
    /// across the two reducers (no disagreement); whether the stellar side
    /// yields a value or a value-less applicative NF is determined by the
    /// call-by-name readout and checked by `differential`.
    fn fixed_cases() -> Vec<Comb> {
        vec![
            // Identity laws.
            app(a_("I"), a_("x")),
            app_n([a_("T"), a_("x"), a_("y")]),
            app_n([a_("F"), a_("x"), a_("y")]),
            // S K K = I  (K = T): S T T x → x.
            app_n([a_("S"), a_("T"), a_("T"), a_("x")]),
            // Confluence: S (K I) (K I) x — both "branches" must agree.
            // K = T, so K I = T I.  S (T I) (T I) x → (T I x) ((T I) x)
            //   → I (I x) → x.
            app_n([
                a_("S"),
                app(a_("T"), a_("I")),
                app(a_("T"), a_("I")),
                a_("x"),
            ]),
            // B/C laws.
            app_n([a_("B"), a_("I"), a_("T"), a_("x"), a_("y")]),
            app_n([a_("C"), a_("T"), a_("x"), a_("y")]),
            // Church pair: pair a b = C (C I a) b ; car = · T, cdr = · F.
            app(
                app_n([a_("C"), app_n([a_("C"), a_("I"), a_("a")]), a_("b")]),
                a_("T"),
            ),
            app(
                app_n([a_("C"), app_n([a_("C"), a_("I"), a_("a")]), a_("b")]),
                a_("F"),
            ),
            // Nested duplication via S: S S S — pure structural churn.
            app_n([a_("S"), a_("S"), a_("S"), a_("x"), a_("y"), a_("z")]),
            // A term that should reach NF after argument flips and compose.
            app_n([a_("C"), a_("B"), a_("x"), a_("I"), a_("y")]),
        ]
    }

    #[test]
    fn kt_differential_fuzz() {
        const FUEL: usize = 4000;
        const N: usize = 20_000;
        const MAX_DEPTH: u32 = 7;

        let mut atom_both = 0usize;
        let mut appl_both = 0usize;
        let mut ref_only = 0usize;
        let mut stellar_only = 0usize;
        let mut neither = 0usize;
        let mut failures: Vec<String> = Vec::new();

        let tally = |t: &Comb, fuel: usize, fixed: bool,
                         failures: &mut Vec<String>,
                         atom_both: &mut usize, appl_both: &mut usize,
                         ref_only: &mut usize, stellar_only: &mut usize,
                         neither: &mut usize| {
            match differential(t, fuel) {
                Ok(Outcome::AtomBoth) => *atom_both += 1,
                Ok(Outcome::ApplBoth) => *appl_both += 1,
                Ok(Outcome::RefOnly) => *ref_only += 1,
                Ok(Outcome::StellarOnly) => *stellar_only += 1,
                Ok(Outcome::NeitherNF) => *neither += 1,
                Err(e) => {
                    if failures.len() < 12 {
                        failures.push(if fixed { format!("[fixed] {e}") } else { e });
                    }
                }
            }
        };

        // 1. Fixed regression / confluence points.
        for t in fixed_cases() {
            tally(&t, FUEL, true, &mut failures, &mut atom_both, &mut appl_both,
                  &mut ref_only, &mut stellar_only, &mut neither);
        }

        // 2. Random closed terms.
        let mut rng = Lcg(0x5715_0517_C0FF_EE01);
        for _ in 0..N {
            let depth = 1 + (rng.next() as u32 % MAX_DEPTH);
            let t = gen(&mut rng, depth);
            tally(&t, FUEL, false, &mut failures, &mut atom_both, &mut appl_both,
                  &mut ref_only, &mut stellar_only, &mut neither);
        }

        let both = atom_both + appl_both;
        let total = both + ref_only + stellar_only + neither + failures.len();
        eprintln!("── KT differential fuzz ───────────────────────────────");
        eprintln!("  total terms exercised   : {total}");
        eprintln!("  agreed, atomic NF       : {atom_both}  (stellar yielded the atom — full teeth)");
        eprintln!("  agreed, applicative NF  : {appl_both}  (stellar NF + value=None, as call-by-name predicts)");
        eprintln!("  reference-NF only       : {ref_only}  (stellar fuel-out — allowed cost split)");
        eprintln!("  stellar-NF only         : {stellar_only}  (reference fuel-out — allowed cost split)");
        eprintln!("  neither reached NF      : {neither}  (both fuel-out — allowed)");
        eprintln!("  DISAGREEMENTS           : {}", failures.len());
        eprintln!("───────────────────────────────────────────────────────");

        if !failures.is_empty() {
            for f in &failures {
                eprintln!("\n!!! {f}");
            }
            panic!(
                "{} disagreement(s) between the stellar engine and the \
                 independent classical reducer — REAL FINDING (see minimal terms above)",
                failures.len()
            );
        }

        // Teeth: the value-comparing prong (atomic NF, where the stellar engine
        // actually produces and we check a concrete value) must fire on a
        // healthy number of terms — otherwise the test passes vacuously on
        // fuel-outs / unobservable applicative forms. Empirically thousands of
        // these small random terms reduce to a bare atom.
        assert!(
            atom_both >= 1000,
            "too few atomic-NF agreements ({atom_both}) — the value gate would \
             be near-vacuous; lower depth or raise fuel"
        );
        // And the overall convergence must be a healthy fraction so the test
        // is not dominated by fuel-outs.
        assert!(
            both * 2 >= total,
            "too few terms converged on BOTH reducers ({both}/{total})"
        );
    }
}

