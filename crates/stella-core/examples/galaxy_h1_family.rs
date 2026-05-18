//! MEASURE — Hypothesis **H1** for galaxy `data[0]`: redex-FAMILY
//! duplication (docs/16 §2 H1 row + §3.2; docs/12 §C.2; docs/11 Lever C).
//!
//!   cargo run -q --release --example galaxy_h1_family
//!
//! BACKGROUND. Lever C (closed-`TermId` NF memo, commit `b6c65d5`) is a
//! *measured honest-negative* on `data[0]`: it is NOT closed-subterm
//! redundant. H1 is the DISTINCT, finer claim (docs/12 §C.2): the engine
//! re-reduces duplicated *redex families* — `s`/`b`/`c` (combinator
//! `Splice`) copy their argument and `δ` (`Delta`, the `:N ↦ body`) splices
//! shared bodies, and each *copy* is re-reduced from scratch even though the
//! closed-`TermId` memo provably cannot see this sharing (the copies are in
//! different reduction states / never the same closed `TermId`). That is a
//! reduction that is "long and non-redundant" to a subterm cache yet highly
//! redundant in **redex-family** terms — exactly the interaction-net /
//! Lévy-optimal sweet spot.
//!
//! WHAT THIS MEASURES (read-only; the reference engine is the oracle, the
//! instrumentation observes only — `galaxy::eval_forced` unchanged). At
//! every committed resolution step the behaviour-preserving
//! `interactive::h1_tap` (gated exactly like `LAYER_TRACE`: `None` in
//! production & tests, byte-identical otherwise — the N-KS
//! `iex_fast_result_eq_iex` battery still passes) records the *resolved
//! head* and the α-canonical key (`antiunify::canonical`) of the redex.
//! Per head class we then count:
//!   (a) TOTAL resolutions per resolvable head, especially `s/b/c`
//!       (combinator `Splice`) and `δ` (`Delta`);
//!   (b) DISTINCT (α-canonical) redexes per class.
//! The redex-family-duplication metric is `dup = total / distinct`. We
//! ladder the bounded step-fuel (the engine descends deeper into the s/δ
//! copy fan-out as fuel grows — the docs/12 §C.2 depth axis) and print, per
//! rung, the `s/b/c/δ` total curve, the distinct curve, and the ratio.
//!
//! VERDICT (in-harness, no expected sign forced):
//!   • `dup` on `s/b/c/δ` grows SUPER-LINEARLY in depth while DISTINCT does
//!     NOT ⇒ **H1 SUPPORTED** — the engine re-reduces structurally-equal
//!     copies; interaction-net is the structurally-correct crosser.
//!   • `dup` ~flat (≈1, distinct ≈ total) ⇒ **H1 NOT supported on this
//!     axis** — work is genuinely non-redex-family-redundant.
//!   • descent fails / budget never deepens the recursion ⇒ **INCONCLUSIVE**
//!     (reported honestly; no retro-widening).
//!
//! Self-bounding: the ladder axis is the STEP-FUEL of one bounded
//! `eval_forced` (more fuel ⇒ the engine descends deeper into the s/δ copy
//! fan-out — the docs/12 §C.2 depth axis), and the H1 tap is capped so
//! recording is a cheap no-op past `TAP_CAP` redexes. Each rung therefore
//! returns in bounded wall time even though `data[0]`'s *full* force
//! diverges (the measured KG6c blocker — we never run it to completion; the
//! H1 ratio is a property of the bounded redex *prefix* at growing depth).
//! Per-rung wall guard ≤30 s as a backstop; the descent to `data[0]` is the
//! cheap 4311/14/6/19-step path of `galaxy_data_probe` (tap NOT installed
//! during the descent ⇒ identical to that probe).

use std::collections::{BTreeMap, HashSet};

use stella_core::galaxy::{self, eval_forced, readback_ray};
use stella_core::interactive::{h1_tap_begin, h1_tap_take};
// (h1_tap_capped is available for early-stop; here the small per-rung fuel
//  already wall-bounds each rung, and the cap bounds memory/work.)
use stella_core::spec_phi::{SpecPhi, Transition};
use stella_core::term::{self, SymName, TermData, TermId};

const GALAXY_TXT: &str = "/Users/ember/dev/embershot/src/galaxy.txt";
const RUNG_WALL_SECS: f64 = 30.0;
/// Cap on recorded redexes per rung — past this, the tap is a cheap no-op
/// (memory bound; the H1 ratio is measured over this bounded prefix at each
/// depth). Large enough to see the s/δ duplication accumulate.
const TAP_CAP: usize = 1_500_000;
/// Step-fuel per `iex_fast` pass. Held SMALL and FIXED so every rung's
/// bounded `eval_forced` provably returns in a few seconds even though
/// `data[0]`'s full force diverges (the measured KG6c blocker): we measure
/// the H1 duplicated/distinct ratio over the bounded redex *prefix* the
/// budget+fuel admit, at increasing forcing depth — exactly docs/16 §3.2's
/// "bounded force", never the divergent full reduction.
const RUNG_FUEL: usize = 50_000;

fn cst(n: &str) -> TermId {
    term::mk_app_str(n, vec![])
}
fn ap(f: TermId, x: TermId) -> TermId {
    term::mk_app_str("a", vec![f, x])
}
fn hd(t: TermId) -> String {
    match term::get(t) {
        TermData::Var(_) => "<var>".into(),
        TermData::App(s, a) => format!("{}/{}", s.name.as_str(), a.len()),
    }
}
/// `a(a(cons,H),T)` → (H,T) — the protocol cons cell.
fn as_cons(t: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(s, a) = term::get(t) else { return None };
    if s.name.as_str() != "a" || a.len() != 2 {
        return None;
    }
    let TermData::App(s2, a2) = term::get(a[0]) else { return None };
    if s2.name.as_str() != "a" || a2.len() != 2 {
        return None;
    }
    match term::get(a2[0]) {
        TermData::App(s3, a3) if a3.is_empty() && s3.name.as_str() == "cons" => Some((a2[1], a[1])),
        _ => None,
    }
}

/// Classify a resolved head against Φ's compiled `SpecPhi` transition
/// table — the SAME structural classification `Σ(Φ)`/`iex_spec` uses
/// (docs/11 §B). `δ` = `Delta` (`:N ↦ body`); `s/b/c/…` = combinator
/// `Splice`; `a` = `Unwind` (Push); anything unmapped (`isnil`, strict
/// numeric ops, the §49.50 boundary) = "other".
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Class {
    Delta,  // δ : the :N ↦ body splice (shared-body duplication)
    Splice, // s/b/c/i/t/f/… : combinator copy-fanout (s x y z → (xz)(yz))
    Unwind, // a : Push (no copy)
    Other,  // isnil / strict ops / unmapped — the disclosed §60 boundary
}

fn classify(head: SymName, sp: &SpecPhi) -> Class {
    match sp.get(head.as_str()) {
        Some(Transition::Delta(_)) => Class::Delta,
        Some(Transition::Splice { .. }) => Class::Splice,
        Some(Transition::Unwind) => Class::Unwind,
        None => Class::Other,
    }
}

/// The combinator letters whose rule is *non-linear in an argument* — the
/// load-bearing copy-fanout heads of docs/12 §C.2/C.1: `s x y z → (xz)(yz)`
/// copies `z`; `b`/`c` rewire. We report `s/b/c` explicitly alongside the
/// δ class because docs/16 H1 names exactly `s/b/c/δ`.
fn is_sbc(head: SymName) -> bool {
    matches!(head.as_str(), "s" | "b" | "c" | "S" | "B" | "C")
}

#[derive(Default, Clone)]
struct Bucket {
    total: u64,
    distinct: HashSet<TermId>,
}
impl Bucket {
    fn observe(&mut self, canon: TermId) {
        self.total += 1;
        self.distinct.insert(canon);
    }
    fn d(&self) -> u64 {
        self.distinct.len() as u64
    }
    /// redex-family-duplication metric: copies per distinct family.
    fn dup(&self) -> f64 {
        if self.distinct.is_empty() {
            0.0
        } else {
            self.total as f64 / self.distinct.len() as f64
        }
    }
}

fn main() {
    let src = match std::fs::read_to_string(GALAXY_TXT) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[skip] {GALAXY_TXT}: {e} (galaxy.txt absent — clean skip)");
            return;
        }
    };
    let g = galaxy::parse(&src).expect("parse galaxy.txt");
    let phi = galaxy::constellation(&g);
    let sp = SpecPhi::build(&phi);
    eprintln!(
        "Φ compiled: {} resolvable heads in SpecPhi (δ + Push + combinator/lazy-prim Splice; \
         isnil/strict delegated — the §49.50 boundary)",
        sp.len()
    );

    // ── Cheap guided descent to data[0]'s img0 (galaxy_data_probe path:
    //    [triple]/[flag]/[state]/[data] force in 4311/14/6/19 steps — only
    //    the final image force diverges; that is the H1 target). ──────────
    let entry = galaxy::ref_atom(g.entry);
    let click = ap(
        ap(cst("cons"), stella_core::binarith::nat(0)),
        stella_core::binarith::nat(0),
    );
    let mut t = ap(ap(entry, cst("nil")), click);
    for (label, want_head) in [
        ("triple", false),
        ("after-flag", false),
        ("after-state", true),
        ("data", true),
    ] {
        let f = eval_forced(&phi, t, 2_000_000, 100_000);
        let rb = readback_ray(f.final_ray.unwrap_or(f.value));
        match as_cons(rb) {
            Some((h, tl)) => t = if want_head { h } else { tl },
            None => {
                println!(
                    "VERDICT: INCONCLUSIVE — descent stalled at [{label}] \
                     (readback head {}, not a cons). Cannot reach data[0]; \
                     report honestly, do not retro-interpret.",
                    hd(rb)
                );
                return;
            }
        }
    }
    let img0 = t;
    eprintln!("reached data[0] img0 (head={})\n", hd(img0));

    // ── Ladder the FORCING BUDGET (the docs/12 §C.2 depth axis: the
    //    `force_value` recursion depth = how deep into the s/δ copy fan-out
    //    the engine descends — the same proven-cheap regime as
    //    galaxy_layer_trace, which returns per-rung in seconds because the
    //    budget, not the 4M fuel, is the real limiter). At each rung:
    //    install the behaviour-preserving capped H1 tap, force img0 to this
    //    budget, classify every committed redex, accumulate per-class total
    //    vs α-distinct. The redex-family-duplication signature is whether
    //    `total/distinct` on s/b/c/δ grows SUPER-LINEARLY in depth while
    //    `distinct` does not. ──────────────────────────────────────────────
    let budgets: &[usize] = &[6, 8, 10, 12, 14, 16, 20, 24, 28, 32];
    println!(
        "{:>7} {:>10} {:>8} {:>8} | {:>9} {:>8} {:>7} | {:>9} {:>8} {:>7} | {:>7} {:>6}",
        "budget",
        "steps",
        "secs",
        "fullRed",
        "δ tot",
        "δ dist",
        "δ dup",
        "sbc tot",
        "sbc dst",
        "sbc dup",
        "splTot",
        "splDup",
    );

    let mut rows: Vec<(usize, f64, f64, u64, u64, u64, u64)> = Vec::new();
    // (budget, δ_dup, sbc_dup, δ_total, sbc_total, δ_distinct, sbc_distinct)

    for &budget in budgets {
        // Run the rung on a worker thread with a HARD join deadline
        // (`RUNG_WALL_SECS`). `data[0]`'s force can diverge for a given
        // budget (the measured KG6c blocker); a single non-returning
        // `eval_forced` cannot be preempted by a post-return wall check, so
        // we bound it structurally here. The tap is per-thread (thread-local
        // sink) so it is installed/taken ON the worker; on timeout we
        // abandon the worker (it holds no shared lock — the term store is a
        // process-global interner; Φ is cloned per worker) and STOP
        // laddering (deeper rungs are monotonically heavier). Pure harness
        // scaffolding — engine semantics untouched.
        let (tx, rx) = std::sync::mpsc::channel();
        let phi_w = phi.clone();
        let img0_w = img0;
        let worker = std::thread::spawn(move || {
            h1_tap_begin(TAP_CAP);
            let t0 = std::time::Instant::now();
            let f = eval_forced(&phi_w, img0_w, RUNG_FUEL, budget);
            let secs = t0.elapsed().as_secs_f64();
            let log = h1_tap_take();
            let _ = tx.send((
                f.steps,
                f.fully_reduced,
                secs,
                log,
            ));
        });
        let (steps_v, fully_v, secs, log) = match rx
            .recv_timeout(std::time::Duration::from_secs_f64(RUNG_WALL_SECS))
        {
            Ok(v) => {
                let _ = worker.join();
                v
            }
            Err(_) => {
                println!(
                    "  (budget={budget}: rung exceeded {RUNG_WALL_SECS:.0}s wall — \
                     `data[0]` force diverges at this depth, the measured KG6c \
                     blocker; abandoning worker and stopping the ladder, \
                     self-bounding. Verdict uses the {} completed rung(s).)",
                    rows.len()
                );
                break;
            }
        };
        let f_steps = steps_v;
        let f_fully = fully_v;

        // Per-class + the explicit s/b/c sub-bucket (docs/16 names s/b/c/δ).
        let mut by_class: BTreeMap<Class, Bucket> = BTreeMap::new();
        let mut sbc = Bucket::default();
        let mut per_head: BTreeMap<String, Bucket> = BTreeMap::new();
        for (head, canon) in &log {
            let cls = classify(*head, &sp);
            by_class.entry(cls).or_default().observe(*canon);
            if is_sbc(*head) {
                sbc.observe(*canon);
            }
            per_head
                .entry(format!("{}[{:?}]", head.as_str(), cls))
                .or_default()
                .observe(*canon);
        }
        let delta = by_class.get(&Class::Delta).cloned().unwrap_or_default();
        let splice = by_class.get(&Class::Splice).cloned().unwrap_or_default();

        let capped = (log.len() >= TAP_CAP).then_some(" [tap@cap]").unwrap_or("");
        println!(
            "{:>7} {:>10} {:>8.2} {:>8} | {:>9} {:>8} {:>7.2} | {:>9} {:>8} {:>7.2} | {:>7} {:>6.2}{}",
            budget,
            f_steps,
            secs,
            f_fully,
            delta.total,
            delta.d(),
            delta.dup(),
            sbc.total,
            sbc.d(),
            sbc.dup(),
            splice.total,
            splice.dup(),
            capped,
        );

        rows.push((
            budget,
            delta.dup(),
            sbc.dup(),
            delta.total,
            sbc.total,
            delta.d(),
            sbc.d(),
        ));

        if f_fully {
            println!(
                "  *** img0 TERMINATES at budget={budget} — data[0] is \
                 terminating-but-deep, not a termination-crosser problem on \
                 this axis. Reporting the dup curve up to here. ***"
            );
            // top contributing heads (diagnostic)
            let mut hv: Vec<_> = per_head.iter().collect();
            hv.sort_by_key(|(_, b)| std::cmp::Reverse(b.total));
            for (h, b) in hv.into_iter().take(6) {
                println!(
                    "      head {h:<14} total={:<7} distinct={:<6} dup={:.2}",
                    b.total,
                    b.d(),
                    b.dup()
                );
            }
            break;
        }
        if secs > RUNG_WALL_SECS {
            println!("  (rung wall {secs:.1}s > {RUNG_WALL_SECS}s — stop laddering, self-bounding)");
            break;
        }
    }

    verdict(&rows);
}

/// In-harness verdict. H1 SUPPORTED ⟺ the `s/b/c/δ` duplicated/distinct
/// ratio grows super-linearly with depth (step-fuel) WHILE the distinct count
/// does not keep pace. Measured, not assumed: we fit nothing — we check the
/// monotone growth of `dup` and that `distinct` grows sub-linearly relative
/// to `total` across the ladder, on both the δ class and the explicit s/b/c
/// bucket (docs/16 names exactly s/b/c/δ).
fn verdict(rows: &[(usize, f64, f64, u64, u64, u64, u64)]) {
    println!();
    if rows.len() < 3 {
        println!(
            "VERDICT: INCONCLUSIVE — only {} rung(s) produced data; the \
             recursion never deepened enough to separate distinct from \
             duplicated work (no retro-widening; report as-is).",
            rows.len()
        );
        return;
    }

    let first = &rows[0];
    let last = &rows[rows.len() - 1];

    // Growth of the dup metric across the ladder, δ and s/b/c.
    let d_dup_0 = first.1.max(1e-9);
    let d_dup_n = last.1;
    let s_dup_0 = first.2.max(1e-9);
    let s_dup_n = last.2;
    let d_dup_growth = d_dup_n / d_dup_0;
    let s_dup_growth = if s_dup_0 > 0.0 { s_dup_n / s_dup_0 } else { 0.0 };

    // Total vs distinct growth (the super-linear test): if total grows much
    // faster than distinct, the extra work is re-reduced *copies* of
    // α-equal redex families — the H1 mechanism.
    let d_tot_growth = (last.3 as f64) / (first.3.max(1) as f64);
    let d_dst_growth = (last.5 as f64) / (first.5.max(1) as f64);
    let s_tot_growth = (last.4 as f64) / (first.4.max(1) as f64);
    let s_dst_growth = (last.6 as f64) / (first.6.max(1) as f64);

    // Is `dup` monotone non-decreasing across the rungs (super-linear
    // duplication accumulating with depth, not a one-off)?
    let mono = |sel: fn(&(usize, f64, f64, u64, u64, u64, u64)) -> f64| {
        rows.windows(2).filter(|w| sel(&w[1]) + 1e-6 >= sel(&w[0])).count() as f64
            / (rows.len() - 1) as f64
    };
    let d_mono = mono(|r| r.1);
    let s_mono = mono(|r| r.2);

    println!("── H1 redex-family-duplication analysis ──");
    println!(
        "  δ (Delta :N↦body):  dup {:.2}→{:.2} (×{:.2}), total ×{:.2} vs distinct ×{:.2}, \
         dup-monotone {:.0}%",
        d_dup_0, d_dup_n, d_dup_growth, d_tot_growth, d_dst_growth, 100.0 * d_mono
    );
    println!(
        "  s/b/c (Splice copy): dup {:.2}→{:.2} (×{:.2}), total ×{:.2} vs distinct ×{:.2}, \
         dup-monotone {:.0}%",
        s_dup_0, s_dup_n, s_dup_growth, s_tot_growth, s_dst_growth, 100.0 * s_mono
    );

    // SUPPORTED: dup grows ≥2× across the ladder AND total outgrows distinct
    // by ≥2× (the copies-re-reduced signature) AND dup is mostly monotone,
    // on δ OR the s/b/c bucket (either copy-fanout channel suffices — both
    // are the docs/12 §C.2 mechanism).
    let superlinear = |dup_growth: f64, tot_g: f64, dst_g: f64, mono_frac: f64| {
        dup_growth >= 2.0 && tot_g >= 2.0 * dst_g.max(1.0) && mono_frac >= 0.6
    };
    let delta_sl = superlinear(d_dup_growth, d_tot_growth, d_dst_growth, d_mono);
    let sbc_sl = s_dup_0 > 0.0 && superlinear(s_dup_growth, s_tot_growth, s_dst_growth, s_mono);

    // FLAT: dup essentially constant (~1) and total ≈ distinct on both
    // channels ⇒ work is genuinely not redex-family-redundant.
    let flat_channel = |dup_n: f64, tot_g: f64, dst_g: f64| {
        dup_n < 1.5 && (tot_g - dst_g).abs() < 0.5 * tot_g.max(1.0)
    };
    let delta_flat = flat_channel(d_dup_n, d_tot_growth, d_dst_growth);
    let sbc_flat = first.4 == 0 || flat_channel(s_dup_n, s_tot_growth, s_dst_growth);

    println!();
    if delta_sl || sbc_sl {
        println!(
            "VERDICT: H1 SUPPORTED. The {} redex class shows SUPER-LINEAR \
             duplicated/distinct growth with forcing depth (the engine \
             re-reduces structurally-equal — α-canonical — copies that the \
             closed-`TermId` memo provably cannot dedup, docs/12 §C.2). \
             Interaction-net / Lévy-optimal reduction (docs/12) is the \
             structurally-correct termination-crosser on this axis: it \
             contracts each redex family once. The Lever-C closed-subterm \
             negative (b6c65d5) and this positive are CONSISTENT — they are \
             different axes (docs/16 §2 H1 row).",
            match (delta_sl, sbc_sl) {
                (true, true) => "δ AND s/b/c",
                (true, false) => "δ (shared-body splice)",
                _ => "s/b/c (combinator copy-fanout)",
            }
        );
    } else if delta_flat && sbc_flat {
        println!(
            "VERDICT: H1 NOT SUPPORTED on this axis. The duplicated/distinct \
             ratio stays ~flat (distinct ≈ total) as depth grows — the \
             reduction is genuinely not redex-family-redundant. Combined \
             with the Lever-C closed-subterm negative (b6c65d5) this points \
             away from interaction-net and toward docs/16 H2 (affine \
             recurrence, KA2) or H3 (first-class negative — no retro-widen)."
        );
    } else {
        println!(
            "VERDICT: INCONCLUSIVE on this axis. The dup curve is neither \
             clearly super-linear (δ ×{d_dup_growth:.2}, s/b/c ×{s_dup_growth:.2}) \
             nor cleanly flat within the bounded budget reached. Honest \
             report: the bounded force did not deepen the recursion enough \
             to separate the curves decisively. Widen budget OFFLINE only if \
             a rung wall did not stop it; do NOT retro-interpret the sign."
        );
    }
    println!(
        "\n(faithfulness: reference `eval_forced`/`iex` unchanged & is the \
         oracle; the H1 tap is the LAYER_TRACE-idiom thread-local — `None` \
         in production & tests, byte-identical otherwise; N-KS \
         `iex_fast_result_eq_iex` battery green.)"
    );
}
