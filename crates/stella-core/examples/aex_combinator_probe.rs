//! Re-aim step 3 isolation: where does COPY-FREE plain aex (no expand_constellation; the faithfully-objective
//! saturation + 2 copies) blow up on the OBJECTIVE combinator core?
use stella_core::combinator::{a_, app, app_n, initial_process, machine_stars, Comb};
use stella_core::constellation::{star_kind, star_kind_eng, StarKind};
use stella_core::dep_graph::DepGraph;
use stella_core::term::{self, TermData, TermId};
fn read_value(psi: &[Vec<TermId>]) -> Option<TermId> {
    for star in psi {
        if star.len()!=1 { continue }
        if let TermData::App(s,a)=term::get(star[0]) {
            if s.name.as_str()=="P" && a.len()==1 {
                if let TermData::App(s2,sa)=term::get(a[0]) {
                    if s2.name.as_str()=="st" && sa.len()==2 { return Some(sa[0]) }
                }
            }
        }
    }
    None
}
fn main() {
    // Classification amplification: legacy census vs faithful Eng.
    let ms = machine_stars();
    let leg_animist = ms.iter().filter(|s| star_kind(s)==StarKind::Animist).count();
    let eng_animist = ms.iter().filter(|s| star_kind_eng(s)==StarKind::Animist).count();
    let eng_obj = ms.iter().filter(|s| star_kind_eng(s)==StarKind::Objective).count();
    println!("machine_stars: {} stars | legacy-census Animist={} (⇒ aex_full copies each 2×) | star_kind_eng Objective={} Animist={}", ms.len(), leg_animist, eng_obj, eng_animist);
    let cases: Vec<(&str, Comb)> = vec![
        ("bare x", a_("x")),
        ("I x", app(a_("I"), a_("x"))),
        ("T x y", app_n([a_("T"), a_("x"), a_("y")])),
        ("SKK x", app_n([a_("S"), a_("T"), a_("T"), a_("x")])),
    ];
    for (label, t) in &cases {
        let mut combined = machine_stars();
        combined.push(initial_process(t));
        let t0 = std::time::Instant::now();
        let ph = combined.clone();
        let h = std::thread::spawn(move || {
            let dg = DepGraph::from_constellation(&ph);
            let psi = stella_core::execution::aex(&ph, &dg);
            (psi.len(), read_value(&psi).is_some())
        });
        let mut done = None;
        while t0.elapsed().as_secs() < 45 {
            if h.is_finished() { done = Some(h.join().unwrap()); break; }
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
        match done {
            Some((n, hasv)) => println!("{label:10} -> {n} result-stars, readback_value={hasv}, {:.2}s", t0.elapsed().as_secs_f64()),
            None => { println!("{label:10} -> DID NOT FINISH in 45s (reference AEx intractable here)"); break; }
        }
    }
}
