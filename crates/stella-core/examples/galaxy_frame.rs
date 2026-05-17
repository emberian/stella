//! KG6 — galaxy end-to-end: first interaction → rendered frame.
//!
//!   cargo run -q --release --example galaxy_frame
//!
//! Runs `interact::galaxy_first_frame` (state=nil, click=(0,0)) with
//! escalating bounds and reports the measured outcome: the protocol triple,
//! and on flag==0 the `multipledraw` frame (image count + point counts +
//! bounding box). Honest: an unforced/`Opaque` payload or non-convergence
//! is reported as a measured stop, not a faked frame.

use std::time::Instant;
use stella_core::galaxy;
use stella_core::interact;

fn main() {
    let path = "/Users/ember/dev/embershot/src/galaxy.txt";
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[galaxy_frame] SKIP — {path}: {e}");
            return;
        }
    };
    let g = galaxy::parse(&src).expect("galaxy.txt parses");
    let phi = galaxy::constellation(&g);
    println!("entry :{}  Φ stars={}", g.entry, phi.len());

    for &(fuel, maxf, rounds) in &[
        (200_000usize, 5_000usize, 4usize),
        (1_000_000, 50_000, 8),
    ] {
        let t0 = Instant::now();
        let out = interact::galaxy_first_frame(&phi, g.entry, fuel, maxf, rounds);
        let dt = t0.elapsed();
        match out {
            Some((state, frame)) => {
                let total_pts: usize = frame.iter().map(|i| i.len()).sum();
                let bbox = frame
                    .iter()
                    .flatten()
                    .fold(None, |b: Option<(i128, i128, i128, i128)>, &(x, y)| {
                        Some(match b {
                            None => (x, y, x, y),
                            Some((lx, ly, hx, hy)) => {
                                (lx.min(x), ly.min(y), hx.max(x), hy.max(y))
                            }
                        })
                    });
                println!(
                    "fuel={fuel} maxf={maxf} rounds={rounds}: FRAME in {:.2}s\n  \
                     images={} total_points={} bbox={:?}\n  \
                     per-image point counts: {:?}\n  finalState = {}",
                    dt.as_secs_f64(),
                    frame.len(),
                    total_pts,
                    bbox,
                    frame.iter().map(|i| i.len()).collect::<Vec<_>>(),
                    stella_core::galaxy_decode::pretty(&state),
                );
                return;
            }
            None => {
                println!(
                    "fuel={fuel} maxf={maxf} rounds={rounds}: no frame in {:.2}s \
                     (honest stop — unforced payload or non-convergence)",
                    dt.as_secs_f64()
                );
            }
        }
    }
    println!("[verdict] measured: no rendered frame within bounds. Not faked.");
}
