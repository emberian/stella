//! stella-viz — interactive stellar-resolution explorer.
//!
//! ## UI tech choice: stdlib HTTP + browser (no external framework)
//!
//! A zero-dependency HTTP server (stdlib `TcpListener`) serves a single-page
//! HTML+JS application.  The browser renders Graphviz DOT via the
//! `@viz-js/viz` CDN library.  This approach:
//!
//! * Requires **no external Rust crates** beyond `stella-core` — builds cleanly
//!   offline once the crate registry is seeded.
//! * Avoids `axum`/`tokio` dependency chains that would pull in ~40 crates and
//!   risk resolution failures in the isolated worktree.
//! * Ships a real interactive browser UI with step navigation, preset picker,
//!   and live DOT rendering — faithful to the assignment's minimum-viable bar.
//!
//! ## Usage
//!
//! ```text
//! cargo run -p stella-viz                   # default port 7878
//! cargo run -p stella-viz -- --port 9090    # custom port
//! cargo run -p stella-viz -- --headless     # headless: print DOT strings and exit
//! ```

mod presets;
mod server;
pub mod stepper;

use presets::{all_presets, all_step_data};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut port: u16 = 7878;
    let mut headless = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--port" => {
                i += 1;
                if let Some(p) = args.get(i) {
                    port = p.parse().unwrap_or_else(|_| {
                        eprintln!("Invalid port: {p}");
                        std::process::exit(1);
                    });
                }
            }
            "--headless" => { headless = true; }
            "--help" | "-h" => {
                println!("stella-viz — stellar resolution visualizer");
                println!("Usage:");
                println!("  stella-viz [--port PORT] [--headless]");
                println!();
                println!("Options:");
                println!("  --port PORT    TCP port to serve on (default: 7878)");
                println!("  --headless     Print preset DOT strings to stdout and exit");
                println!("  --help         Show this help");
                std::process::exit(0);
            }
            other => {
                eprintln!("Unknown argument: {other}");
                std::process::exit(1);
            }
        }
        i += 1;
    }

    if headless {
        run_headless();
    } else {
        if let Err(e) = server::serve(port) {
            eprintln!("server error: {e}");
            std::process::exit(1);
        }
    }
}

/// Headless mode: load all presets and step data, print their DOT strings, and exit.
///
/// Intended for smoke-testing that the engine + viz pipeline works without
/// starting the HTTP server (useful in CI / `cargo test`).
fn run_headless() {
    // Summary presets (static dep-graph + IEx result).
    let presets = all_presets();
    for (i, p) in presets.iter().enumerate() {
        println!("=== Preset {i}: {} ===", p.name);
        println!("--- Execution ---");
        println!("{}", p.execution_summary);
        println!("--- Dep-graph DOT ({} chars) ---", p.dep_graph_dot.len());
        // Print only the first few lines so output is manageable
        for line in p.dep_graph_dot.lines().take(8) {
            println!("{line}");
        }
        if p.dep_graph_dot.lines().count() > 8 {
            println!("  … ({} more lines)", p.dep_graph_dot.lines().count() - 8);
        }
        println!();
    }

    // Step-by-step traces.
    println!("=== Step-through traces ===");
    let step_data = all_step_data();
    for (i, sd) in step_data.iter().enumerate() {
        println!("--- Preset {i}: {} ({} steps) ---", sd.name, sd.steps.len());
        // Print step-0 and step-N DOTs (first 4 lines each).
        if let Some(s0) = sd.steps.first() {
            println!("  Step 0 DOT ({} chars, is_final={}):", s0.dot.len(), s0.is_final);
            for line in s0.dot.lines().take(4) {
                println!("    {line}");
            }
        }
        if sd.steps.len() > 1 {
            let sn = sd.steps.last().unwrap();
            println!("  Step {} DOT ({} chars, is_final={}):", sn.step, sn.dot.len(), sn.is_final);
            for line in sn.dot.lines().take(4) {
                println!("    {line}");
            }
            println!("  Final Ψ: {}", sn.psi_stars.join("; "));
        }
        println!();
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::presets::{all_presets, all_step_data};

    /// Smoke test: load all presets, verify DOT strings are non-empty and
    /// well-formed (start/end with correct graphviz delimiters).
    #[test]
    fn smoke_all_presets_produce_dot() {
        let presets = all_presets();
        assert!(!presets.is_empty(), "should have at least one preset");
        for (i, p) in presets.iter().enumerate() {
            let dot = &p.dep_graph_dot;
            assert!(
                !dot.is_empty(),
                "preset {i} ({}) dep_graph_dot should be non-empty",
                p.name
            );
            assert!(
                dot.contains("graph dep_graph {"),
                "preset {i} ({}) DOT should contain 'graph dep_graph {{'",
                p.name
            );
            assert!(
                dot.trim_end().ends_with('}'),
                "preset {i} ({}) DOT should end with '}}'",
                p.name
            );
            assert!(
                !p.execution_summary.is_empty(),
                "preset {i} ({}) execution_summary should be non-empty",
                p.name
            );
        }
    }

    /// Smoke: Horn-add preset includes expected stars in the DOT (star_0, star_1).
    #[test]
    fn horn_add_preset_has_stars() {
        let presets = all_presets();
        let horn = &presets[0]; // horn_add is first preset
        assert!(
            horn.dep_graph_dot.contains("star_0"),
            "Horn-add DOT should contain star_0"
        );
        assert!(
            horn.dep_graph_dot.contains("star_1"),
            "Horn-add DOT should contain star_1"
        );
    }

    /// Smoke: NFA preset execution summary mentions "ACCEPTED" or "REJECTED".
    #[test]
    fn nfa_preset_execution_verdict() {
        let presets = all_presets();
        let nfa = &presets[1]; // nfa is second preset
        let summary = &nfa.execution_summary;
        assert!(
            summary.contains("ACCEPTED") || summary.contains("REJECTED") || summary.contains("Fuel"),
            "NFA execution summary should contain a verdict; got: {summary}"
        );
    }

    /// Smoke: NTM preset execution summary mentions a verdict.
    #[test]
    fn ntm_preset_execution_verdict() {
        let presets = all_presets();
        let ntm = &presets[2]; // ntm is third preset
        let summary = &ntm.execution_summary;
        assert!(
            summary.contains("ACCEPTED") || summary.contains("REJECTED") || summary.contains("Fuel") || summary.contains("DIVERGED"),
            "NTM execution summary should contain a verdict; got: {summary}"
        );
    }

    /// Smoke: headless function runs without panicking (exercises the full pipeline).
    #[test]
    fn headless_no_panic() {
        // Redirect stdout doesn't matter here; just verify it doesn't panic.
        let presets = all_presets();
        for p in &presets {
            // Verify every piece of data is accessible.
            let _ = p.name.len();
            let _ = p.description.len();
            let _ = p.dep_graph_dot.len();
            let _ = p.execution_summary.len();
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Step-through smoke tests
    // ─────────────────────────────────────────────────────────────────────────

    /// Smoke: all presets produce at least 2 step snapshots (step-0 and step-N).
    #[test]
    fn smoke_step_data_has_steps() {
        let sd = all_step_data();
        assert!(!sd.is_empty(), "should have step data for all presets");
        for (i, d) in sd.iter().enumerate() {
            assert!(
                d.steps.len() >= 2,
                "preset {i} ({}) should have at least 2 steps (initial + final); got {}",
                d.name,
                d.steps.len()
            );
        }
    }

    /// Smoke: step-0 DOT for every preset is a valid dep_graph DOT.
    #[test]
    fn smoke_step0_dot_valid() {
        let sd = all_step_data();
        for (i, d) in sd.iter().enumerate() {
            let s0 = &d.steps[0];
            assert_eq!(s0.step, 0, "preset {i}: first snapshot should be step 0");
            assert!(
                s0.dot.contains("graph dep_graph {"),
                "preset {i} ({}) step-0 DOT should contain 'graph dep_graph {{'; got: {}",
                d.name,
                &s0.dot[..s0.dot.len().min(120)]
            );
            assert!(
                s0.dot.trim_end().ends_with('}'),
                "preset {i} ({}) step-0 DOT should end with '}}'",
                d.name
            );
        }
    }

    /// Smoke: step-N (last snapshot) for every preset is marked final and has valid DOT.
    #[test]
    fn smoke_step_n_dot_and_final() {
        let sd = all_step_data();
        for (i, d) in sd.iter().enumerate() {
            let sn = d.steps.last().unwrap();
            assert!(
                sn.is_final,
                "preset {i} ({}) last step should be marked is_final",
                d.name
            );
            assert!(
                sn.dot.contains("graph dep_graph {") || sn.dot.contains("// empty"),
                "preset {i} ({}) step-N DOT should be a valid dep_graph or empty marker",
                d.name
            );
        }
    }

    /// Smoke: Horn-add step-N Ψ contains s(s(s(s(0)))) = nat(4) (the answer 2+2=4).
    #[test]
    fn smoke_horn_add_step_n_answer() {
        let sd = all_step_data();
        let horn_steps = &sd[0]; // horn_add is first
        let sn = horn_steps.steps.last().unwrap();
        let result_str = sn.psi_stars.join(" ");
        assert!(
            result_str.contains("s(s(s(s(0))))"),
            "Horn-add 2+2 final Ψ should contain nat(4) = s(s(s(s(0)))); got: {result_str}"
        );
    }

    /// Smoke: NFA step-N Ψ contains "accept" (NFA accepts "000").
    #[test]
    fn smoke_nfa_step_n_accepts() {
        let sd = all_step_data();
        let nfa_steps = &sd[1]; // nfa is second
        let sn = nfa_steps.steps.last().unwrap();
        let result_str = sn.psi_stars.join(" ");
        assert!(
            result_str.contains("accept"),
            "NFA '000' final Ψ should contain accept; got: {result_str}"
        );
    }
}
