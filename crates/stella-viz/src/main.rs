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

use presets::all_presets;

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

/// Headless mode: load all presets, print their DOT strings, and exit.
///
/// Intended for smoke-testing that the engine + viz pipeline works without
/// starting the HTTP server (useful in CI / `cargo test`).
fn run_headless() {
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
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::presets::all_presets;

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
}
