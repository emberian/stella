//! WASM bindings for stella-viz.
//!
//! Compiled only when `--features wasm` is active (target `wasm32-unknown-unknown`).
//! Exposed via `wasm-bindgen` as a JavaScript module.
//!
//! ## API surface (mirrors the server's /api/* routes, pure-compute, no TCP)
//!
//! ```js
//! // List preset names/descriptions as a JSON string
//! const presetsJson = list_presets();
//!
//! // Get dep-graph DOT + execution summary for preset n
//! const dotJson = get_preset_dot(n);
//!
//! // Get all step snapshots for preset n as JSON
//! const stepsJson = get_preset_steps(n);
//! ```

use wasm_bindgen::prelude::*;

use crate::presets::{all_presets, all_step_data};

// Install a human-readable panic hook so browser console shows Rust panics.
#[wasm_bindgen(start)]
pub fn _start() {
    console_error_panic_hook::set_once();
}

// ── JSON helpers (no serde dep — hand-rolled just like server.rs) ─────────────

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"'  => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Return all presets as a JSON array:
/// `[{"id": 0, "name": "…", "description": "…"}, …]`
#[wasm_bindgen]
pub fn list_presets() -> String {
    let presets = all_presets();
    let items: Vec<String> = presets
        .iter()
        .enumerate()
        .map(|(i, p)| {
            format!(
                "{{\"id\":{i},\"name\":{},\"description\":{}}}",
                json_str(&p.name),
                json_str(&p.description)
            )
        })
        .collect();
    format!("[{}]", items.join(","))
}

/// Return the dep-graph DOT + execution summary for preset `idx` as JSON:
/// `{"name": "…", "dep_graph_dot": "…", "execution_summary": "…"}`
///
/// Returns `null` (JSON) if `idx` is out of range.
#[wasm_bindgen]
pub fn get_preset_dot(idx: usize) -> String {
    let presets = all_presets();
    if idx >= presets.len() {
        return "null".to_string();
    }
    let p = &presets[idx];
    format!(
        "{{\"name\":{},\"dep_graph_dot\":{},\"execution_summary\":{}}}",
        json_str(&p.name),
        json_str(&p.dep_graph_dot),
        json_str(&p.execution_summary)
    )
}

/// Return all step snapshots for preset `idx` as a JSON array.
///
/// Each element: `{"step": N, "psi_stars": […], "active_ray": "…", "dot": "…", "is_final": bool}`
///
/// Returns `"[]"` if `idx` is out of range.
#[wasm_bindgen]
pub fn get_preset_steps(idx: usize) -> String {
    let step_data = all_step_data();
    if idx >= step_data.len() {
        return "[]".to_string();
    }
    let sd = &step_data[idx];
    let items: Vec<String> = sd.steps.iter().map(|s| {
        let psi_arr: Vec<String> = s.psi_stars.iter()
            .map(|star| json_str(star))
            .collect();
        format!(
            "{{\"step\":{},\"psi_stars\":[{}],\"active_ray\":{},\"dot\":{},\"is_final\":{}}}",
            s.step,
            psi_arr.join(","),
            json_str(&s.active_ray),
            json_str(&s.dot),
            s.is_final
        )
    }).collect();
    format!("[{}]", items.join(","))
}

/// Return the number of available presets.
#[wasm_bindgen]
pub fn preset_count() -> usize {
    all_presets().len()
}
