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

use crate::build::build as build_machine_impl;
use crate::exsem::ex_summary;
use crate::logic::{
    behaviour as lc_behaviour_impl, orthogonality as lc_ortho_impl,
    proofnet as lc_proofnet_impl,
};
use crate::presets::{all_presets, all_step_data, preset_io};
use crate::stepper::{capture_path, capture_steps, StepSnapshot};
use stella_core::constellation::Constellation;
use stella_core::parse::{parse_constellation, parse_psi};

/// Clamp the caller's fuel into a sane range (0 → default).
fn fuel_or(n: usize) -> usize {
    if n == 0 { 300 } else { n.min(20_000) }
}

/// Render a constellation back to surface syntax — the inverse the IDE uses
/// to make any engine-built showcase editable. `parse(format(c))` is faithful.
fn format_constellation(c: &Constellation) -> String {
    c.iter()
        .map(|s| {
            let rays: Vec<String> = s.iter().map(|r| format!("{r}")).collect();
            format!("[{}]", rays.join(", "))
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

/// The editable source `{ "phi": "...", "psi": "..." }` for preset `idx`,
/// or `null`. This is what makes every showcase a first-class editable
/// example rather than a read-only trace.
#[wasm_bindgen]
pub fn preset_source(idx: usize) -> String {
    match preset_io(idx) {
        Some((phi, psi)) => format!(
            "{{\"phi\":{},\"psi\":{}}}",
            json_str(&format_constellation(&phi)),
            json_str(&format_constellation(&psi))
        ),
        None => "null".to_string(),
    }
}

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
    steps_json(&sd.steps)
}

/// Serialize one snapshot, including the redex set and the next MGU.
fn snapshot_json(s: &StepSnapshot) -> String {
    let psi: Vec<String> = s.psi_stars.iter().map(|x| json_str(x)).collect();
    let fire: Vec<String> = s
        .fireable
        .iter()
        .map(|f| {
            let tg: Vec<String> = f.targets.iter().map(|t| json_str(t)).collect();
            format!(
                "{{\"star\":{},\"ray\":{},\"ray_str\":{},\"kind\":{},\"targets\":[{}],\"is_next\":{}}}",
                f.star,
                f.ray,
                json_str(&f.ray_str),
                json_str(&f.kind),
                tg.join(","),
                f.is_next
            )
        })
        .collect();
    let mgu: Vec<String> = s
        .mgu
        .iter()
        .map(|(v, t)| format!("[{},{}]", json_str(v), json_str(t)))
        .collect();
    let summands: Vec<String> = s
        .summands
        .iter()
        .map(|sm| {
            let th: Vec<String> = sm
                .theta
                .iter()
                .map(|(v, t)| format!("[{},{}]", json_str(v), json_str(t)))
                .collect();
            format!(
                "{{\"external\":{},\"target\":{},\"theta\":[{}]}}",
                sm.external,
                json_str(&sm.target),
                th.join(",")
            )
        })
        .collect();
    let obs: Vec<String> = s.observable.iter().map(|x| json_str(x)).collect();
    format!(
        "{{\"step\":{},\"psi_stars\":[{}],\"active_ray\":{},\"dot\":{},\"is_final\":{},\"fireable\":[{}],\"mgu\":[{}],\"summands\":[{}],\"observable\":[{}]}}",
        s.step,
        psi.join(","),
        json_str(&s.active_ray),
        json_str(&s.dot),
        s.is_final,
        fire.join(","),
        mgu.join(","),
        summands.join(","),
        obs.join(",")
    )
}

fn steps_json(steps: &[StepSnapshot]) -> String {
    let items: Vec<String> = steps.iter().map(snapshot_json).collect();
    format!("[{}]", items.join(","))
}

/// Parse and run a user-supplied constellation. `phi_src` is the reference
/// constellation Φ; `psi_src` is the initial interaction space Ψ. Returns
/// `{"ok":true,"steps":[…]}` or `{"ok":false,"error":"…","pos":N}`.
#[wasm_bindgen]
pub fn run_source(phi_src: &str, psi_src: &str, fuel: usize) -> String {
    let phi = match parse_constellation(phi_src) {
        Ok(p) => p,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"where\":\"Φ\",\"error\":{},\"pos\":{}}}",
                json_str(&e.msg),
                e.pos
            )
        }
    };
    let psi = match parse_psi(psi_src) {
        Ok(p) => p,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"where\":\"Ψ\",\"error\":{},\"pos\":{}}}",
                json_str(&e.msg),
                e.pos
            )
        }
    };
    let steps = capture_steps(&phi, psi, fuel_or(fuel));
    format!("{{\"ok\":true,\"steps\":{}}}", steps_json(&steps))
}

/// Parse-only check (no execution) for live editor feedback. Returns
/// `{"ok":true}` or `{"ok":false,"where":"Φ|Ψ","error":"…","pos":N}`.
#[wasm_bindgen]
pub fn parse_check(phi_src: &str, psi_src: &str) -> String {
    if let Err(e) = parse_constellation(phi_src) {
        return format!(
            "{{\"ok\":false,\"where\":\"Φ\",\"error\":{},\"pos\":{}}}",
            json_str(&e.msg), e.pos
        );
    }
    if let Err(e) = parse_constellation(psi_src) {
        return format!(
            "{{\"ok\":false,\"where\":\"Ψ\",\"error\":{},\"pos\":{}}}",
            json_str(&e.msg), e.pos
        );
    }
    "{\"ok\":true}".to_string()
}

/// Like `run_source`, but drives an explicitly chosen resolution path.
/// `path` is `"i,j;i,j;…"` (star,ray per step); steps not named follow the
/// IEx default. Lets the explorer offer "pick which redex fires".
#[wasm_bindgen]
pub fn run_path(phi_src: &str, psi_src: &str, path: &str, fuel: usize) -> String {
    let phi = match parse_constellation(phi_src) {
        Ok(p) => p,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"where\":\"Φ\",\"error\":{},\"pos\":{}}}",
                json_str(&e.msg), e.pos
            )
        }
    };
    let psi = match parse_psi(psi_src) {
        Ok(p) => p,
        Err(e) => {
            return format!(
                "{{\"ok\":false,\"where\":\"Ψ\",\"error\":{},\"pos\":{}}}",
                json_str(&e.msg), e.pos
            )
        }
    };
    let chosen: Vec<(usize, usize)> = path
        .split(';')
        .filter(|s| !s.is_empty())
        .filter_map(|p| {
            let mut it = p.split(',');
            Some((it.next()?.trim().parse().ok()?, it.next()?.trim().parse().ok()?))
        })
        .collect();
    let steps = capture_path(&phi, psi, &chosen, fuel_or(fuel));
    format!("{{\"ok\":true,\"steps\":{}}}", steps_json(&steps))
}

/// Construction lab: turn a structured machine/proof spec into editable
/// surface source. `kind` ∈ {nfa,npda,ntm,atm,nfta,nfst,circuit,tiles,
/// mll,mll2i}; `json` is the spec. Returns
/// `{"ok":true,"phi":"…","psi":"…"}` or `{"ok":false,"error":"…"}`.
#[wasm_bindgen]
pub fn build_machine(kind: &str, json: &str) -> String {
    match build_machine_impl(kind, json) {
        Ok((phi, psi)) => format!(
            "{{\"ok\":true,\"phi\":{},\"psi\":{}}}",
            json_str(&phi),
            json_str(&psi)
        ),
        Err(e) => format!("{{\"ok\":false,\"error\":{}}}", json_str(&e)),
    }
}

/// Ex semantics (bounded): ɟ of CEx at copy budget `k`, the exact IEx ɟ,
/// and whether they coincide (confluence at k, demonstrated). Returns
/// `{"ok":true,"result":[…],"iex_obs":[…],"k":N,"confluent":bool,"note":"…"}`.
#[wasm_bindgen]
pub fn ex_run(phi_src: &str, psi_src: &str, k: usize, fuel: usize) -> String {
    match ex_summary(phi_src, psi_src, k, fuel_or(fuel)) {
        Err(e) => format!("{{\"ok\":false,\"error\":{}}}", json_str(&e)),
        Ok(s) => {
            let j = |v: &[String]| -> String {
                v.iter().map(|x| json_str(x)).collect::<Vec<_>>().join(",")
            };
            format!(
                "{{\"ok\":true,\"result\":[{}],\"alt\":[{}],\"order_independent\":{},\"cex\":[{}],\"cex_k\":{},\"note\":{}}}",
                j(&s.result),
                j(&s.alt),
                s.order_independent,
                j(&s.cex),
                s.cex_k,
                json_str(&s.note)
            )
        }
    }
}

/// Logic workbench — orthogonality `Φ₁ ⊥ Φ₂` (the three relations).
#[wasm_bindgen]
pub fn lc_ortho(phi1: &str, phi2: &str) -> String {
    match lc_ortho_impl(phi1, phi2) {
        Ok(j) => j,
        Err(e) => format!("{{\"ok\":false,\"error\":{}}}", json_str(&e)),
    }
}

/// Proof-net correctness (DR / Girard) + Φ_comp source + guarded diagrams.
/// `kind` ∈ {mll, mll2i}.
#[wasm_bindgen]
pub fn lc_proofnet(kind: &str, json: &str) -> String {
    match lc_proofnet_impl(kind, json) {
        Ok(j) => j,
        Err(e) => format!("{{\"ok\":false,\"error\":{}}}", json_str(&e)),
    }
}

/// Behaviour / type bench — A^⊥, A^⊥⊥, is-behaviour over a small universe.
#[wasm_bindgen]
pub fn lc_behaviour(json: &str) -> String {
    match lc_behaviour_impl(json) {
        Ok(j) => j,
        Err(e) => format!("{{\"ok\":false,\"error\":{}}}", json_str(&e)),
    }
}

/// Return the number of available presets.
#[wasm_bindgen]
pub fn preset_count() -> usize {
    all_presets().len()
}
