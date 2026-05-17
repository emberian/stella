// explorer.js — the live stellar-resolution explorer.
//
// stella-core, compiled to wasm32-unknown-unknown, runs the interactive
// execution (IEx) entirely in the browser. This module mounts a self-contained
// explorer widget; it is used full-page by explore.html and inline, compactly,
// by the Field Journal reader.

const WASM_URL = new URL("../pkg/stella_viz_wasm.js", import.meta.url).href;
const VIZ_CDN = "https://cdn.jsdelivr.net/npm/@viz-js/viz@3/lib/viz-standalone.js";

let wasmReady = null; // Promise<api> — instantiate the engine exactly once.
let vizReady = null;  // Promise<Viz | null>

function loadWasm() {
  if (!wasmReady) {
    wasmReady = (async () => {
      const mod = await import(WASM_URL);
      await mod.default();
      return mod;
    })();
  }
  return wasmReady;
}

function loadViz() {
  if (!vizReady) {
    vizReady = new Promise((resolve) => {
      if (window.Viz) return resolve(window.Viz);
      const s = document.createElement("script");
      s.src = VIZ_CDN;
      s.onload = () => resolve(window.Viz || null);
      s.onerror = () => resolve(null); // offline → fall back to text DOT
      document.head.appendChild(s);
    }).then((V) => (V ? V.instance() : null)).catch(() => null);
  }
  return vizReady;
}

const esc = (s) =>
  String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

function classifyRay(r) {
  const s = r.trim();
  if (s.startsWith("+")) return "ray-pos";
  if (s.startsWith("-") || s.startsWith("−")) return "ray-neg";
  return "ray-neu";
}

function splitTopLevel(s) {
  const parts = [];
  let depth = 0, cur = "";
  for (const ch of s) {
    if (ch === "(") { depth++; cur += ch; }
    else if (ch === ")") { depth--; cur += ch; }
    else if (ch === "," && depth === 0) { parts.push(cur); cur = ""; }
    else cur += ch;
  }
  if (cur) parts.push(cur);
  return parts;
}

function renderStar(starStr) {
  const inner = starStr.replace(/^\[/, "").replace(/\]$/, "").trim();
  if (!inner) return '<span class="empty">∅ — empty star</span>';
  return splitTopLevel(inner)
    .map((r) => `<span class="${classifyRay(r)}">${esc(r.trim())}</span>`)
    .join('<span class="ray-neu">, </span>');
}

// Recolour Graphviz output into the Stella palette. CSS beats SVG presentation
// attributes, so a scoped <style> is enough — no attribute surgery.
function styleSvg(svg) {
  const st = document.createElementNS("http://www.w3.org/2000/svg", "style");
  st.textContent = `
    text { fill: #2a2620; font-family: 'JetBrains Mono', ui-monospace, monospace; font-size: 12px; }
    ellipse, polygon, path { stroke: #8a6a47; }
    ellipse { fill: #faf6ea; }
    path { fill: none; }
    polygon { fill: #8a6a47; }
    .node polygon { fill: #faf6ea; }
    [fill="white"], [fill="#ffffff"], [fill="none"].graph { fill: transparent; }
  `;
  svg.insertBefore(st, svg.firstChild);
  svg.removeAttribute("width");
  svg.removeAttribute("height");
}

const TEMPLATE = (compact) => `
  <div class="stx-bar">
    <span class="stx-bar__title">
      <img src="assets/stella/glyphs/star.svg" alt="" />
      Stellar resolution — interactive execution
    </span>
    <span class="stx-bar__spacer"></span>
    <span class="st-pulse" data-role="pulse">starting engine</span>
    <select class="stx-select" data-role="presets" aria-label="Choose a constellation"></select>
  </div>
  <div class="stx-body">
    <div class="stx-graph" data-role="graph">
      <span class="reader-status">Compiling stella-core to your browser…</span>
    </div>
    ${compact ? "" : '<div class="stx-trace" data-role="trace"></div>'}
  </div>
  ${compact ? '<div class="stx-trace" data-role="trace" style="max-height:300px;border-top:1px solid var(--border)"></div>' : ""}
  <div class="stx-controls">
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="reset" title="Back to step 0">↺ Reset</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="prev" title="Previous step">◂ Prev</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="next" title="Next step">Next ▸</button>
    <span class="step-readout" data-role="readout">select a constellation</span>
  </div>
  <div class="stx-desc" data-role="desc"></div>
`;

export async function mountExplorer(root, opts = {}) {
  const compact = !!opts.compact;
  root.classList.add("st-explorer");
  if (compact) root.classList.add("st-explorer--inline");
  root.innerHTML = TEMPLATE(compact);

  const $ = (r) => root.querySelector(`[data-role="${r}"]`);
  const elGraph = $("graph"), elTrace = $("trace"), elReadout = $("readout"),
        elDesc = $("desc"), elPresets = $("presets"), elPulse = $("pulse");

  const [mod, viz] = await Promise.all([loadWasm(), loadViz()]);
  elPulse.textContent = "engine ready";
  elPulse.classList.remove("st-pulse--idle");

  const presets = JSON.parse(mod.list_presets());
  elPresets.innerHTML = presets
    .map((p, i) => `<option value="${i}">${esc(p.name)}</option>`)
    .join("");

  let steps = [];
  let idx = 0;
  let presetIdx = -1;

  async function drawDot(dot) {
    if (!dot || !dot.trim() || dot.includes("// empty")) {
      elGraph.innerHTML = '<span class="reader-status">Ψ is empty — no stars.</span>';
      return;
    }
    if (viz) {
      try {
        const svg = await viz.renderSVGElement(dot);
        styleSvg(svg);
        elGraph.innerHTML = "";
        elGraph.appendChild(svg);
        return;
      } catch (_) { /* fall through to text */ }
    }
    elGraph.innerHTML = `<pre style="font-size:12px">${esc(dot)}</pre>`;
  }

  function drawTrace() {
    elTrace.innerHTML = steps
      .map((s, i) => {
        const cls =
          "stx-step" + (i === idx ? " is-current" : "") + (s.is_final ? " is-final" : "");
        const stars = s.psi_stars.length
          ? s.psi_stars.map((st) => `<span class="star">[${renderStar(st)}]</span>`).join("")
          : '<span class="empty">∅ — empty interaction space</span>';
        const fire = s.active_ray
          ? `<div class="stx-fire"><span class="lab">Next interaction</span>${esc(s.active_ray)}</div>`
          : "";
        const badge = s.is_final
          ? '<span class="stx-badge is-final">normal form</span>'
          : `<span class="stx-badge">step ${s.step}</span>`;
        return (
          `<div class="${cls}" data-step="${i}">` +
          `<div class="stx-step__label">Step ${s.step} ${badge}</div>` +
          `<div class="stx-stars">${stars}</div>${fire}</div>`
        );
      })
      .join("");
    elTrace.querySelectorAll(".stx-step").forEach((el) =>
      el.addEventListener("click", () => { idx = +el.dataset.step; render(); })
    );
    const cur = elTrace.querySelector(".is-current");
    if (cur) cur.scrollIntoView({ block: "nearest" });
  }

  function updateControls() {
    const s = steps[idx] || {};
    $("prev").disabled = idx <= 0;
    $("next").disabled = idx >= steps.length - 1;
    $("reset").disabled = steps.length === 0;
    const name = presets[presetIdx] ? presets[presetIdx].name : "";
    elReadout.innerHTML =
      `${esc(name)} — step ${idx} / ${Math.max(0, steps.length - 1)}` +
      (s.is_final ? ' <span class="nf">· normal form</span>' : "");
  }

  async function render() {
    if (!steps.length) return;
    await drawDot(steps[idx].dot);
    drawTrace();
    updateControls();
  }

  async function selectPreset(i) {
    presetIdx = i;
    elPresets.value = String(i);
    elGraph.innerHTML = '<span class="reader-status">Resolving…</span>';
    const info = JSON.parse(mod.get_preset_dot(i));
    elDesc.innerHTML = info
      ? `<span class="lab">${esc(info.name)}</span>${esc(info.execution_summary || "")}`
      : "";
    steps = JSON.parse(mod.get_preset_steps(i));
    idx = 0;
    await render();
  }

  elPresets.addEventListener("change", (e) => selectPreset(+e.target.value));
  $("reset").addEventListener("click", () => { idx = 0; render(); });
  $("prev").addEventListener("click", () => { if (idx > 0) { idx--; render(); } });
  $("next").addEventListener("click", () => { if (idx < steps.length - 1) { idx++; render(); } });

  root.tabIndex = 0;
  root.addEventListener("keydown", (e) => {
    if (["ArrowRight", "ArrowDown"].includes(e.key) && idx < steps.length - 1) { idx++; render(); e.preventDefault(); }
    else if (["ArrowLeft", "ArrowUp"].includes(e.key) && idx > 0) { idx--; render(); e.preventDefault(); }
    else if (e.key === "Home") { idx = 0; render(); e.preventDefault(); }
    else if (e.key === "End") { idx = steps.length - 1; render(); e.preventDefault(); }
  });

  const start = Number.isInteger(opts.initialPreset) && opts.initialPreset < presets.length
    ? opts.initialPreset : 0;
  await selectPreset(start);
  return { selectPreset };
}
