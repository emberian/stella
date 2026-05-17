// explorer.js — the live stellar-resolution explorer.
//
// stella-core, compiled to wasm32, runs interactive execution (IEx) entirely
// in the browser. This module renders a constellation as it resolves — stars
// and rays, the redex that fires, the most general unifier — and also offers a
// dependency-graph view and a free-form editor. It is a tool; the reading on
// the model is static and stands without it.

// This module lives at /assets/explorer.js; the WASM bundle is /pkg/ and the
// vendored viz.js is /assets/vendor/.
const WASM_URL = new URL("../pkg/stella_viz_wasm.js", import.meta.url).href;
const VIZ_URL = new URL("./vendor/viz-standalone.js", import.meta.url).href;

let wasmReady = null;
let vizReady = null;

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

// viz.js is vendored locally (no CDN). It is only needed for the dep-graph
// view, so it is loaded lazily on first use.
function loadViz() {
  if (!vizReady) {
    vizReady = new Promise((resolve) => {
      if (window.Viz) return resolve(window.Viz);
      const s = document.createElement("script");
      s.src = VIZ_URL;
      s.onload = () => resolve(window.Viz || null);
      s.onerror = () => resolve(null);
      document.head.appendChild(s);
    }).then((V) => (V ? V.instance() : null)).catch(() => null);
  }
  return vizReady;
}

const esc = (s) =>
  String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

function rayPolarity(s) {
  const t = s.trim();
  if (t.startsWith("+")) return "pos";
  if (t.startsWith("-") || t.startsWith("−")) return "neg";
  return "neu";
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
  if (cur.trim() !== "" || parts.length) parts.push(cur);
  return parts.map((x) => x.trim()).filter((x) => x.length);
}

// "[a, b, c]" -> ["a","b","c"]
function parseStar(starStr) {
  const inner = starStr.replace(/^\s*\[/, "").replace(/\]\s*$/, "");
  return splitTopLevel(inner);
}

// Recolour Graphviz output into the Stella palette (CSS beats SVG attrs).
function styleSvg(svg) {
  const st = document.createElementNS("http://www.w3.org/2000/svg", "style");
  st.textContent = `
    text{fill:var(--ink);font-family:var(--font-mono),monospace;font-size:12px}
    ellipse,polygon,path{stroke:var(--bark)}
    ellipse{fill:var(--cream)}
    path{fill:none}
    polygon{fill:var(--bark)}
    .node polygon{fill:var(--cream)}`;
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

  <div class="stx-views" role="tablist">
    <button class="stx-viewbtn is-active" data-view="constellation" role="tab">Constellation</button>
    <button class="stx-viewbtn" data-view="depgraph" role="tab">Dependency graph</button>
    ${compact ? "" : '<button class="stx-viewbtn" data-view="editor" role="tab">Editor</button>'}
    <span class="stx-bar__spacer"></span>
    <a class="stx-permalink" data-role="permalink" href="#" title="Copy a link to this constellation">Permalink</a>
  </div>

  <div class="stx-stage" data-role="stage">
    <div class="stx-pane stx-pane--constellation is-active" data-pane="constellation">
      <div class="stx-canvas" data-role="canvas"></div>
      <div class="stx-readout">
        <div class="stx-mgu" data-role="mgu"></div>
        <div class="stx-redexes" data-role="redexes"></div>
      </div>
    </div>
    <div class="stx-pane" data-pane="depgraph">
      <div class="stx-graph" data-role="graph"></div>
    </div>
    ${compact ? "" : `
    <div class="stx-pane" data-pane="editor">
      <div class="stx-editor">
        <label>Reference constellation Φ
          <textarea data-role="phi" spellcheck="false" rows="4"></textarea></label>
        <label>Interaction space Ψ
          <textarea data-role="psi" spellcheck="false" rows="2"></textarea></label>
        <div class="stx-editor__row">
          <button class="st-btn st-btn--sm" data-role="run">Resolve ▸</button>
          <select class="stx-select stx-select--light" data-role="examples" aria-label="Load an example"></select>
          <span class="stx-error" data-role="error"></span>
        </div>
        <p class="stx-syntax">Syntax: <code>[+f(X), -g(X,a)] + [-f(Y), Y]</code> — uppercase = variable,
          <code>+</code>/<code>-</code> = polarity, <code>+</code> or newline separates stars.</p>
      </div>
    </div>`}
  </div>

  <div class="stx-controls">
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="reset" title="Step 0">↺</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="prev" title="Previous (←)">◂</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="play" title="Play / pause (space)">▶ Play</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="next" title="Next (→)">▸</button>
    <input type="range" class="stx-scrub" data-role="scrub" min="0" max="0" value="0" aria-label="Step" />
    <select class="stx-select stx-select--light" data-role="speed" aria-label="Speed">
      <option value="1400">0.5×</option><option value="750" selected>1×</option>
      <option value="380">2×</option><option value="160">4×</option>
    </select>
    <span class="step-readout" data-role="readout"></span>
  </div>
  <div class="stx-desc" data-role="desc"></div>
`;

const EXAMPLES = [
  { name: "Horn addition — 2 + 2",
    phi: "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
    psi: "[-add(s(s(0)), s(s(0)), R), R]" },
  { name: "Horn multiplication — 2 × 3",
    phi: "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))] + [+mul(0, Y, 0)] + [-mul(X, Y, Z), -add(Y, Z, W), +mul(s(X), Y, W)]",
    psi: "[-mul(s(s(0)), s(s(s(0))), R), R]" },
  { name: "Identity / self-interaction",
    phi: "[+f(X), -f(X)]",
    psi: "[-f(a), R] + [+f(a)]" },
  { name: "List membership",
    phi: "[+mem(X, cons(X, T))] + [-mem(X, T), +mem(X, cons(Y, T))]",
    psi: "[-mem(b, cons(a, cons(b, nil))), R]" },
];

export async function mountExplorer(root, opts = {}) {
  const compact = !!opts.compact;
  root.classList.add("st-explorer");
  if (compact) root.classList.add("st-explorer--inline");
  root.innerHTML = TEMPLATE(compact);
  const $ = (r) => root.querySelector(`[data-role="${r}"]`);

  const elPresets = $("presets"), elPulse = $("pulse"), elCanvas = $("canvas"),
    elMgu = $("mgu"), elRedex = $("redexes"), elGraph = $("graph"),
    elReadout = $("readout"), elDesc = $("desc"), elScrub = $("scrub"),
    elPlay = $("play"), elSpeed = $("speed");

  const mod = await loadWasm();
  elPulse.textContent = "engine ready";

  const presets = JSON.parse(mod.list_presets());
  elPresets.innerHTML = presets
    .map((p, i) => `<option value="${i}">${esc(p.name)}</option>`)
    .join("");

  let steps = [], idx = 0, presetIdx = -1, view = "constellation",
    playTimer = null, sourceMode = false, lastPhi = "", lastPsi = "";

  // ── view switching ─────────────────────────────────────────────────────────
  root.querySelectorAll(".stx-viewbtn").forEach((b) =>
    b.addEventListener("click", () => setView(b.dataset.view)));

  function setView(v) {
    view = v;
    root.querySelectorAll(".stx-viewbtn").forEach((b) =>
      b.classList.toggle("is-active", b.dataset.view === v));
    root.querySelectorAll(".stx-pane").forEach((p) =>
      p.classList.toggle("is-active", p.dataset.pane === v));
    if (v === "depgraph") drawGraph();
  }

  // ── constellation rendering ────────────────────────────────────────────────
  function rayHtml(ray, key) {
    return `<span class="stx-ray stx-ray--${rayPolarity(ray)}" data-k="${key}">${esc(ray)}</span>`;
  }

  function renderConstellation(animateFrom) {
    const snap = steps[idx];
    if (!snap) return;
    const fired = (steps[idx - 1] && steps[idx - 1].fireable || []).find((f) => f.is_next);
    const nextRedex = (snap.fireable || []).find((f) => f.is_next);

    const starsHtml = (snap.psi_stars.length
      ? snap.psi_stars
      : ["∅"]).map((starStr, si) => {
        if (starStr === "∅") {
          return `<div class="stx-star stx-star--empty">∅ — empty interaction space</div>`;
        }
        const rays = parseStar(starStr);
        const involved = nextRedex && nextRedex.star === si;
        const inner = rays.map((r, ri) => {
          const isHot = involved && nextRedex.ray === ri;
          return `<span class="stx-ray stx-ray--${rayPolarity(r)}${isHot ? " is-next" : ""}"
                    data-star="${si}" data-ray="${ri}">${esc(r)}</span>`;
        }).join('<span class="stx-comma">,</span>');
        return `<div class="stx-star${involved ? " is-active" : ""}"
                  data-star="${si}" style="--i:${si}">${inner}</div>`;
      }).join("");

    elCanvas.innerHTML = `<div class="stx-constellation${animateFrom != null ? " stx-anim" : ""}">${starsHtml}</div>`;

    // MGU readout — the unifier IEx will compute for the next firing.
    if (snap.mgu && snap.mgu.length && nextRedex) {
      const binds = snap.mgu
        .map(([v, t]) => `<span class="stx-bind"><span class="v">${esc(v)}</span>
            <span class="arr">↦</span><span class="t">${esc(t)}</span></span>`)
        .join("");
      elMgu.innerHTML =
        `<div class="stx-mgu__lab">Next: <code>${esc(nextRedex.ray_str)}</code> ` +
        `${nextRedex.kind === "self" ? "self-interacts" : "resolves against " + esc(nextRedex.targets[0] || "Φ")} ` +
        `· most general unifier</div><div class="stx-binds">${binds}</div>`;
    } else if (snap.is_final) {
      elMgu.innerHTML = `<div class="stx-mgu__lab stx-nf">Normal form — no interaction remains. This is the result.</div>`;
    } else {
      elMgu.innerHTML = "";
    }

    // All redexes — concurrency made visible.
    const fr = snap.fireable || [];
    if (fr.length) {
      elRedex.innerHTML =
        `<div class="stx-redex__lab">${fr.length} redex${fr.length > 1 ? "es" : ""} available · ` +
        `IEx fires the first (left-to-right). Hover to locate.</div>` +
        fr.map((f, k) =>
          `<button class="stx-chip${f.is_next ? " is-next" : ""}" data-fk="${k}">
             <code>${esc(f.ray_str)}</code>
             <span class="stx-chip__t">${f.kind === "self" ? "self" : esc(f.targets.join(", "))}</span>
           </button>`).join("");
      elRedex.querySelectorAll(".stx-chip").forEach((c) => {
        const f = fr[+c.dataset.fk];
        const hl = (on) => {
          const sel = root.querySelector(
            `.stx-ray[data-star="${f.star}"][data-ray="${f.ray}"]`);
          if (sel) sel.classList.toggle("is-hover", on);
        };
        c.addEventListener("mouseenter", () => hl(true));
        c.addEventListener("mouseleave", () => hl(false));
      });
    } else {
      elRedex.innerHTML = "";
    }
  }

  async function drawGraph() {
    const snap = steps[idx];
    if (!snap) return;
    if (!snap.dot || snap.dot.includes("// empty")) {
      elGraph.innerHTML = '<span class="reader-status">Ψ is empty — no stars.</span>';
      return;
    }
    elGraph.innerHTML = '<span class="reader-status">Rendering…</span>';
    const viz = await loadViz();
    if (!viz) { elGraph.innerHTML = `<pre>${esc(snap.dot)}</pre>`; return; }
    try {
      const svg = await viz.renderSVGElement(snap.dot);
      styleSvg(svg);
      elGraph.innerHTML = "";
      elGraph.appendChild(svg);
    } catch (_) {
      elGraph.innerHTML = `<pre>${esc(snap.dot)}</pre>`;
    }
  }

  function render(animate) {
    if (!steps.length) return;
    const snap = steps[idx];
    renderConstellation(animate);
    if (view === "depgraph") drawGraph();
    elScrub.max = String(steps.length - 1);
    elScrub.value = String(idx);
    $("prev").disabled = idx <= 0;
    $("next").disabled = idx >= steps.length - 1;
    const name = sourceMode ? "source" : (presets[presetIdx]?.name ?? "");
    elReadout.innerHTML =
      `${esc(name)} — step ${idx} / ${steps.length - 1}` +
      (snap.is_final ? ' <span class="nf">· normal form</span>' : "");
  }

  function go(to, animate) {
    idx = Math.max(0, Math.min(steps.length - 1, to));
    render(animate);
    if (idx >= steps.length - 1) stop();
  }

  // ── playback ───────────────────────────────────────────────────────────────
  function stop() {
    if (playTimer) { clearInterval(playTimer); playTimer = null; }
    elPlay.innerHTML = "▶ Play";
  }
  function play() {
    if (steps.length < 2 || idx >= steps.length - 1) { go(0); }
    elPlay.innerHTML = "❚❚ Pause";
    playTimer = setInterval(() => {
      if (idx >= steps.length - 1) return stop();
      go(idx + 1, idx);
    }, +elSpeed.value);
  }
  elPlay.addEventListener("click", () => (playTimer ? stop() : play()));
  elSpeed.addEventListener("change", () => { if (playTimer) { stop(); play(); } });
  $("reset").addEventListener("click", () => { stop(); go(0); });
  $("prev").addEventListener("click", () => { stop(); go(idx - 1); });
  $("next").addEventListener("click", () => { stop(); go(idx + 1, idx); });
  elScrub.addEventListener("input", () => { stop(); go(+elScrub.value); });

  root.tabIndex = 0;
  root.addEventListener("keydown", (e) => {
    if (e.target.tagName === "TEXTAREA" || e.target.tagName === "SELECT") return;
    if (e.key === "ArrowRight") { stop(); go(idx + 1, idx); e.preventDefault(); }
    else if (e.key === "ArrowLeft") { stop(); go(idx - 1); e.preventDefault(); }
    else if (e.key === " ") { playTimer ? stop() : play(); e.preventDefault(); }
    else if (e.key === "Home") { stop(); go(0); e.preventDefault(); }
    else if (e.key === "End") { stop(); go(steps.length - 1); e.preventDefault(); }
  });

  // ── loading a trace ────────────────────────────────────────────────────────
  async function loadPreset(i) {
    stop();
    sourceMode = false;
    presetIdx = i;
    elPresets.value = String(i);
    const info = JSON.parse(mod.get_preset_dot(i));
    elDesc.innerHTML = info
      ? `<span class="lab">${esc(info.name)}</span>${esc(info.execution_summary || "")}`
      : "";
    steps = JSON.parse(mod.get_preset_steps(i));
    go(0);
    updatePermalink();
  }

  function runSource(phi, psi) {
    stop();
    const elErr = $("error");
    if (elErr) elErr.textContent = "";
    let res;
    try { res = JSON.parse(mod.run_source(phi, psi)); }
    catch (e) { if (elErr) elErr.textContent = "engine error: " + e.message; return; }
    if (!res.ok) {
      if (elErr) elErr.textContent = `${res.where} parse error (pos ${res.pos}): ${res.error}`;
      return;
    }
    sourceMode = true;
    lastPhi = phi; lastPsi = psi;
    steps = res.steps;
    elDesc.innerHTML = `<span class="lab">source</span>Φ = <code>${esc(phi)}</code> · Ψ = <code>${esc(psi)}</code>`;
    go(0);
    updatePermalink();
  }

  if (!compact) {
    const elEx = $("examples");
    elEx.innerHTML = `<option value="">Load an example…</option>` +
      EXAMPLES.map((e, i) => `<option value="${i}">${esc(e.name)}</option>`).join("");
    elEx.addEventListener("change", () => {
      const e = EXAMPLES[+elEx.value];
      if (e) { $("phi").value = e.phi; $("psi").value = e.psi; }
    });
    $("run").addEventListener("click", () =>
      runSource($("phi").value.trim(), $("psi").value.trim()));
  }

  // ── permalink / deep links ─────────────────────────────────────────────────
  function updatePermalink() {
    const u = new URL(location.href);
    u.search = "";
    if (sourceMode) {
      u.searchParams.set("phi", lastPhi);
      u.searchParams.set("psi", lastPsi);
    } else {
      u.searchParams.set("preset", String(presetIdx));
    }
    const a = $("permalink");
    if (a) a.href = u.toString();
    history.replaceState(null, "", u.toString());
  }
  const pl = $("permalink");
  if (pl) pl.addEventListener("click", (e) => {
    e.preventDefault();
    navigator.clipboard?.writeText(pl.href).then(() => {
      pl.textContent = "Copied"; setTimeout(() => (pl.textContent = "Permalink"), 1400);
    });
  });

  elPresets.addEventListener("change", (e) => loadPreset(+e.target.value));

  // initial: ?phi=&psi= | ?preset=<idx|name substring> | opts | first preset
  const q = new URLSearchParams(location.search);
  const qPhi = q.get("phi"), qPsi = q.get("psi"), qPreset = q.get("preset");
  if (qPhi != null && !compact) {
    setView("editor");
    $("phi").value = qPhi; $("psi").value = qPsi || "";
    runSource(qPhi.trim(), (qPsi || "").trim());
  } else if (qPreset != null) {
    let i = parseInt(qPreset, 10);
    if (Number.isNaN(i)) {
      i = presets.findIndex((p) =>
        p.name.toLowerCase().includes(qPreset.toLowerCase()));
    }
    await loadPreset(i >= 0 && i < presets.length ? i : 0);
  } else {
    await loadPreset(
      Number.isInteger(opts.initialPreset) && opts.initialPreset < presets.length
        ? opts.initialPreset : 0);
  }
  return { loadPreset };
}
