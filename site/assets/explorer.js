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

// The Stella visual kit — star-and-ray glyphs, fields, verdict chips,
// closure + proof-structure plates. Renders exact engine output; no inference.
import * as DGM from "./diagram.js";
// Schema-driven structured spec editor (form-primary, raw-JSON round-trip).
import { SpecForm } from "./specform.js";

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

// Tokenize the surface syntax into highlighted HTML (no dependency).
function tokenizeStella(src) {
  let out = "";
  const re =
    /(#[^\n]*)|([\[\]()])|([+\-−](?=[A-Za-z_]))|([,;])|([A-Za-z_$.][\w$.'\-]*|ε|□|★)|(\s+)|([^\s])/g;
  let m;
  while ((m = re.exec(src))) {
    if (m[1]) out += `<span class="tk-c">${esc(m[1])}</span>`;
    else if (m[2]) out += `<span class="tk-b">${esc(m[2])}</span>`;
    else if (m[3]) out += `<span class="tk-p">${esc(m[3])}</span>`;
    else if (m[4]) out += `<span class="tk-s">${esc(m[4])}</span>`;
    else if (m[5]) {
      const cls = /^[A-Z]/.test(m[5]) ? "tk-v" : "tk-f";
      out += `<span class="${cls}">${esc(m[5])}</span>`;
    } else if (m[6]) out += esc(m[6]);
    else out += esc(m[7]);
  }
  return out;
}

// Turn a <textarea> into a syntax-highlighted code field with a line-number
// gutter and an error-line marker. A transparent textarea sits over a
// highlighted <pre>; metrics are pinned identical in CSS.
function enhanceField(ta, onInput) {
  const code = document.createElement("div");
  code.className = "stx-code";
  const gutter = document.createElement("div");
  gutter.className = "stx-gutter";
  gutter.setAttribute("aria-hidden", "true");
  const wrap = document.createElement("div");
  wrap.className = "stx-wrap";
  const pre = document.createElement("pre");
  pre.className = "stx-hl";
  pre.setAttribute("aria-hidden", "true");
  const codeEl = document.createElement("code");
  pre.appendChild(codeEl);
  ta.parentNode.insertBefore(code, ta);
  wrap.appendChild(pre);
  wrap.appendChild(ta);
  code.appendChild(gutter);
  code.appendChild(wrap);

  let errLine = -1;
  const refresh = () => {
    const v = ta.value;
    codeEl.innerHTML = tokenizeStella(v) + "\n";
    const lines = v.split("\n").length;
    let g = "";
    for (let i = 1; i <= lines; i++) {
      g += `<div class="${i - 1 === errLine ? "is-err" : ""}">${i}</div>`;
    }
    gutter.innerHTML = g;
    // auto-grow
    ta.style.height = "auto";
    ta.style.height = ta.scrollHeight + "px";
    pre.style.height = ta.style.height;
  };
  ta.addEventListener("input", () => { refresh(); onInput && onInput(); });
  ta.addEventListener("scroll", () => {
    codeEl.style.transform = `translateX(${-ta.scrollLeft}px)`;
  });
  ta.addEventListener("keydown", (e) => {
    if (e.key === "Tab") {
      e.preventDefault();
      const s = ta.selectionStart, en = ta.selectionEnd;
      ta.value = ta.value.slice(0, s) + "  " + ta.value.slice(en);
      ta.selectionStart = ta.selectionEnd = s + 2;
      refresh(); onInput && onInput();
    } else if (e.key === "(" || e.key === "[") {
      const close = e.key === "(" ? ")" : "]";
      const s = ta.selectionStart, en = ta.selectionEnd;
      if (s === en) {
        e.preventDefault();
        ta.value = ta.value.slice(0, s) + e.key + close + ta.value.slice(en);
        ta.selectionStart = ta.selectionEnd = s + 1;
        refresh(); onInput && onInput();
      }
    }
  });
  return {
    refresh,
    setValue(v) { ta.value = v; refresh(); },
    markError(line) { errLine = line; refresh(); },
    clearError() { if (errLine !== -1) { errLine = -1; refresh(); } },
  };
}

// Inline (primer) widget — unchanged minimal layout.
const TEMPLATE_INLINE = `
  <div class="stx-bar">
    <span class="stx-bar__title"><img src="assets/stella/glyphs/star.svg" alt="" />
      Stellar resolution — interactive execution</span>
    <span class="stx-bar__spacer"></span>
    <span class="st-pulse" data-role="pulse">starting engine</span>
    <select class="stx-select" data-role="presets" aria-label="Choose a constellation"></select>
  </div>
  <div class="stx-views" role="tablist">
    <button class="stx-viewbtn is-active" data-view="constellation" role="tab">Constellation</button>
    <button class="stx-viewbtn" data-view="depgraph" role="tab">Dependency graph</button>
    <span class="stx-bar__spacer"></span>
    <a class="stx-permalink" data-role="permalink" href="#">Permalink</a>
  </div>
  <div class="stx-stage" data-role="stage">
    <div class="stx-pane stx-pane--constellation is-active" data-pane="constellation">
      <div class="stx-canvas" data-role="canvas"></div>
      <div class="stx-readout">
        <div class="stx-mgu" data-role="mgu"></div>
        <div class="stx-redexes" data-role="redexes"></div>
      </div>
    </div>
    <div class="stx-pane" data-pane="depgraph"><div class="stx-graph" data-role="graph"></div></div>
  </div>
  <div class="stx-controls">
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="reset" title="Step 0">↺</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="prev" title="Previous (←)">◂</button>
    <button class="st-btn st-btn--secondary st-btn--sm" data-role="play" title="Play / pause">▶ Play</button>
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

// Full educational IDE: a library rail, a syntax-highlighted editor, a live
// constellation, and an inspector — all on one screen.
const TEMPLATE_IDE = `
  <div class="stx-bar">
    <span class="stx-bar__title"><img src="assets/stella/glyphs/star.svg" alt="" />
      Stellar resolution — a playground</span>
    <span class="stx-bar__spacer"></span>
    <span class="st-pulse" data-role="pulse">starting engine</span>
    <select class="stx-select" data-role="ws" title="Saved workspaces"></select>
    <button class="stx-iconbtn" data-role="wssave" title="Save the current Φ/Ψ as a named workspace">save</button>
    <button class="stx-iconbtn" data-role="wsdel" title="Delete the selected workspace" hidden>del</button>
    <button class="stx-iconbtn" data-role="wsexport" title="Export all workspaces as JSON">export</button>
    <button class="stx-iconbtn" data-role="wsimport" title="Import workspaces JSON">import</button>
    <input type="file" data-role="wsfile" accept="application/json" hidden />
    <button class="stx-iconbtn" data-role="construct" title="Build a constellation from a machine / proof spec">＋ build</button>
    <button class="stx-iconbtn" data-role="logic" title="Orthogonality, behaviours, proof-net correctness">⊥ logic</button>
    <button class="stx-iconbtn" data-role="copytrace" title="Copy the whole step-by-step trace">⧉ trace</button>
    <a class="stx-permalink" data-role="permalink" href="#" title="Copy a sharable link">↪ share</a>
  </div>

  <div class="stx-modal" data-role="cpanel" hidden>
    <div class="stx-modal__box">
      <div class="stx-modal__head">
        <span>Construct a constellation</span>
        <select class="stx-select stx-select--light" data-role="cclass" aria-label="Machine class">
          <option value="nfa">NFA — finite automaton</option>
          <option value="npda">NPDA — pushdown automaton</option>
          <option value="ntm">NTM — Turing machine</option>
          <option value="atm">ATM — alternating TM</option>
          <option value="nfta">NFTA — tree automaton</option>
          <option value="nfst">NFST — transducer</option>
          <option value="circuit">Boolean circuit (Ex)</option>
          <option value="tiles">Tile assembly (Ex)</option>
          <option value="mll">MLL proof structure (Ex)</option>
          <option value="mll2i">MLL2I proof structure (Ex)</option>
        </select>
        <span class="stx-bar__spacer"></span>
        <button class="stx-iconbtn" data-role="cclose">✕</button>
      </div>
      <div class="sf-split">
        <div class="sf-host" data-role="cform"></div>
        <div class="sf-preview" data-role="cprev"><span class="sf-preview__lab">live preview</span></div>
      </div>
      <div class="stx-modal__row">
        <button class="st-btn st-btn--sm" data-role="cbuild">Build → editor&nbsp;<span class="stx-kbd">⌘↵</span></button>
        <button class="st-btn st-btn--secondary st-btn--sm" data-role="cexample">Load example</button>
        <span class="stx-error" data-role="cerr"></span>
        <span class="stx-bar__spacer"></span>
        <span class="stx-syntax">The encoder is Eng-faithful; the result is editable source.</span>
      </div>
    </div>
  </div>

  <div class="stx-modal" data-role="lpanel" hidden>
    <div class="stx-modal__box">
      <div class="stx-modal__head">
        <span>Logic workbench</span>
        <select class="stx-select stx-select--light" data-role="lclass" aria-label="Tool">
          <option value="ortho">Orthogonality — Φ₁ ⊥ Φ₂</option>
          <option value="proofnet">Proof net — correctness + Φ_comp</option>
          <option value="behaviour">Behaviour / type — A^⊥⊥</option>
          <option value="compare">Compare — same result? ω delta</option>
        </select>
        <span class="stx-bar__spacer"></span>
        <button class="stx-iconbtn" data-role="lclose">✕</button>
      </div>
      <div class="sf-split">
        <div class="sf-host" data-role="lform"></div>
        <div class="sf-preview" data-role="lprev"><span class="sf-preview__lab">live preview</span></div>
      </div>
      <div class="stx-modal__row">
        <button class="st-btn st-btn--sm" data-role="lrun">Run&nbsp;<span class="stx-kbd">⌘↵</span></button>
        <button class="st-btn st-btn--secondary st-btn--sm" data-role="lexample">Load example</button>
        <button class="st-btn st-btn--secondary st-btn--sm" data-role="lload" hidden>Φ_comp → editor</button>
        <span class="stx-error" data-role="lerr"></span>
        <span class="stx-bar__spacer"></span>
        <span class="stx-syntax">A type is a behaviour; membership is orthogonality; proofs validated by the stellar/DR/Girard criterion.</span>
      </div>
      <div class="stx-lout" data-role="lout"></div>
    </div>
  </div>

  <div class="stx-ide">
    <aside class="stx-rail" data-role="lib" aria-label="Example library"></aside>

    <section class="stx-work">
      <div class="stx-edit">
        <div class="stx-edit__head"><span>Reference constellation Φ — the rules</span>
          <span class="stx-validity" data-role="validity"></span></div>
        <textarea data-role="phi" class="stx-ta" spellcheck="false" wrap="off"
          autocapitalize="off" autocomplete="off"
          placeholder="[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]"></textarea>
        <div class="stx-edit__head"><span>Interaction space Ψ — the query</span></div>
        <textarea data-role="psi" class="stx-ta" spellcheck="false" wrap="off"
          autocapitalize="off" autocomplete="off"
          placeholder="[-add(s(s(0)), s(s(0)), R), R]"></textarea>
        <div class="stx-edit__row">
          <button class="st-btn st-btn--sm" data-role="run">Resolve&nbsp;▸<span class="stx-kbd">⌘⏎</span></button>
          <button class="st-btn st-btn--secondary st-btn--sm" data-role="fork"
            title="Snip the current state back into the editor" hidden>⑂ Fork here</button>
          <span class="stx-bar__spacer"></span>
          <a class="stx-syntax-link" href="r/notation.html" target="_blank" rel="noopener">notation ↗</a>
        </div>
        <p class="stx-syntax" data-role="hint">Uppercase = variable · <code>+</code>/<code>-</code> = polarity ·
          <code>+</code> or newline separates stars · ⌘⏎ to resolve</p>
      </div>

      <div class="stx-out">
        <div class="stx-views" role="tablist">
          <button class="stx-viewbtn is-active" data-view="constellation" role="tab">Constellation</button>
          <button class="stx-viewbtn" data-view="depgraph" role="tab">Dependency graph</button>
          <button class="stx-viewbtn" data-view="exsem" role="tab" title="The strategy-independent result (Ex), vs the exact IEx path">Ex semantics</button>
          <span class="stx-bar__spacer"></span>
          <span class="step-readout" data-role="readout"></span>
        </div>
        <div class="stx-stage" data-role="stage">
          <div class="stx-pane stx-pane--constellation is-active" data-pane="constellation">
            <div class="stx-canvas" data-role="canvas"></div>
            <div class="stx-readout">
              <div class="stx-mgu" data-role="mgu"></div>
              <div class="stx-obs" data-role="obs"></div>
              <div class="stx-redexes" data-role="redexes"></div>
            </div>
          </div>
          <div class="stx-pane" data-pane="depgraph"><div class="stx-graph" data-role="graph"></div></div>
          <div class="stx-pane" data-pane="exsem">
            <div class="stx-ex">
              <div class="stx-ex__bar">
                <span class="stx-ex__lab">Concrete execution at copy budget</span>
                <label class="stx-fuel">k <input type="number" data-role="exk" min="1" max="12" step="1" value="2" /></label>
                <button class="st-btn st-btn--sm" data-role="excompute">Compute Ex</button>
                <span class="stx-ex__hint">Φ is non-linear; CEx needs ≥k fresh copies. Raise k until it meets the exact IEx ɟ. Note: CEx saturation is exponential for recursive Φ — keep k small.</span>
              </div>
              <div class="stx-ex__body" data-role="exbody">
                <p class="reader-status">Press <em>Compute Ex</em> — this runs the engine's concrete execution (synchronous; bounded by k).</p>
              </div>
            </div>
          </div>
        </div>
        <div class="stx-controls">
          <button class="st-btn st-btn--secondary st-btn--sm" data-role="reset" title="Step 0 (Home)">↺</button>
          <button class="st-btn st-btn--secondary st-btn--sm" data-role="prev" title="Previous (←)">◂</button>
          <button class="st-btn st-btn--secondary st-btn--sm" data-role="play" title="Play / pause (space)">▶ Play</button>
          <button class="st-btn st-btn--secondary st-btn--sm" data-role="next" title="Next (→)">▸</button>
          <input type="range" class="stx-scrub" data-role="scrub" min="0" max="0" value="0" aria-label="Step" />
          <select class="stx-select stx-select--light" data-role="speed" aria-label="Speed">
            <option value="1400">0.5×</option><option value="750" selected>1×</option>
            <option value="380">2×</option><option value="160">4×</option>
          </select>
          <label class="stx-fuel" title="Max resolution steps before the engine stops (for non-terminating constellations)">
            fuel <input type="number" data-role="fuel" min="1" max="20000" step="50" value="300" /></label>
        </div>
      </div>
    </section>
  </div>
  <div class="stx-desc" data-role="desc"></div>
  <select data-role="presets" hidden></select>
`;

const TEMPLATE = (compact) => (compact ? TEMPLATE_INLINE : TEMPLATE_IDE);

// The example library — the editable, pedagogical core. Each entry has a
// note pointing at *what to watch for*.
// Worked, valid spec templates for the construction lab (also documentation).
const CSPEC = {
  nfa: `{
  "states": ["q0","q1","q2"],
  "alphabet": ["0","1"],
  "initial": ["q0"],
  "finals": ["q2"],
  "transitions": [
    ["q0","0","q0"], ["q0","1","q0"],
    ["q0","0","q1"], ["q1","0","q2"]
  ],
  "word": ["0","0","0"]
}`,
  npda: `{
  "states": ["q0","q1"],
  "alphabet": ["0","1"],
  "stack_alphabet": ["Z","0"],
  "initial": ["q0"],
  "finals": ["q1"],
  "transitions": [
    ["q0","0",null,"q0","0"],
    ["q0","1","0","q1",null],
    ["q1","1","0","q1",null]
  ],
  "word": ["0","1"]
}`,
  ntm: `{
  "states": ["q0","qa","qr"],
  "gamma": ["0","1","blank"],
  "delta": [["q0","blank","qa","blank","S"]],
  "q0": "q0", "q_accept": "qa", "q_reject": "qr",
  "input": []
}`,
  atm: `{
  "states": ["q0","qa","qr"],
  "gamma": ["0","1","blank"],
  "delta": [["q0","blank","qa","blank","S"]],
  "q0": "q0", "q_accept": "qa", "q_reject": "qr",
  "class": { "q0": "E" },
  "input": []
}`,
  nfta: `{
  "states": ["q1","qb"],
  "initial": ["q1"],
  "rules": [
    {"state":"q1","symbol":"or","successors":["q1","q1"]},
    {"state":"q1","symbol":"not","successors":["q1"]}
  ],
  "leaf_states": ["q1"],
  "terminal_pairs": [["q1","1"],["q1","0"]],
  "tree": {"node":["or",[{"node":["not",[{"leaf":"1"}]]},{"leaf":"1"}]]}
}`,
  nfst: `{
  "states": ["q0","q1"],
  "alphabet": ["a","b"],
  "output_alphabet": ["a","b"],
  "initial": ["q0"],
  "finals": ["q1"],
  "transitions": [
    ["q0","a","q0","a"],
    ["q0","b","q1","b"]
  ],
  "word": ["a","b"]
}`,
  circuit: `{
  "gates": [
    {"label":"1","inputs":[],"outputs":["a"]},
    {"label":"1","inputs":[],"outputs":["b"]},
    {"label":"∧","inputs":["a","b"],"outputs":["c"]},
    {"label":"c","inputs":["c"],"outputs":["z"],"is_output":true}
  ]
}`,
  tiles: `{
  "tile_types": [
    {"label":"A","glue_w":"aw","glue_e":"ae","glue_s":"as","glue_n":"an","strengths":[1,1,1,1]}
  ],
  "tau": 1,
  "positions": ["p0"]
}`,
  mll: `{
  "links": [
    {"kind":"ax","left":0,"right":1},
    {"kind":"ax","left":2,"right":3},
    {"kind":"cut","left":1,"right":2}
  ]
}`,
  mll2i: `{
  "links": [
    {"kind":"ax","left":0,"right":1},
    {"kind":"ax","left":2,"right":3},
    {"kind":"cut","left":1,"right":2}
  ]
}`,
};

// Worked templates for the Logic workbench.
const LSPEC = {
  ortho: `{
  "phi1": "[+a(X)]",
  "phi2": "[-a(X), R]"
}`,
  proofnet: `{
  "kind": "mll",
  "links": [
    {"kind":"ax","left":0,"right":1}
  ]
}`,
  behaviour: `{
  "members": ["[+a(X)]"],
  "universe": ["[+a(X)]", "[-a(X), R]"],
  "orth": "roots"
}`,
  compare: `{
  "phiA": "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
  "psiA": "[-add(s(0), s(0), R), R]",
  "phiB": "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
  "psiB": "[-add(s(s(0)), 0, R), R]"
}`,
};

const LIBRARY = [
  { group: "Logic programming", items: [
    { name: "Addition — 2 + 2", note: "Peano addition; watch the request peel one s each step.",
      phi: "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
      psi: "[-add(s(s(0)), s(s(0)), R), R]" },
    { name: "Multiplication — 2 × 3", note: "mul calls add — nested resolution.",
      phi: "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))] + [+mul(0, Y, 0)] + [-mul(X, Y, Z), -add(Y, Z, W), +mul(s(X), Y, W)]",
      psi: "[-mul(s(s(0)), s(s(s(0))), R), R]" },
    { name: "List membership", note: "Backtracking-free search down a list.",
      phi: "[+mem(X, cons(X, T))] + [-mem(X, T), +mem(X, cons(Y, T))]",
      psi: "[-mem(b, cons(a, cons(b, nil))), R]" },
    { name: "List append", note: "The classic relational append.",
      phi: "[+app(nil, Y, Y)] + [-app(X, Y, Z), +app(cons(H, X), Y, cons(H, Z))]",
      psi: "[-app(cons(a, cons(b, nil)), cons(c, nil), R), R]" },
    { name: "Even / odd", note: "Mutual recursion across two predicates.",
      phi: "[+even(0)] + [-odd(X), +even(s(X))] + [-even(X), +odd(s(X))]",
      psi: "[-even(s(s(s(s(0))))), R] + [-odd(s(s(s(0)))), S]" },
  ]},
  { group: "Concurrency & non-determinism", items: [
    { name: "Two queries, two redexes", note: "Two independent requests — pick which fires.",
      phi: "[+add(0, Y, Y)] + [-add(X, Y, Z), +add(s(X), Y, s(Z))]",
      psi: "[-add(s(0), s(0), R), R] + [-add(s(s(0)), 0, S), S]" },
    { name: "Self-interaction", note: "A star resolves against itself.",
      phi: "[+f(X), -f(X)]", psi: "[-f(a), R] + [+f(a)]" },
    { name: "Divergence", note: "No normal form — the engine caps at 300 steps.",
      phi: "[+f(X), -f(X)]", psi: "[-f(a)]" },
  ]},
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
    playTimer = null, sourceMode = false, lastPhi = "", lastPsi = "",
    choicePath = [], // chosen (star,ray) per step; [] = pure IEx order
    phiEd = null, psiEd = null; // code-editor handles (set in IDE wiring)

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

    const isFinal = !!snap.is_final;
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
          // At normal form the surviving unpolarised rays *are* the answer.
          const isResult = isFinal && rayPolarity(r) === "neu";
          return `<span class="stx-ray stx-ray--${rayPolarity(r)}${isHot ? " is-next" : ""}${isResult ? " is-result" : ""}"
                    data-star="${si}" data-ray="${ri}">${esc(r)}</span>`;
        }).join('<span class="stx-comma">,</span>');
        return `<div class="stx-star${involved ? " is-active" : ""}"
                  data-star="${si}" style="--i:${si}">${inner}</div>`;
      }).join("");

    elCanvas.innerHTML = `<div class="stx-constellation${animateFrom != null ? " stx-anim" : ""}">${starsHtml}</div>`;

    // ɟ(Ψ): the engine's own observable output (conceal+noise filter,
    // §49.44) — authoritative, computed in stella-core, not client-side.
    const elObs = $("obs");
    if (elObs) {
      const obs = snap.observable || [];
      const body = obs.length
        ? obs.map((s) => `<span class="stx-obs__s">${esc(s)}</span>`).join("")
        : `<span class="stx-obs__none">∅ — nothing observable yet</span>`;
      elObs.innerHTML =
        `<span class="stx-obs__lab" title="ɟ = conceal ↨ + noise filter ♭ (Eng §49.44), computed by stella-core">ɟ(Ψ)${isFinal ? " — the result" : ""}</span>${body}`;
      elObs.classList.toggle("is-final", isFinal);
    }

    // The EXACT §51.9 decomposition: one step fires a *sum* of summands,
    // each with the real θ the engine applied (authoritative, not
    // reconstructed). Fall back to the single-mgu phrasing only if the
    // exact summands are absent (the primer's fuel-replay capture).
    const sums = snap.summands || [];
    if (sums.length && nextRedex) {
      const plural = sums.length > 1;
      const head =
        `<div class="stx-mgu__lab">The ray <code>${esc(nextRedex.ray_str)}</code> fires a ` +
        `${plural ? `<strong>sum of ${sums.length} summands</strong> (§51.9)` : "single interaction"} — ` +
        `each with the exact unifier <code>stella-core</code> applied:</div>`;
      const blocks = sums.map((s) => {
        const binds = s.theta.length
          ? s.theta.map(([v, t]) =>
              `<span class="stx-bind"><span class="v">${esc(v)}</span>` +
              `<span class="arr">↦</span><span class="t">${esc(t)}</span></span>`).join("")
          : `<span class="stx-bind stx-bind--id">θ = identity</span>`;
        const tgt = s.external
          ? `fusion against <code>${esc(s.target)}</code>`
          : `self-interaction (<code>${esc(s.target)}</code>)`;
        return `<div class="stx-summand"><span class="stx-summand__t">${tgt}</span>` +
               `<div class="stx-binds">${binds}</div></div>`;
      }).join("");
      elMgu.innerHTML = head + blocks;
    } else if (snap.mgu && snap.mgu.length && nextRedex) {
      const binds = snap.mgu
        .map(([v, t]) => `<span class="stx-bind"><span class="v">${esc(v)}</span>
            <span class="arr">↦</span><span class="t">${esc(t)}</span></span>`)
        .join("");
      const how = nextRedex.kind === "self"
        ? `self-interacts (two rays of the same star unify)`
        : `unifies with <code>${esc(nextRedex.targets[0] || "Φ")}</code> in the reference Φ`;
      elMgu.innerHTML =
        `<div class="stx-mgu__lab">The ray <code>${esc(nextRedex.ray_str)}</code> ${how} — ` +
        `the stars fuse, the matched pair is consumed, θ is applied to the rest.</div>` +
        `<div class="stx-binds">${binds}</div>`;
    } else if (isFinal) {
      elMgu.innerHTML =
        `<div class="stx-mgu__lab stx-nf">Normal form — no pair is matchable. ` +
        `The highlighted unpolarised rays are the result.</div>`;
    } else {
      elMgu.innerHTML = "";
    }

    // All redexes — concurrency made visible; clickable to branch in the editor.
    const fr = snap.fireable || [];
    const crumb = (sourceMode && choicePath.length)
      ? `<div class="stx-crumb">Path: ` +
        choicePath.map((c, i) =>
          `<span class="stx-crumb__c">${i}:[${c[0]},${c[1]}]</span>`).join("→") +
        ` <button class="stx-crumb__reset" data-role="resetpath">↺ IEx order</button></div>`
      : "";
    if (fr.length) {
      const can = sourceMode;
      elRedex.innerHTML = crumb +
        `<div class="stx-redex__lab">${fr.length} redex${fr.length > 1 ? "es" : ""} available — ` +
        (can
          ? `click one to resolve <em>it</em> next and follow that path.`
          : `IEx fires the first (left-to-right). Hover to locate; open the Editor to choose.`) +
        `</div>` +
        fr.map((f, k) =>
          `<button class="stx-chip${f.is_next ? " is-next" : ""}${can ? " stx-chip--pick" : ""}" data-fk="${k}">
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
        if (can) c.addEventListener("click", () => chooseRedex(f));
      });
    } else {
      elRedex.innerHTML = crumb;
    }
    // The path breadcrumb (and its reset) can appear in either branch —
    // including at the final step, where there are no redexes.
    const rp = elRedex.querySelector('[data-role="resetpath"]');
    if (rp) rp.addEventListener("click", () => {
      stop(); choicePath = []; runPath(lastPhi, lastPsi, 0);
    });
  }

  // Branch: resolve the clicked redex at the current step, then continue.
  function chooseRedex(f) {
    stop();
    choicePath = choicePath.slice(0, idx);
    choicePath[idx] = [f.star, f.ray];
    runPath(lastPhi, lastPsi, idx + 1);
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
    const fk = $("fork");
    if (fk) fk.hidden = !sourceMode;
    const name = sourceMode ? "source" : (presets[presetIdx]?.name ?? "");
    elReadout.innerHTML =
      `<span class="stx-strat" title="IEx with a left-to-right strategy; each successor Ψ is exact (the engine's own θ). The normal form is strategy-independent — choose any redex to verify.">IEx · exact</span> ` +
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
  { const fk = $("fork"); if (fk) fk.addEventListener("click", forkFromHere); }
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

  // Run the source along the current choicePath ([] = pure IEx), then view
  // step `gotoIdx`. The engine's capture_path takes the chosen redex where
  // the path names one and the IEx default elsewhere.
  // ── editor feedback (live validity + a caret code-frame) ───────────────────
  function setValidity(ok, msg) {
    const v = $("validity");
    if (!v) return;
    v.className = "stx-validity " + (ok ? "is-ok" : "is-err");
    v.textContent = msg;
  }
  // pos is a byte/char offset into the *trimmed* source the parser saw.
  function lineOf(src, pos) {
    const s = (src || "").trimStart();
    const p = Math.max(0, Math.min(pos | 0, s.length));
    let line = 0;
    for (let i = 0; i < p; i++) if (s[i] === "\n") line++;
    return line;
  }
  function clearFrame() { phiEd && phiEd.clearError(); psiEd && psiEd.clearError(); }
  function showParseError(res, phi, psi) {
    setValidity(false, `✗ ${res.where} · ${res.error}`);
    const onPsi = res.where === "Ψ";
    const ed = onPsi ? psiEd : phiEd;
    const other = onPsi ? phiEd : psiEd;
    other && other.clearError();
    ed && ed.markError(lineOf(onPsi ? psi : phi, res.pos));
  }

  function runPath(phi, psi, gotoIdx) {
    stop();
    const pathStr = choicePath
      .filter(Boolean)
      .map((c) => `${c[0]},${c[1]}`)
      .join(";");
    let res;
    try { res = JSON.parse(mod.run_path(phi, psi, pathStr, fuelVal())); }
    catch (e) { setValidity(false, "engine error: " + e.message); return false; }
    if (!res.ok) {
      showParseError(res, phi, psi);
      return false;
    }
    setValidity(true, "✓ resolved");
    clearFrame();
    sourceMode = true;
    lastPhi = phi; lastPsi = psi;
    steps = res.steps;
    const branched = choicePath.filter(Boolean).length
      ? ` · <span class="stx-branched">chosen path</span>` : "";
    elDesc.innerHTML =
      `<span class="lab">source</span>Φ = <code>${esc(phi)}</code> · Ψ = <code>${esc(psi)}</code>${branched}`;
    go(Math.min(gotoIdx | 0, steps.length - 1));
    updatePermalink();
    return true;
  }

  function runSource(phi, psi) {
    choicePath = [];
    return runPath(phi, psi, 0);
  }

  function runEditor() {
    runSource($("phi").value.trim(), $("psi").value.trim());
  }

  // Snip the interaction space at the current step back into the editor and
  // continue from there — explore "what if I'd started here?".
  function forkFromHere() {
    if (!sourceMode || !steps[idx]) return;
    const psi = steps[idx].psi_stars.join(" + ");
    if (psiEd) psiEd.setValue(psi); else $("psi").value = psi;
    if (phiEd) phiEd.setValue(lastPhi); else $("phi").value = lastPhi;
    choicePath = [];
    runSource(lastPhi, psi);
  }

  function loadIntoEditor(phi, psi) {
    if (phiEd) phiEd.setValue(phi); else $("phi").value = phi;
    if (psiEd) psiEd.setValue(psi); else $("psi").value = psi;
    runEditor();
  }

  // Ex semantics — on demand (synchronous engine call; never auto).
  function computeEx() {
    const body = $("exbody");
    if (!body) return;
    const phi = (lastPhi || $("phi").value).trim();
    const psi = (lastPsi || $("psi").value).trim();
    const k = Math.max(1, Math.min(12, parseInt($("exk").value, 10) || 2));
    body.innerHTML = `<p class="reader-status">Running concrete execution at k=${k}…</p>`;
    let res;
    try { res = JSON.parse(mod.ex_run(phi, psi, k, fuelVal())); }
    catch (e) { body.innerHTML = `<p class="reader-status error">engine error: ${esc(e.message)}</p>`; return; }
    if (!res.ok) { body.innerHTML = `<p class="reader-status error">${esc(res.error)}</p>`; return; }
    body.textContent = "";
    body.appendChild(DGM.chip(
      res.order_independent ? "strategy-independent ɟ" : "order-sensitive ɟ",
      res.order_independent ? "ok" : "no",
      res.order_independent
        ? "same ɟ under the default and an alternate firing order — exact engine"
        : "different ɟ under another order — non-confluent here, or fuel exhausted"));
    body.appendChild(DGM.setField(res.result, { title: "the result — ɟ(IEx), exact (Stage 0)" }));
    body.appendChild(DGM.setField(res.alt, { title: "ɟ under an alternate firing order (exact)" }));
    body.appendChild(DGM.setField(res.cex, {
      title: `raw CEx cross-check · copy budget k=${res.cex_k} (renamed copies; research aid)`,
    }));
    body.appendChild(DGM.legend());
    const note = document.createElement("p");
    note.className = "stx-ex__note";
    note.textContent = res.note;
    body.appendChild(note);
    // Quantitative strip (ω-weight §79, visibility, counts) as stat tiles.
    try {
      const m = JSON.parse(mod.lc_measures(phi, psi));
      if (m.ok) {
        const mw = document.createElement("div");
        mw.className = "stx-ex__grp";
        const lab = document.createElement("span");
        lab.className = "stx-obs__lab";
        lab.textContent = "measures — ω-weight §79, visibility, structure";
        mw.appendChild(lab);
        mw.appendChild(DGM.tiles([
          { k: "ω(Φ⊎Ψ)", v: m.omega_cfg },
          { k: "ω(Φ)", v: m.omega_phi },
          { k: "ω(Ψ)", v: m.omega_psi, tone: "warm" },
          { k: "visible", v: m.visible ? "yes" : "no", tone: "cool" },
          { k: "Φ ★/rays", v: `${m.stars_phi}/${m.rays_phi}` },
          { k: "Ψ ★/rays", v: `${m.stars_psi}/${m.rays_psi}`, tone: "warm" },
        ]));
        body.appendChild(mw);
      }
    } catch (_) { /* measures are a nicety; never block the Ex view */ }
  }

  // A preset is now just an editable example: pull its Display source.
  function loadShowcase(i) {
    let src;
    try { src = JSON.parse(mod.preset_source(i)); } catch { src = null; }
    if (src) { choicePath = []; loadIntoEditor(src.phi, src.psi); return true; }
    return false;
  }

  function fuelVal() {
    const el = $("fuel");
    const n = el ? parseInt(el.value, 10) : 0;
    return Number.isFinite(n) && n > 0 ? n : 0; // 0 → engine default
  }

  // ɟ(Ψ) is now computed authoritatively by stella-core (snap.observable);
  // the old client-side polarity filter was removed for exactness.

  // Plain-text dump of the whole trace, for sharing / lecture notes.
  function traceText() {
    const lines = [
      `Φ = ${lastPhi}`,
      `Ψ = ${lastPsi}`,
      `— ${steps.length} step(s) —`,
      "",
    ];
    steps.forEach((s) => {
      lines.push(`step ${s.step}${s.is_final ? " (normal form)" : ""}`);
      s.psi_stars.forEach((st) => lines.push(`  ${st}`));
      if (s.mgu && s.mgu.length) {
        lines.push(`  mgu: ${s.mgu.map(([v, t]) => `${v} ↦ ${t}`).join(" · ")}`);
      }
      lines.push("");
    });
    return lines.join("\n");
  }

  if (!compact) {
    phiEd = enhanceField($("phi"));
    psiEd = enhanceField($("psi"));

    // Library rail — categorised, editable, with "what to watch for".
    const lib = $("lib");
    lib.innerHTML =
      `<div class="stx-rail__h">Examples</div>` +
      LIBRARY.map((g) =>
        `<div class="stx-rail__g">${esc(g.group)}</div>` +
        g.items.map((it, k) =>
          `<button class="stx-rail__i" data-g="${esc(g.group)}" data-k="${k}">
             <span class="stx-rail__n">${esc(it.name)}</span>
             <span class="stx-rail__note">${esc(it.note)}</span></button>`
        ).join("")
      ).join("") +
      `<div class="stx-rail__g">Engine showcases — Eng's encodings, editable</div>` +
      presets.map((p, i) =>
        `<button class="stx-rail__i" data-preset="${i}">
           <span class="stx-rail__n">${esc(p.name)}</span>
           <span class="stx-rail__note">${esc(p.description)}</span></button>`
      ).join("");
    lib.querySelectorAll(".stx-rail__i").forEach((b) => {
      b.addEventListener("click", () => {
        lib.querySelectorAll(".stx-rail__i").forEach((x) =>
          x.classList.toggle("is-active", x === b));
        if (b.dataset.preset != null) { loadShowcase(+b.dataset.preset); return; }
        const g = LIBRARY.find((x) => x.group === b.dataset.g);
        const it = g && g.items[+b.dataset.k];
        if (it) loadIntoEditor(it.phi, it.psi);
      });
    });

    $("run").addEventListener("click", runEditor);

    // Ex semantics — on-demand only.
    const exBtn = $("excompute");
    if (exBtn) exBtn.addEventListener("click", computeEx);
    const exk = $("exk");
    if (exk) exk.addEventListener("keydown", (e) => {
      if (e.key === "Enter") { e.preventDefault(); computeEx(); }
    });

    // ── Shared spec helpers ────────────────────────────────────────────────
    const SPEC_KEY = (m, k) => `stella.spec.${m}.${k}`;
    const parseCheck = (src) => {
      if (!src || !src.trim()) return true;
      try { return JSON.parse(mod.parse_check(src, "")).ok !== false; }
      catch { return false; }
    };
    const prevReset = (host) => {
      host.textContent = "";
      host.appendChild(
        Object.assign(document.createElement("span"),
          { className: "sf-preview__lab", textContent: "live preview" }));
      return host;
    };
    // Live diagram preview from the in-progress form value.
    function renderSpecPreview(kind, v, host) {
      prevReset(host);
      try {
        if (kind === "mll" || kind === "mll2i" || kind === "proofnet") {
          host.appendChild(DGM.proofStructure(v.kind || kind, v.links || []));
        } else if (kind === "ortho") {
          host.appendChild(DGM.field(v.phi1 || "", { title: "Φ₁" }));
          host.appendChild(DGM.field(v.phi2 || "", { title: "Φ₂" }));
        } else if (kind === "compare") {
          host.appendChild(DGM.field(v.phiA || "", { title: "ΦA" }));
          host.appendChild(DGM.field(v.psiA || "", { title: "ΨA" }));
          host.appendChild(DGM.field(v.phiB || "", { title: "ΦB" }));
          host.appendChild(DGM.field(v.psiB || "", { title: "ΨB" }));
        } else if (kind === "behaviour") {
          host.appendChild(DGM.setField(v.members || [], { title: "A — members" }));
          host.appendChild(DGM.setField(v.universe || [], { title: "universe" }));
        } else if (kind === "nfta") {
          host.appendChild(DGM.field((v.rules || []).map((r) =>
            `[${r.state}, ${r.symbol}(${(r.successors || []).join(",")})]`).join(" + "),
            { title: `${(v.rules || []).length} rules` }));
        } else if (kind === "circuit") {
          host.appendChild(DGM.field((v.gates || []).map((g) =>
            `[${g.label}(${(g.inputs || []).join(",")})${g.is_output ? ", out" : ""}]`).join(" + "),
            { title: `${(v.gates || []).length} gates` }));
        } else {
          // automata / tiles — a compact structural snapshot
          const box = document.createElement("div");
          box.className = "dgm-tiles";
          const tile = (label, val) => {
            const d = document.createElement("div"); d.className = "dgm-tile";
            d.appendChild(Object.assign(document.createElement("div"),
              { className: "dgm-tile__v", textContent: String(val) }));
            d.appendChild(Object.assign(document.createElement("div"),
              { className: "dgm-tile__k", textContent: label }));
            box.appendChild(d);
          };
          if (v.states) tile("states", v.states.length);
          if (v.transitions) tile("δ rows", v.transitions.length);
          if (v.delta) tile("δ rows", v.delta.length);
          if (v.tile_types) tile("tiles", v.tile_types.length);
          if (v.word) tile("|word|", v.word.length);
          if (v.input) tile("|input|", v.input.length);
          host.appendChild(box);
          if (v.states && v.states.length) {
            const f = document.createElement("div"); f.className = "sf-preview__lab";
            f.textContent = "states: " + v.states.join(" · ");
            host.appendChild(f);
          }
        }
      } catch (_) { /* preview is best-effort; never block editing */ }
    }

    // Construction lab — schema-driven form → Eng-faithful constellation.
    const cpanel = $("cpanel"), cclass = $("cclass"), cerr = $("cerr");
    const cForm = new SpecForm($("cform"), {
      parseCheck,
      onChange: (v) => {
        try { localStorage.setItem(SPEC_KEY("c", cclass.value), JSON.stringify(v)); } catch (_) {}
        renderSpecPreview(cclass.value, v, $("cprev"));
      },
    });
    const cSetSchema = (useExample) => {
      cerr.textContent = "";
      let init = null;
      if (!useExample) {
        try { init = JSON.parse(localStorage.getItem(SPEC_KEY("c", cclass.value))); } catch (_) {}
      }
      if (!init) { try { init = JSON.parse(CSPEC[cclass.value] || "{}"); } catch (_) {} }
      cForm.setSchema(cclass.value, init);
    };
    const cBuild = () => {
      cerr.textContent = "";
      let res;
      try { res = JSON.parse(mod.build_machine(cclass.value, cForm.json())); }
      catch (e) { cerr.textContent = "engine error: " + e.message; return; }
      if (!res.ok) { cerr.textContent = res.error || "build failed"; return; }
      cpanel.hidden = true;
      choicePath = [];
      loadIntoEditor(res.phi, res.psi || "");
    };
    $("construct").addEventListener("click", () => {
      if (!cForm.schemaKey) cSetSchema(false);
      cpanel.hidden = false;
      cpanel.querySelector(".sf-in,.sf-sel,.sf-add")?.focus();
    });
    $("cclose").addEventListener("click", () => { cpanel.hidden = true; });
    cpanel.addEventListener("click", (e) => { if (e.target === cpanel) cpanel.hidden = true; });
    cpanel.addEventListener("keydown", (e) => {
      if (e.key === "Escape") cpanel.hidden = true;
      else if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); cBuild(); }
    });
    cclass.addEventListener("change", () => cSetSchema(false));
    $("cexample").addEventListener("click", () => cSetSchema(true));
    $("cbuild").addEventListener("click", cBuild);
    cSetSchema(false);

    // ── Logic workbench ────────────────────────────────────────────────────
    const lpanel = $("lpanel"), lclass = $("lclass"),
      lerr = $("lerr"), lout = $("lout"), lload = $("lload");
    let lastPhiComp = "";
    const lForm = new SpecForm($("lform"), {
      parseCheck,
      onChange: (v) => {
        try { localStorage.setItem(SPEC_KEY("l", lclass.value), JSON.stringify(v)); } catch (_) {}
        renderSpecPreview(lclass.value, v, $("lprev"));
      },
    });
    const lSetSchema = (useExample) => {
      lerr.textContent = ""; lout.textContent = ""; lload.hidden = true;
      let init = null;
      if (!useExample) {
        try { init = JSON.parse(localStorage.getItem(SPEC_KEY("l", lclass.value))); } catch (_) {}
      }
      if (!init) { try { init = JSON.parse(LSPEC[lclass.value] || "{}"); } catch (_) {} }
      lForm.setSchema(lclass.value, init);
    };
    $("logic").addEventListener("click", () => {
      if (!lForm.schemaKey) lSetSchema(false);
      lpanel.hidden = false;
      lpanel.querySelector(".sf-in,.sf-sel,.sf-add")?.focus();
    });
    $("lclose").addEventListener("click", () => { lpanel.hidden = true; });
    lpanel.addEventListener("click", (e) => { if (e.target === lpanel) lpanel.hidden = true; });
    lpanel.addEventListener("keydown", (e) => {
      if (e.key === "Escape") lpanel.hidden = true;
      else if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); $("lrun").click(); }
    });
    lclass.addEventListener("change", () => lSetSchema(false));
    $("lexample").addEventListener("click", () => lSetSchema(true));
    lSetSchema(false);
    lload.addEventListener("click", () => {
      if (!lastPhiComp) return;
      lpanel.hidden = true; choicePath = []; loadIntoEditor(lastPhiComp, "");
    });
    $("lrun").addEventListener("click", () => {
      lerr.textContent = ""; lout.innerHTML = ""; lload.hidden = true;
      const spec = lForm.value();
      let res;
      try {
        if (lclass.value === "ortho") {
          res = JSON.parse(mod.lc_ortho(spec.phi1 || "", spec.phi2 || ""));
        } else if (lclass.value === "proofnet") {
          res = JSON.parse(mod.lc_proofnet(spec.kind || "mll",
            JSON.stringify({ links: spec.links || [] })));
        } else if (lclass.value === "compare") {
          res = JSON.parse(mod.lc_compare(spec.phiA || "", spec.psiA || "",
            spec.phiB || "", spec.psiB || "", fuelVal()));
        } else {
          res = JSON.parse(mod.lc_behaviour(lForm.json()));
        }
      } catch (e) { lerr.textContent = "engine error: " + e.message; return; }
      if (!res.ok) { lerr.textContent = res.error || "failed"; return; }

      lout.textContent = "";
      const lgrp = (labTxt, node) => {
        const g = document.createElement("div");
        g.className = "stx-ex__grp";
        const l = document.createElement("span");
        l.className = "stx-obs__lab";
        l.textContent = labTxt;
        g.appendChild(l);
        g.appendChild(node);
        return g;
      };
      const lnote = (t) => {
        const p = document.createElement("p");
        p.className = "stx-ex__note";
        p.textContent = t;
        return p;
      };
      const lrow = (...chips) => {
        const r = document.createElement("div");
        r.className = "stx-ex__set";
        chips.forEach((c) => r.appendChild(c));
        return r;
      };

      if (lclass.value === "ortho") {
        lout.appendChild(lgrp("Φ₁ ⊥ Φ₂ — the three orthogonality relations",
          lrow(
            DGM.chip("⊥fin", res.fin ? "ok" : "no", "finite — the interaction normalises"),
            DGM.chip("⊥1", res.one ? "ok" : "no", "single-component (proof-net ⊥¹)"),
            DGM.chip("⊥R", res.roots ? "ok" : "no", "root-based (⊥ᴿ)"))));
        if (spec.phi1) lout.appendChild(DGM.field(spec.phi1, { title: "Φ₁" }));
        if (spec.phi2) lout.appendChild(DGM.field(spec.phi2, { title: "Φ₂" }));
      } else if (lclass.value === "proofnet") {
        lastPhiComp = res.phi || "";
        lload.hidden = !lastPhiComp;
        const state = res.verdict === true ? "ok" : res.verdict === false ? "no" : "na";
        lout.appendChild(lrow(DGM.chip(esc(res.verdict_name) + " criterion", state,
          res.verdict === true ? "correct" : res.verdict === false ? "not correct" : "not applicable")));
        lout.appendChild(lnote(res.verdict_note));
        lout.appendChild(lgrp("proof-structure — your spec · axiom arcs above, cut below",
          DGM.proofStructure(spec.kind || "mll", spec.links || [])));
        lout.appendChild(lgrp("Φ_comp (editable, runnable)", DGM.field(res.phi, { title: "Φ_comp" })));
        if (res.diagrams && res.diagrams.length) {
          lout.appendChild(lgrp("saturated diagrams",
            lrow(...res.diagrams.map((d, i) =>
              DGM.chip(`δ${i} · ${d.vertices}v/${d.edges}e`, d.correct ? "ok" : "no",
                `${d.connected ? "connected" : "disconnected"}${d.actualised ? " · ↓" + d.actualised : ""}`)))));
        }
        lout.appendChild(lnote(res.diag_note));
      } else if (lclass.value === "compare") {
        lout.appendChild(lrow(DGM.chip(
          res.same ? "same observable" : "different observables",
          res.same ? "ok" : "no",
          res.same ? "A and B compute the same result" : "A and B diverge")));
        lout.appendChild(lgrp(`A — ɟ · ω = ${res.omega_a}`, DGM.setField(res.obs_a)));
        lout.appendChild(lgrp(`B — ɟ · ω = ${res.omega_b}`, DGM.setField(res.obs_b)));
        lout.appendChild(DGM.tiles([
          { k: "ω(A)", v: res.omega_a },
          { k: "ω(B)", v: res.omega_b, tone: "warm" },
          { k: "Δω", v: res.omega_b - res.omega_a, tone: "cool" },
        ]));
        lout.appendChild(lnote("Exact engine (Stage 0) both sides."));
      } else {
        lout.appendChild(lgrp(`bi-orthogonal closure  (⊥${res.orth})`,
          DGM.closure(res.a, res.a_perp, res.a_biperp, res.is_behaviour)));
        lout.appendChild(lnote(
          "A type, in transcendental syntax, is exactly a behaviour: a set fixed by " +
          "bi-orthogonal closure. Membership of a Φ is orthogonality to every test."));
      }
    });

    const ct = $("copytrace");
    if (ct) ct.addEventListener("click", () => {
      if (!steps.length) return;
      navigator.clipboard?.writeText(traceText()).then(() => {
        const o = ct.textContent; ct.textContent = "copied";
        setTimeout(() => (ct.textContent = o), 1400);
      });
    });

    // Live, debounced parse feedback — ✓/✗ and an in-gutter error line.
    let vt = null;
    const validate = () => {
      const phi = $("phi").value.trim();
      const psi = $("psi").value.trim();
      if (!phi && !psi) { setValidity(false, ""); clearFrame(); return; }
      let res;
      try { res = JSON.parse(mod.parse_check(phi, psi)); }
      catch { return; }
      if (res.ok) { setValidity(true, "✓ well-formed"); clearFrame(); }
      else showParseError(res, phi, psi);
    };
    const debounced = () => { clearTimeout(vt); vt = setTimeout(validate, 250); };
    ["phi", "psi"].forEach((r) => {
      const t = $(r);
      t.addEventListener("input", debounced);
      t.addEventListener("keydown", (e) => {
        if ((e.metaKey || e.ctrlKey) && e.key === "Enter") {
          e.preventDefault(); runEditor();
        }
      });
    });

    // Re-resolve with the new fuel cap (useful for non-terminating Ψ).
    const fuelEl = $("fuel");
    if (fuelEl) fuelEl.addEventListener("change", () => {
      if (sourceMode) runPath(lastPhi, lastPsi, idx);
    });

    // ── Workspaces — self-contained persistence (localStorage + JSON) ───────
    const WS_KEY = "stella.workspaces.v1";
    const wsLoad = () => {
      try { return JSON.parse(localStorage.getItem(WS_KEY)) || {}; }
      catch { return {}; }
    };
    const wsStore = (o) => localStorage.setItem(WS_KEY, JSON.stringify(o));
    const elWs = $("ws"), elWsDel = $("wsdel");
    function wsRefresh(sel) {
      const all = wsLoad();
      const names = Object.keys(all).sort();
      elWs.innerHTML =
        `<option value="">workspaces…</option>` +
        names.map((n) => `<option value="${esc(n)}">${esc(n)}</option>`).join("");
      if (sel && all[sel]) elWs.value = sel;
      if (elWsDel) elWsDel.hidden = !elWs.value;
    }
    elWs.addEventListener("change", () => {
      const all = wsLoad(), w = all[elWs.value];
      if (elWsDel) elWsDel.hidden = !elWs.value;
      if (w) { choicePath = []; loadIntoEditor(w.phi, w.psi); }
    });
    $("wssave").addEventListener("click", () => {
      const def = "ws-" + new Date().toISOString().slice(0, 16).replace("T", " ");
      const name = (prompt("Save workspace as:", def) || "").trim();
      if (!name) return;
      const all = wsLoad();
      all[name] = { phi: $("phi").value, psi: $("psi").value };
      wsStore(all); wsRefresh(name);
    });
    if (elWsDel) elWsDel.addEventListener("click", () => {
      const all = wsLoad();
      if (elWs.value && all[elWs.value]) {
        delete all[elWs.value]; wsStore(all); wsRefresh();
      }
    });
    $("wsexport").addEventListener("click", () => {
      const blob = new Blob([JSON.stringify(wsLoad(), null, 2)],
        { type: "application/json" });
      const a = document.createElement("a");
      a.href = URL.createObjectURL(blob);
      a.download = "stella-workspaces.json";
      a.click(); URL.revokeObjectURL(a.href);
    });
    const wsFile = $("wsfile");
    $("wsimport").addEventListener("click", () => wsFile && wsFile.click());
    if (wsFile) wsFile.addEventListener("change", () => {
      const f = wsFile.files && wsFile.files[0];
      if (!f) return;
      const rd = new FileReader();
      rd.onload = () => {
        try {
          const inc = JSON.parse(rd.result);
          const all = wsLoad();
          for (const k of Object.keys(inc)) {
            if (inc[k] && typeof inc[k].phi === "string") all[k] = inc[k];
          }
          wsStore(all); wsRefresh();
        } catch { /* ignore bad file */ }
      };
      rd.readAsText(f);
      wsFile.value = "";
    });
    wsRefresh();
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
    const orig = pl.textContent;
    navigator.clipboard?.writeText(pl.href).then(() => {
      pl.textContent = "copied ✓"; setTimeout(() => (pl.textContent = orig), 1400);
    });
  });

  elPresets.addEventListener("change", (e) => loadPreset(+e.target.value));

  // initial: ?phi=&psi= | ?preset=<idx|name substring> | opts | first preset
  const q = new URLSearchParams(location.search);
  const qPhi = q.get("phi"), qPsi = q.get("psi"), qPreset = q.get("preset");
  if (qPhi != null && !compact) {
    if (phiEd) phiEd.setValue(qPhi); else $("phi").value = qPhi;
    if (psiEd) psiEd.setValue(qPsi || ""); else $("psi").value = qPsi || "";
    runSource(qPhi.trim(), (qPsi || "").trim());
  } else if (qPreset != null) {
    let i = parseInt(qPreset, 10);
    if (Number.isNaN(i)) {
      i = presets.findIndex((p) =>
        p.name.toLowerCase().includes(qPreset.toLowerCase()));
    }
    i = i >= 0 && i < presets.length ? i : 0;
    // In the IDE a preset opens as editable source; inline stays a trace.
    if (compact) await loadPreset(i);
    else if (!loadShowcase(i)) await loadPreset(i);
  } else if (compact) {
    await loadPreset(
      Number.isInteger(opts.initialPreset) && opts.initialPreset < presets.length
        ? opts.initialPreset : 0);
  } else {
    // The IDE opens on an editable example, with the rail item marked.
    const first = LIBRARY[0].items[0];
    const b = $("lib").querySelector('.stx-rail__i[data-g][data-k="0"]');
    if (b) b.classList.add("is-active");
    loadIntoEditor(first.phi, first.psi);
  }
  return { loadPreset };
}
