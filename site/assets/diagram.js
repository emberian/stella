// diagram.js — the Stella visual kit.
//
// A dependency-free renderer for the diagrammatic objects of stellar
// resolution: stars-and-rays (the literal "stellar" metaphor), constellation
// fields, the bi-orthogonal closure, and MLL proof-structures. Every colour is
// a design-system token (var(--…)), so light/dark and the botanical palette
// come for free. Nothing here infers semantics — it renders exact strings the
// engine produced; structural overlays are always labelled as such.

const SVGNS = "http://www.w3.org/2000/svg";
const svg = (n, a = {}) => {
  const e = document.createElementNS(SVGNS, n);
  for (const k in a) e.setAttribute(k, a[k]);
  return e;
};
const el = (n, cls, txt) => {
  const e = document.createElement(n);
  if (cls) e.className = cls;
  if (txt != null) e.textContent = txt;
  return e;
};

// ── Parsing the surface syntax (faithful, no inference) ───────────────────
// Constellation: "[r1, r2] + [r3]" — stars are []-delimited; terms use ().
export function splitStars(src) {
  const out = [];
  const re = /\[([^\]]*)\]/g;
  let m;
  while ((m = re.exec(src || ""))) out.push(m[1]);
  return out;
}

function splitTop(s) {
  const parts = [];
  let d = 0, cur = "";
  for (const ch of s) {
    if (ch === "(") { d++; cur += ch; }
    else if (ch === ")") { d--; cur += ch; }
    else if (ch === "," && d === 0) { parts.push(cur); cur = ""; }
    else cur += ch;
  }
  if (cur.trim() || parts.length) parts.push(cur);
  return parts.map((x) => x.trim()).filter(Boolean);
}

// "+add(s(X), Y, s(Z))" → { pol:'pos', sym:'add', arity:3, text:'add(…)' }
export function parseRay(raw) {
  const t = (raw || "").trim();
  let pol = "neu", body = t;
  if (t[0] === "+") { pol = "pos"; body = t.slice(1); }
  else if (t[0] === "-" || t[0] === "−") { pol = "neg"; body = t.slice(1); }
  body = body.trim();
  const lp = body.indexOf("(");
  let sym = body, arity = 0;
  if (lp >= 0 && body.endsWith(")")) {
    sym = body.slice(0, lp);
    arity = splitTop(body.slice(lp + 1, -1)).length;
  }
  return { pol, sym, arity, text: body, raw: t };
}

// ── The star glyph ────────────────────────────────────────────────────────
// A soft ringed body with a faint starburst and its rays as curved ink
// spokes, polarity-coloured (+ moss, − bark, neutral ink). Organic.
const POL = {
  pos: { stroke: "var(--moss)", glyph: "+" },
  neg: { stroke: "var(--bark)", glyph: "−" },
  neu: { stroke: "var(--fg-3)", glyph: "·" },
};

export function starGlyph(rayStrs, opts = {}) {
  const rays = rayStrs.map(parseRay);
  const n = Math.max(rays.length, 1);
  // Body at left-centre; rays fan rightward to left-aligned labels. Height
  // scales with ray count so trivial stars stay compact, dense ones breathe.
  const rDisc = 15;
  const cx = 40;
  const H = Math.max(58, 14 + n * 26);
  const longest = rays.reduce((m, r) => Math.max(m, r.text.length), 1);
  const W = Math.max(208, 148 + longest * 7.2);
  const cy = H / 2;
  const s = svg("svg", {
    class: "dgm-star", viewBox: `0 0 ${W} ${H}`, width: W, height: H,
    preserveAspectRatio: "xMinYMid meet",
    role: "img",
    "aria-label": `star with ${rays.length} ray${rays.length === 1 ? "" : "s"}`,
  });

  // a faint 8-point starburst behind the body — the "stellar" motif
  const burst = svg("g", { class: "dgm-burst" });
  for (let k = 0; k < 8; k++) {
    const ba = (Math.PI / 4) * k;
    const r0 = rDisc + 3, r1 = rDisc + (k % 2 ? 6 : 10);
    burst.appendChild(svg("line", {
      x1: cx + Math.cos(ba) * r0, y1: cy + Math.sin(ba) * r0,
      x2: cx + Math.cos(ba) * r1, y2: cy + Math.sin(ba) * r1,
    }));
  }
  s.appendChild(burst);

  // spokes — gentle curves from the body out to each ray label
  const spread = n === 1 ? 0 : Math.min(Math.PI * 0.9, 0.34 * n + 0.5);
  const startA = -spread / 2;
  const len = 50;
  rays.forEach((r, i) => {
    const a = n === 1 ? 0 : startA + (spread * i) / (n - 1);
    const sx = cx + Math.cos(a) * rDisc, sy = cy + Math.sin(a) * rDisc;
    const ex = cx + rDisc + len;
    const ey = cy + Math.sin(a) * (rDisc + len) * 0.6;
    const p = POL[r.pol];
    s.appendChild(svg("path", {
      d: `M ${sx} ${sy} C ${sx + 22} ${sy}, ${ex - 26} ${ey}, ${ex} ${ey}`,
      fill: "none", stroke: p.stroke, "stroke-width": 1.6,
      "stroke-linecap": "round", class: "dgm-spoke",
    }));
    s.appendChild(svg("circle", { cx: ex, cy: ey, r: 2.6, fill: p.stroke, class: "dgm-tip" }));
    const tt = svg("text", {
      x: ex + 7, y: ey + 3.6, "text-anchor": "start",
      class: `dgm-ray dgm-ray--${r.pol}`,
    });
    tt.textContent = `${p.glyph} ${r.text}`;
    s.appendChild(tt);
  });

  // the body
  s.appendChild(svg("circle", {
    cx, cy, r: rDisc + 4, fill: "none", stroke: "var(--border-strong)",
    "stroke-width": 1, "stroke-dasharray": "1 3", class: "dgm-halo",
  }));
  s.appendChild(svg("circle", {
    cx, cy, r: rDisc, fill: "var(--cream)",
    stroke: "var(--bark)", "stroke-width": 1.4, class: "dgm-body",
  }));
  const lab = svg("text", { x: cx, y: cy + 4.4, "text-anchor": "middle", class: "dgm-bodylab" });
  lab.textContent = opts.title || "★";
  s.appendChild(lab);

  const fig = el("figure", "dgm-starfig");
  fig.appendChild(s);
  if (opts.caption) fig.appendChild(el("figcaption", "dgm-cap", opts.caption));
  return fig;
}

// ── Constellation field ───────────────────────────────────────────────────
// A labelled card holding the stars of a constellation as wrapped glyphs.
export function field(src, opts = {}) {
  const wrap = el("div", "dgm-field");
  const stars = splitStars(src);
  if (opts.title) {
    const h = el("div", "dgm-field__hd");
    h.appendChild(el("span", "dgm-field__lab", opts.title));
    h.appendChild(el("span", "dgm-field__meta",
      `${stars.length}★ · ${stars.reduce((a, c) => a + splitTop(c).length, 0)} rays`));
    wrap.appendChild(h);
  }
  const body = el("div", "dgm-field__body");
  if (!stars.length) {
    body.appendChild(el("span", "dgm-empty", opts.empty || "∅"));
  } else {
    stars.forEach((st, i) =>
      body.appendChild(starGlyph(splitTop(st), {
        title: opts.label ? opts.label(i) : `${i}`,
      })));
  }
  wrap.appendChild(body);
  return wrap;
}

// Render a list of constellation strings as one field (used for result sets).
export function setField(arr, opts = {}) {
  return field((arr || []).join(" + "), { ...opts, empty: opts.empty || "∅ empty" });
}

// ── Verdict chip ──────────────────────────────────────────────────────────
// state: 'ok' | 'no' | 'na'. Optional gloss line beneath.
export function chip(label, state, gloss) {
  const c = el("span", `dgm-chip dgm-chip--${state}`);
  c.appendChild(el("span", "dgm-chip__dot"));
  c.appendChild(el("span", "dgm-chip__lab", label));
  c.appendChild(el("span", "dgm-chip__mark",
    state === "ok" ? "✓" : state === "no" ? "✗" : "—"));
  if (!gloss) return c;
  const w = el("span", "dgm-chipwrap");
  w.appendChild(c);
  w.appendChild(el("small", "dgm-chip__gloss", gloss));
  return w;
}

// ── Stat tiles ────────────────────────────────────────────────────────────
// pairs: [{ k:'ω(Φ⊎Ψ)', v:-1, tone:'warm', hint:'…' }, …]
export function tiles(pairs) {
  const row = el("div", "dgm-tiles");
  for (const p of pairs) {
    const t = el("div", "dgm-tile");
    if (p.tone) t.classList.add(`dgm-tile--${p.tone}`);
    t.appendChild(el("div", "dgm-tile__v", String(p.v)));
    t.appendChild(el("div", "dgm-tile__k", p.k));
    if (p.hint) t.title = p.hint;
    row.appendChild(t);
  }
  return row;
}

// ── Bi-orthogonal closure ─────────────────────────────────────────────────
// A ⊆ A^⊥⊥, with A^⊥ as the dual region; the outer ring is the fixed point
// (A = A^⊥⊥) — highlighted when A is a behaviour.
export function closure(a, aPerp, aBi, isBeh) {
  const W = 460, H = 200;
  const s = svg("svg", {
    class: "dgm-closure", viewBox: `0 0 ${W} ${H}`, role: "img",
    "aria-label": "bi-orthogonal closure diagram",
  });
  const blob = (bx, by, rx, ry, cls) =>
    svg("path", {
      class: cls,
      d: `M ${bx - rx} ${by}
          C ${bx - rx} ${by - ry * 1.1}, ${bx - rx * 0.4} ${by - ry}, ${bx} ${by - ry}
          C ${bx + rx * 0.5} ${by - ry}, ${bx + rx} ${by - ry * 0.9}, ${bx + rx} ${by}
          C ${bx + rx} ${by + ry * 1.05}, ${bx + rx * 0.4} ${by + ry}, ${bx} ${by + ry}
          C ${bx - rx * 0.5} ${by + ry}, ${bx - rx} ${by + ry * 0.95}, ${bx - rx} ${by} Z`,
    });
  s.appendChild(blob(150, 100, 128, 78, "dgm-cl dgm-cl--bi" + (isBeh ? " is-fixed" : "")));
  s.appendChild(blob(150, 100, 78, 46, "dgm-cl dgm-cl--a"));
  s.appendChild(blob(360, 100, 78, 60, "dgm-cl dgm-cl--perp"));
  const cap = (x, y, t, num) => {
    const g = svg("g", { class: "dgm-cl__cap" });
    const e1 = svg("text", { x, y, "text-anchor": "middle", class: "dgm-cl__t" });
    e1.textContent = t;
    const e2 = svg("text", { x, y: y + 17, "text-anchor": "middle", class: "dgm-cl__n" });
    e2.textContent = `|·| = ${num}`;
    g.appendChild(e1); g.appendChild(e2);
    return g;
  };
  s.appendChild(cap(150, 70, "A", a));
  s.appendChild(cap(150, 30, "A⊥⊥", aBi));
  s.appendChild(cap(360, 96, "A⊥", aPerp));
  const tag = svg("text", { x: W / 2, y: H - 8, "text-anchor": "middle", class: "dgm-cl__verdict" });
  tag.textContent = isBeh
    ? "A = A⊥⊥  —  fixed by bi-orthogonal closure: a behaviour"
    : "A ⊂ A⊥⊥  —  not closed: not a behaviour";
  tag.classList.add(isBeh ? "is-ok" : "is-no");
  s.appendChild(tag);
  return s;
}

// ── MLL / MLL2I proof-structure ───────────────────────────────────────────
// Faithful to the engine spec (logic.rs): links are
//   { kind:"ax"|"cut", left, right }
//   { kind:"tensor"|"par"|"etensor"|"epar"|"contraction", left, right, output }
// where left/right/output are integer vertex ids. Vertices sit on a baseline
// row; axiom links arc above, cut links arc below, connectives are nodes that
// fan down to their two premises. Exact rendering of the user's spec; the
// correctness verdict is the engine's.
const CONN = {
  tensor: "⊗", par: "⅋", etensor: "⊗", epar: "⅋",
  contraction: "c", weakening: "w", dereliction: "d",
};
export function proofStructure(kind, links) {
  links = (links || []).map((lk) => ({
    kind: String(lk.kind || lk.type || "").toLowerCase(),
    left: lk.left, right: lk.right, output: lk.output,
  }));
  // collect vertex ids in ascending order
  const ids = [...new Set(links.flatMap((lk) =>
    [lk.left, lk.right, lk.output].filter((v) => v != null)))].sort((p, q) => p - q);
  const n = Math.max(ids.length, 1);
  const W = Math.max(300, n * 78 + 40), H = 230, base = 150;
  const s = svg("svg", {
    class: "dgm-pn", viewBox: `0 0 ${W} ${H}`, role: "img",
    "aria-label": `${kind} proof-structure`,
  });
  const X = {};
  ids.forEach((v, i) => { X[v] = 36 + i * ((W - 72) / Math.max(n - 1, 1)); });
  const arc = (a, b, up, label, cls) => {
    if (X[a] == null || X[b] == null) return;
    const dy = up ? -74 : 60;
    s.appendChild(svg("path", {
      d: `M ${X[a]} ${base} C ${X[a]} ${base + dy}, ${X[b]} ${base + dy}, ${X[b]} ${base}`,
      class: cls, fill: "none",
    }));
    const t = svg("text", {
      x: (X[a] + X[b]) / 2, y: base + dy * 0.86,
      "text-anchor": "middle", class: "dgm-pn__elab" + (up ? "" : " is-cut"),
    });
    t.textContent = label;
    s.appendChild(t);
  };
  // axiom / cut arcs
  links.forEach((lk) => {
    if (lk.kind === "ax") arc(lk.left, lk.right, true, "ax", "dgm-pn__ax");
    else if (lk.kind === "cut") arc(lk.left, lk.right, false, "cut", "dgm-pn__cut");
  });
  // connective nodes: glyph above the baseline at the output vertex,
  // thin links fanning down to the two premises
  links.forEach((lk) => {
    const g = CONN[lk.kind];
    if (!g || X[lk.output] == null) return;
    const nx = X[lk.output], ny = base - 34;
    [lk.left, lk.right].forEach((pm) => {
      if (X[pm] == null) return;
      s.appendChild(svg("path", {
        d: `M ${nx} ${ny} Q ${(nx + X[pm]) / 2} ${(ny + base) / 2 - 6} ${X[pm]} ${base}`,
        class: "dgm-pn__cedge", fill: "none",
      }));
    });
    s.appendChild(svg("line", { x1: nx, y1: ny, x2: nx, y2: base, class: "dgm-pn__cstem" }));
    const isPar = lk.kind === "par" || lk.kind === "epar";
    s.appendChild(svg("circle", {
      cx: nx, cy: ny, r: 13,
      class: "dgm-pn__node " + (isPar ? "is-par" : "is-tensor"),
    }));
    const tg = svg("text", { x: nx, y: ny + 5, "text-anchor": "middle", class: "dgm-pn__nlab" });
    tg.textContent = g;
    s.appendChild(tg);
  });
  // vertices + id labels
  ids.forEach((v) => {
    const x = X[v];
    s.appendChild(svg("line", { x1: x, y1: base, x2: x, y2: H - 24, class: "dgm-pn__concl" }));
    s.appendChild(svg("circle", { cx: x, cy: base, r: 4.5, class: "dgm-pn__port" }));
    const t = svg("text", { x, y: H - 9, "text-anchor": "middle", class: "dgm-pn__plab" });
    t.textContent = v;
    s.appendChild(t);
  });
  if (!links.length) {
    const t = svg("text", { x: W / 2, y: base, "text-anchor": "middle", class: "dgm-pn__plab" });
    t.textContent = "no links";
    s.appendChild(t);
  }
  return s;
}

// A small polarity legend, reused under fields.
export function legend() {
  const w = el("div", "dgm-legend");
  for (const [k, lab] of [["pos", "+ output"], ["neg", "− input"], ["neu", "neutral"]]) {
    const i = el("span", "dgm-legend__i");
    i.appendChild(el("span", `dgm-legend__sw dgm-legend__sw--${k}`));
    i.appendChild(el("span", null, lab));
    w.appendChild(i);
  }
  return w;
}

// ── Automaton state-graph (Graphviz DOT) ──────────────────────────────────
// Faithful to the engine spec shapes (build.rs). Returns a DOT string for
// nfa / npda / ntm / atm / nfst — rendered by the vendored viz.js, recoloured
// by styleSvg into the Stella palette. Initial states get an entry arrow;
// final / accept states are double-circled; ATM marks E/U state classes.
const dq = (s) => `"${String(s ?? "").replace(/\\/g, "\\\\").replace(/"/g, '\\"')}"`;
const eps = (s) => (s == null || s === "" ? "ε" : String(s));

export function automatonDot(kind, v) {
  v = v || {};
  const head =
    "digraph{rankdir=LR;bgcolor=transparent;" +
    'node[shape=circle,fontname="JetBrains Mono",fontsize=11];' +
    'edge[fontname="JetBrains Mono",fontsize=10];';
  const lines = [];
  const states = new Set(v.states || []);
  const finals = new Set(v.finals || []);
  const initials = v.initial || (v.q0 != null ? [v.q0] : []);
  const accept = v.q_accept, reject = v.q_reject;
  const cls = v.class || {};
  const edges = [];

  if (kind === "nfa") {
    for (const [a, s, b] of v.transitions || []) edges.push([a, b, eps(s)]);
  } else if (kind === "nfst") {
    for (const [a, i, b, o] of v.transitions || []) edges.push([a, b, `${eps(i)} / ${eps(o)}`]);
  } else if (kind === "npda") {
    for (const [a, r, pop, b, push] of v.transitions || [])
      edges.push([a, b, `${eps(r)}, ${eps(pop)} → ${eps(push)}`]);
  } else if (kind === "ntm" || kind === "atm") {
    for (const [a, r, b, w, d] of v.delta || []) edges.push([a, b, `${r} → ${w}, ${d}`]);
    if (accept != null) finals.add(accept);
  }
  for (const [a, b] of edges.map((e) => [e[0], e[1]])) { states.add(a); states.add(b); }

  // node declarations
  for (const st of states) {
    const attrs = [];
    if (finals.has(st) || st === accept) attrs.push("shape=doublecircle");
    if (kind === "atm" && cls[st]) attrs.push(cls[st] === "U" ? "shape=box" : "shape=diamond");
    if (st === reject) attrs.push('style=dashed');
    let lbl = st;
    if (kind === "atm" && cls[st]) lbl = `${st}\\n[${cls[st]}]`;
    lines.push(`${dq(st)}[label=${dq(lbl)}${attrs.length ? "," + attrs.join(",") : ""}];`);
  }
  // initial entry arrows
  initials.forEach((q, i) => {
    if (q == null || q === "") return;
    lines.push(`__i${i}[shape=point,width=0.06];__i${i}->${dq(q)};`);
  });
  // edges (merge identical pairs' labels)
  const seen = new Map();
  for (const [a, b, l] of edges) {
    const k = a + " " + b;
    seen.set(k, seen.has(k) ? seen.get(k) + "\\n" + l : l);
  }
  for (const [k, l] of seen) {
    const [a, b] = k.split(" ");
    lines.push(`${dq(a)}->${dq(b)}[label=${dq(l)}];`);
  }
  if (!states.size) lines.push('empty[shape=plaintext,label="no states yet"];');
  return head + lines.join("") + "}";
}
