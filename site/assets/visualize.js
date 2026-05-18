// visualize.js — a dependency-free, hand-fed illustration of the two
// dynamics described on the page: (1) one stellar-resolution *fusion* step
// (ray matching + most general unifier + substitution) and (2) one KAM
// Push / δ reduction step.
//
// This is NOT the engine. It does not parse, unify, or resolve anything. It
// plays a fixed, pre-authored script that mirrors what the real engine
// (`stella-core`) does on these exact inputs — the same conclusions the live
// /explore.html WebAssembly build reaches, here animated with vanilla
// JS/SVG so a static archive keeps the whole thing. It is labelled
// illustrative on the page for that reason.

const NS = "http://www.w3.org/2000/svg";

function el(tag, attrs, kids) {
  const n = document.createElementNS(NS, tag);
  for (const k in attrs || {}) n.setAttribute(k, attrs[k]);
  for (const c of kids || []) n.appendChild(c);
  return n;
}
function txt(s) { return document.createTextNode(String(s)); }
function htmlEl(tag, cls, html) {
  const n = document.createElement(tag);
  if (cls) n.className = cls;
  if (html != null) n.innerHTML = html;
  return n;
}

// ── Fusion: a tiny constellation, scripted ───────────────────────────────
// Φ : [ +add(0, Y, Y) ]                          (base case)
//     [ -add(X, Y, Z), +add(s(X), Y, s(Z)) ]     (step)
// Ψ : [ -add(s(0), s(0), R), R ]                  (query: 1 + 1 = R)
//
// The script below is the resolution the real engine takes, narrated one
// step at a time. Each frame names the matched ±pair, the most general
// unifier, and the resulting interaction space.

const FUSION_FRAMES = [
  {
    title: "Start",
    note: "Two reference stars (Φ) and one query star (Ψ). " +
      "The query asks for 1 + 1, with a neutral ray R to carry the answer out.",
    stars: [
      { rays: ["+add(0, Y, Y)"], tag: "Φ" },
      { rays: ["−add(X, Y, Z)", "+add(s(X), Y, s(Z))"], tag: "Φ" },
      { rays: ["−add(s(0), s(0), R)", "R"], tag: "Ψ" },
    ],
    match: null, mgu: null,
  },
  {
    title: "Match",
    note: "The query's −add ray and Φ's +add(s(X),…) ray have the same " +
      "symbol, opposite polarity, and unifiable arguments. They are a redex.",
    stars: [
      { rays: ["+add(0, Y, Y)"], tag: "Φ" },
      { rays: ["−add(X, Y, Z)", "+add(s(X), Y, s(Z))"], tag: "Φ", hot: 1 },
      { rays: ["−add(s(0), s(0), R)", "R"], tag: "Ψ", hot: 0 },
    ],
    match: "−add(s(0),s(0),R)  ⋈  +add(s(X),Y,s(Z))",
    mgu: "X ↦ 0 · Y ↦ s(0) · R ↦ s(Z)",
  },
  {
    title: "Fuse + substitute",
    note: "The two stars fuse; the matched pair is consumed; the unifier is " +
      "applied to every ray that remains. A fresh −add request appears.",
    stars: [
      { rays: ["+add(0, Y, Y)"], tag: "Φ" },
      { rays: ["−add(0, s(0), Z)", "s(Z)"], tag: "Ψ", hot: 0 },
    ],
    match: null,
    mgu: "applied: X↦0, Y↦s(0), R↦s(Z)",
  },
  {
    title: "Match the base case",
    note: "The new −add(0, s(0), Z) request now matches Φ's base star " +
      "+add(0, Y, Y) — the recursion bottoms out.",
    stars: [
      { rays: ["+add(0, Y, Y)"], tag: "Φ", hot: 0 },
      { rays: ["−add(0, s(0), Z)", "s(Z)"], tag: "Ψ", hot: 0 },
    ],
    match: "−add(0,s(0),Z)  ⋈  +add(0,Y,Y)",
    mgu: "Y ↦ s(0) · Z ↦ s(0)",
  },
  {
    title: "Normal form",
    note: "No matchable pair remains. The neutral ray left in Ψ is the " +
      "answer: 1 + 1 = s(s(0)).",
    stars: [
      { rays: ["s(s(0))"], tag: "Ψ", result: 0 },
    ],
    match: null, mgu: null, done: true,
  },
];

function rayPol(s) {
  const t = s.trim();
  if (t.startsWith("+")) return "pos";
  if (t.startsWith("-") || t.startsWith("−")) return "neg";
  return "neu";
}

function renderConstellation(host, frame) {
  host.innerHTML = "";
  const c = htmlEl("div", "stx-constellation");
  frame.stars.forEach((star, si) => {
    const sd = htmlEl("div", "stx-star" +
      (frame.hot != null && si === frame.hotStar ? " is-active" : ""));
    star.rays.forEach((r, ri) => {
      if (ri) sd.appendChild(htmlEl("span", "stx-comma", ","));
      let cls = "stx-ray stx-ray--" + rayPol(r);
      if (star.hot === ri) cls += " is-next";
      if (star.result === ri) cls += " is-result";
      sd.appendChild(htmlEl("span", cls, r
        .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")));
    });
    c.appendChild(sd);
  });
  host.appendChild(c);
}

function mountFusion(root) {
  let i = 0;
  const wrap = htmlEl("div", "viz");
  const stage = htmlEl("div", "viz-stage");
  const read = htmlEl("div", "viz-read");
  const controls = htmlEl("div", "viz-controls");

  const prev = htmlEl("button", "viz-btn", "‹ Back");
  const step = htmlEl("button", "viz-btn viz-btn--primary", "Step ›");
  const reset = htmlEl("button", "viz-btn", "Restart");
  const pos = htmlEl("span", "viz-pos");
  prev.type = step.type = reset.type = "button";

  controls.append(prev, step, reset, pos);
  wrap.append(stage, read, controls);
  root.appendChild(wrap);

  function draw() {
    const f = FUSION_FRAMES[i];
    renderConstellation(stage, f);
    let html = `<div class="viz-read__h">${f.title}</div>` +
      `<p class="viz-read__n">${f.note}</p>`;
    if (f.match) html += `<div class="viz-read__row"><span class="viz-lab">redex</span>` +
      `<code>${f.match}</code></div>`;
    if (f.mgu) html += `<div class="viz-read__row"><span class="viz-lab">unifier</span>` +
      `<code>${f.mgu}</code></div>`;
    read.innerHTML = html;
    pos.textContent = `${i + 1} / ${FUSION_FRAMES.length}`;
    prev.disabled = i === 0;
    step.disabled = i === FUSION_FRAMES.length - 1;
  }
  step.addEventListener("click", () => { if (i < FUSION_FRAMES.length - 1) { i++; draw(); } });
  prev.addEventListener("click", () => { if (i > 0) { i--; draw(); } });
  reset.addEventListener("click", () => { i = 0; draw(); });
  root.addEventListener("keydown", (e) => {
    if (e.key === "ArrowRight") { step.click(); e.preventDefault(); }
    if (e.key === "ArrowLeft") { prev.click(); e.preventDefault(); }
  });
  root.tabIndex = 0;
  draw();
}

// ── KAM: Push and δ as scripted constellation steps ──────────────────────
// The galaxy reducer is a Krivine machine *as a constellation*: a process
// is +P(st(M, π)) — a focused term M over a stack π. Two of its rules:
//
//   Push : a(M,N) ⋆ π          ↝  M ⋆ (N · π)        (uncurry an application)
//   δ    : :Name ⋆ π           ↝  body• ⋆ π          (unfold a definition)
//
// Scripted here on  ((:double 2)) , with  :double X = add X X .

const KAM_FRAMES = [
  {
    title: "A process",
    note: "A KAM process is the single ray +P(st(M, π)): a focused term M " +
      "over a stack π. Here M = a(:double, 2) — :double applied to 2 — and " +
      "the stack is empty (eps).",
    ray: "+P( st( a(:double, 2), eps ) )",
    rule: null,
  },
  {
    title: "Push",
    note: "The focus is an application node a(M,N). The Push rule uncurries " +
      "it: the operator becomes the new focus, the operand is pushed onto " +
      "the stack. No unification — a pure structural rewrite.",
    ray: "+P( st( :double, 2 · eps ) )",
    rule: "Push :  a(M,N) ⋆ π  ↝  M ⋆ (N · π)",
  },
  {
    title: "δ — unfold a definition",
    note: "The focus is the definition atom :double. Its δ-star rewrites " +
      "it to its closed body. The most general unifier is definitionally " +
      "{π ↦ the live stack}: no scan, no α-rename, no general unification.",
    ray: "+P( st( add(X, X)[X:=•], 2 · eps ) )",
    rule: "δ :  :double ⋆ π  ↝  (add X X)• ⋆ π",
  },
  {
    title: "Push the operand into place",
    note: "Another Push moves the argument 2 off the stack into the body. " +
      "The strict primitive add now has both operands and can fire.",
    ray: "+P( st( add(2, 2), eps ) )",
    rule: "Push (again) :  a(M,N) ⋆ π  ↝  M ⋆ (N · π)",
  },
  {
    title: "Normal form",
    note: "add resolves to 4. No redex remains; the readback of the final " +
      "ray is the result.",
    ray: "+P( st( 4, eps ) )",
    rule: null,
    done: true,
  },
];

function mountKam(root) {
  let i = 0;
  const wrap = htmlEl("div", "viz");
  const stage = htmlEl("div", "viz-stage viz-stage--kam");
  const read = htmlEl("div", "viz-read");
  const controls = htmlEl("div", "viz-controls");
  const prev = htmlEl("button", "viz-btn", "‹ Back");
  const step = htmlEl("button", "viz-btn viz-btn--primary", "Step ›");
  const reset = htmlEl("button", "viz-btn", "Restart");
  const pos = htmlEl("span", "viz-pos");
  prev.type = step.type = reset.type = "button";
  controls.append(prev, step, reset, pos);
  wrap.append(stage, read, controls);
  root.appendChild(wrap);

  function draw() {
    const f = KAM_FRAMES[i];
    stage.innerHTML = "";
    const c = htmlEl("div", "stx-constellation");
    const sd = htmlEl("div", "stx-star" + (f.done ? "" : " is-active"));
    sd.appendChild(htmlEl("span",
      "stx-ray stx-ray--pos" + (f.done ? " is-result" : " is-next"),
      f.ray.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")));
    c.appendChild(sd);
    stage.appendChild(c);

    let html = `<div class="viz-read__h">${f.title}</div>` +
      `<p class="viz-read__n">${f.note}</p>`;
    if (f.rule) html += `<div class="viz-read__row"><span class="viz-lab">rule</span>` +
      `<code>${f.rule}</code></div>`;
    read.innerHTML = html;
    pos.textContent = `${i + 1} / ${KAM_FRAMES.length}`;
    prev.disabled = i === 0;
    step.disabled = i === KAM_FRAMES.length - 1;
  }
  step.addEventListener("click", () => { if (i < KAM_FRAMES.length - 1) { i++; draw(); } });
  prev.addEventListener("click", () => { if (i > 0) { i--; draw(); } });
  reset.addEventListener("click", () => { i = 0; draw(); });
  root.addEventListener("keydown", (e) => {
    if (e.key === "ArrowRight") { step.click(); e.preventDefault(); }
    if (e.key === "ArrowLeft") { prev.click(); e.preventDefault(); }
  });
  root.tabIndex = 0;
  draw();
}

function boot() {
  const a = document.getElementById("viz-fusion");
  if (a) mountFusion(a);
  const b = document.getElementById("viz-kam");
  if (b) mountKam(b);
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", boot);
} else {
  boot();
}
