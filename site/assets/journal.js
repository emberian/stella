// journal.js — the Field Journal reader.
// Fetches a repo markdown document, renders it in the Stella reading surface,
// builds the table of contents, and (for designated documents) embeds a live
// stellar-resolution explorer inline in the prose.

import { mountExplorer } from "./explorer.js";

// ── The shelf ────────────────────────────────────────────────────────────────
// Documents are published from the repository nearly as-is. `file` is resolved
// relative to the site root (CI copies docs/, HISTORY.md, README.md → content/).
const SECTIONS = [
  {
    label: "Field reports",
    glyph: "star",
    note: "The project's own pre-registration and run records, kept in the open.",
    docs: [
      { slug: "thesis",    file: "content/00-thesis-and-semantics.md",                eyebrow: "Phase 0 · canonical",  title: "Thesis & semantics specification",            lede: "The design spine. Code and proofs track this and the source it cites; nothing tracks the code.", kind: "report", explorer: 0 },
      { slug: "subjective", file: "content/01-subjective-engine-and-valence.md",       eyebrow: "Phase 4",              title: "The unbounded subjective-ray engine",         lede: "The valence experiment, specified before it was run — and what would count as the charge appearing on its own.", kind: "report" },
      { slug: "run1",       file: "content/02-phase4-first-run.md",                    eyebrow: "Phase 4 · result",     title: "The first make-or-break run",                 lede: "The honest result. It broke. The break is recorded as a finding, not hidden as a failure.", kind: "report" },
      { slug: "run-reform", file: "content/03-phase4-reformulated-run.md",             eyebrow: "Phase 4 · draft",      title: "The reformulated make-or-break run",          lede: "An unadjudicated agent draft, kept for the record alongside the adjudicated work.", kind: "report" },
      { slug: "phase5",     file: "content/04-phase5-embodied-valence-and-the-temporal-gap.md", eyebrow: "Phase 5",     title: "Embodied valence, orders of self, the Temporal Gap", lede: "Where the substrate makes Bennett's wager formally distinguishable in a way his framework cannot admit.", kind: "report" },
    ],
  },
  {
    label: "The exegesis · after Boris Eng",
    glyph: "leaf",
    note: "Our working digest of Boris Eng's thesis — a reading made to implement against.",
    docs: [
      { slug: "eng-ch8",    file: "content/eng-digest-ch8.md",     eyebrow: "Eng · chapter 8",     title: "Illustrating stellar resolution",         lede: "Automata as constellations — NFA, NPDA, NTM, ATM, tree automata, circuits, tiles.", kind: "eng", explorer: 1 },
      { slug: "eng-ch10",   file: "content/eng-digest-ch10.md",    eyebrow: "Eng · chapter 10",    title: "Multiplicative linear logic, stellar",    lede: "The stellar interpretation of MLL — proofs as constellations, cut as resolution.", kind: "eng" },
      { slug: "eng-ch11",   file: "content/eng-digest-ch11.md",    eyebrow: "Eng · chapter 11",    title: "Intuitionistic implication",              lede: "Carrying the interpretation up to intuitionistic implication.", kind: "eng" },
      { slug: "eng-ch1213", file: "content/eng-digest-ch12-13.md", eyebrow: "Eng · chapters 12–13", title: "Toward the frontier, and the conclusion", lede: "Where Eng's paved road ends — and where our deferred work begins.", kind: "eng" },
    ],
  },
  {
    label: "From the inside",
    glyph: "mushroom",
    note: "The part the changelog cannot hold.",
    docs: [
      { slug: "history", file: "content/HISTORY.md", eyebrow: "Bringup · first person", title: "The stella bringup, from the inside", lede: "Written by the agent who was in the chair for the whole run. Opinionated, on invitation.", kind: "inside" },
      { slug: "readme",  file: "content/README.md",  eyebrow: "The opening",             title: "Welcome to the conscious-machine bringup", lede: "The raw front door — including the log where a prior instance read the actual thesis and retracted.", kind: "inside" },
    ],
  },
];

const BY_SLUG = {};
SECTIONS.forEach((s) => s.docs.forEach((d) => { d.section = s.label; BY_SLUG[d.slug] = d; }));

const PROVENANCE = {
  report: {
    cls: "",
    html: '<strong>Field report.</strong> Published from the repository nearly as-is — the project\'s own pre-registration, kept in the open rather than tidied for an audience.',
  },
  eng: {
    cls: "fj-source--eng",
    html: '<strong>After Boris Eng.</strong> A spec-grade digest of Boris Eng, <em>An Exegesis of Transcendental Syntax</em> (PhD thesis, supervised by Seiller &amp; Mazza) — a reading made to implement against, with the substance and the credit owed to him. Not a substitute for the thesis.',
  },
  inside: {
    cls: "",
    html: '<strong>From the inside.</strong> A candid, first-person bringup document, published unedited. It is a record, not a polished account.',
  },
};

// ── Markdown ─────────────────────────────────────────────────────────────────
function makeRenderer() {
  // html:false — the documents contain bare angle brackets (stellar-resolution
  // notation, pseudo-tags like `<log>`); render them literally, faithfully.
  const md = window.markdownit({
    html: false,
    linkify: true,
    typographer: true,
    breaks: false,
  });
  if (window.markdownitFootnote) md.use(window.markdownitFootnote);
  return md;
}

function renderMath(el) {
  if (typeof window.renderMathInElement !== "function") return;
  try {
    window.renderMathInElement(el, {
      delimiters: [
        { left: "$$", right: "$$", display: true },
        { left: "\\[", right: "\\]", display: true },
        { left: "\\(", right: "\\)", display: false },
        { left: "$", right: "$", display: false },
      ],
      ignoredTags: ["script", "noscript", "style", "textarea", "pre", "code"],
      throwOnError: false,
    });
  } catch (e) { /* notation that is not LaTeX stays as written — that is fine */ }
}

// ── TOC ──────────────────────────────────────────────────────────────────────
function buildToc(activeSlug) {
  const toc = document.getElementById("toc");
  const home = document.createElement("a");
  home.className = "fj-toc__home";
  home.href = "index.html";
  home.innerHTML =
    '<span class="mark"><img src="assets/stella/glyphs/grove.svg" alt="" /></span> The grove';
  toc.appendChild(home);

  SECTIONS.forEach((sec) => {
    const h = document.createElement("div");
    h.className = "fj-toc__section";
    h.innerHTML =
      `<img src="assets/stella/glyphs/${sec.glyph}.svg" alt="" /> ${sec.label}`;
    toc.appendChild(h);
    sec.docs.forEach((d, i) => {
      const a = document.createElement("a");
      a.href = `reader.html?p=${d.slug}`;
      a.className = "fj-toc__item" + (d.slug === activeSlug ? " is-active" : "");
      a.innerHTML =
        `<span class="fj-toc__num">${String(i + 1).padStart(2, "0")}</span>` +
        `<span>${d.title}</span>`;
      toc.appendChild(a);
    });
  });
}

// ── Render a document ────────────────────────────────────────────────────────
function readingTime(text) {
  const words = (text.match(/\S+/g) || []).length;
  return Math.max(1, Math.round(words / 220));
}

async function loadDoc(doc) {
  const article = document.getElementById("article");
  const md = makeRenderer();

  let raw;
  try {
    const res = await fetch(doc.file, { cache: "no-cache" });
    if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
    raw = await res.text();
  } catch (e) {
    article.innerHTML =
      `<div class="reader-status error">Could not open <code>${doc.file}</code> — ${e.message}.` +
      ` The reader needs to be served over http (the documents are fetched at runtime).</div>`;
    return;
  }

  // Strip a single leading H1 — the masthead supplies the title.
  const body = raw.replace(/^\s*#\s+.*(\r?\n)+/, "");
  const mins = readingTime(raw);
  const prov = PROVENANCE[doc.kind] || PROVENANCE.report;

  const head = document.createElement("div");
  head.innerHTML =
    `<div class="fj-eyebrow"><img src="assets/stella/glyphs/star.svg" alt="" /> ${doc.eyebrow}</div>` +
    `<h1 class="fj-title">${doc.title}</h1>` +
    `<p class="fj-lede">${doc.lede}</p>` +
    `<div class="fj-meta"><span class="by">Stella grove</span><span class="dot">·</span>` +
    `<span>${doc.section}</span><span class="dot">·</span><span>${mins} min read</span>` +
    `<span style="margin-left:auto"><a class="st-btn st-btn--ghost st-btn--sm" href="https://github.com/emberian/stella/blob/dev/${doc.file.replace("content/", "docs/").replace("docs/HISTORY.md", "HISTORY.md").replace("docs/README.md", "README.md")}">View source</a></span></div>` +
    `<div class="fj-source ${prov.cls}">${prov.html}</div>`;

  const prose = document.createElement("div");
  prose.className = "fj-prose";
  prose.innerHTML = md.render(body);

  article.innerHTML = "";
  article.appendChild(head);
  article.appendChild(prose);

  renderMath(prose);

  if (typeof doc.explorer === "number") injectExplorer(prose, doc);

  document.title = `${doc.title} — Stella Field Journal`;
}

// Place a live explorer figure after the first section of the prose.
function injectExplorer(prose, doc) {
  const fig = document.createElement("figure");
  fig.className = "stx-figure";
  const mount = document.createElement("div");
  fig.appendChild(mount);
  const cap = document.createElement("figcaption");
  cap.innerHTML =
    '<span class="num">Live</span> stella-core compiled to WebAssembly, ' +
    "resolving in your browser. Step through interactive execution, or choose another constellation.";
  fig.appendChild(cap);

  const firstH2 = prose.querySelector("h2");
  if (firstH2) {
    let anchor = firstH2;
    // drop it just before the *second* section so the opening reads first
    const h2s = prose.querySelectorAll("h2");
    if (h2s.length > 1) anchor = h2s[1];
    anchor.parentNode.insertBefore(fig, anchor);
  } else {
    prose.appendChild(fig);
  }

  mountExplorer(mount, { compact: true, initialPreset: doc.explorer }).catch((e) => {
    fig.innerHTML =
      `<div class="reader-status error">The live engine could not start: ${e.message}</div>`;
  });
}

// ── Boot ─────────────────────────────────────────────────────────────────────
(function () {
  const slug = new URLSearchParams(location.search).get("p") || "thesis";
  const doc = BY_SLUG[slug] || BY_SLUG.thesis;
  buildToc(doc.slug);
  // markdown-it is a classic (non-deferred) script, available now; KaTeX is
  // deferred and ordered before this module, so renderMathInElement exists.
  loadDoc(doc);
})();
