# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "markdown-it-py==3.0.0",
#   "mdit-py-plugins==0.4.2",
#   "latex2mathml",
# ]
# ///
"""Prebake the Stella site to fully static HTML.

The reading pages are rendered from the repository's markdown at build time —
no runtime fetch, no client-side markdown or math. A snapshot of any page in a
web archive is the whole page. Math is emitted as MathML (rendered natively by
browsers, no script, no stylesheet). The only JavaScript anywhere is the
optional WebAssembly explorer, which is a tool, not content.

    uv run --script site/build.py        # writes site/r/*.html
"""
from __future__ import annotations

import html
import json
import pathlib
import re
import subprocess

from markdown_it import MarkdownIt
from mdit_py_plugins.footnote import footnote_plugin
from mdit_py_plugins.dollarmath import dollarmath_plugin
import latex2mathml.converter

ROOT = pathlib.Path(__file__).resolve().parent.parent
SITE = ROOT / "site"
OUT = SITE / "r"

# ── The shelf ────────────────────────────────────────────────────────────────
# The public site is narrow: stellar resolution itself, read through Boris
# Eng's exegesis, plus the live engine. The implementation project (the applied
# arm — valence, the bringup) lives quietly under /cmi/.

STELLAR = [
    dict(slug="eng-ch8",    src="docs/eng-digest-ch8.md",     eyebrow="Eng · chapter 8",      title="Illustrating stellar resolution",        lede="Automata as constellations — finite, pushdown, Turing, alternating, tree automata, circuits, and tile systems, each as a constellation that resolves.", kind="eng"),
    dict(slug="eng-ch10",   src="docs/eng-digest-ch10.md",    eyebrow="Eng · chapter 10",     title="Multiplicative linear logic, stellar",   lede="The stellar interpretation of MLL: proofs become constellations, cut becomes resolution, correctness becomes a property of execution.", kind="eng"),
    dict(slug="eng-ch11",   src="docs/eng-digest-ch11.md",    eyebrow="Eng · chapter 11",     title="Intuitionistic implication",             lede="Carrying the interpretation up to intuitionistic implication.", kind="eng"),
    dict(slug="eng-ch1213", src="docs/eng-digest-ch12-13.md", eyebrow="Eng · chapters 12–13", title="Toward the frontier, and the conclusion", lede="Where the shared mechanism shows through — and where the paved road ends.", kind="eng"),
]

CMI = [
    dict(slug="thesis",     src="docs/00-thesis-and-semantics.md",                 eyebrow="Phase 0 · canonical", title="Thesis & semantics specification",        lede="The design spine for the implementation project. Code and proofs track this and the source it cites.", kind="report"),
    dict(slug="subjective", src="docs/01-subjective-engine-and-valence.md",         eyebrow="Phase 4",             title="The unbounded subjective-ray engine",     lede="The valence experiment, specified before it was run.", kind="report"),
    dict(slug="run1",       src="docs/02-phase4-first-run.md",                      eyebrow="Phase 4 · result",    title="The first make-or-break run",             lede="It broke; the break is recorded as a finding.", kind="report"),
    dict(slug="run-reform", src="docs/03-phase4-reformulated-run.md",               eyebrow="Phase 4 · draft",     title="The reformulated make-or-break run",      lede="An unadjudicated draft, kept for the record.", kind="report"),
    dict(slug="phase5",     src="docs/04-phase5-embodied-valence-and-the-temporal-gap.md", eyebrow="Phase 5",      title="Embodied valence, orders of self, the Temporal Gap", lede="Where the substrate makes a wager about time formally distinguishable.", kind="report"),
    dict(slug="phase5-onset", src="docs/06-phase5-coherent-reorganization-under-selection.md", eyebrow="Phase 5 · draft", title="Coherent reorganization under selection", lede="A drafted, unlocked pre-registration. The regress closed: an onset study, not an origin claim. Negative-only, by its nature.", kind="report"),
    dict(slug="history",    src="HISTORY.md",                                      eyebrow="Bringup · first person", title="The bringup, from the inside",        lede="A candid, first-person account of the run. A record, not a polished account.", kind="inside"),
    dict(slug="history-0517", src="HISTORY-2026-05-17.md",                          eyebrow="Bringup · first person", title="The long untangling, from the inside", lede="The second long session: the regress, the errors, the deflations. Huge as method, not as result. Written deflated on purpose.", kind="inside"),
    dict(slug="readme",     src="README.md",                                       eyebrow="The opening",         title="The project front door",                  lede="The raw opening of the implementation project.", kind="inside"),
]

PROVENANCE = {
    "eng": ("fj-source--eng",
            "<strong>After Boris Eng.</strong> A spec-grade digest of Boris Eng, "
            "<em>An Exegesis of Transcendental Syntax</em> (PhD thesis, supervised "
            "by Seiller &amp; Mazza) — a reading made to implement against, with the "
            "substance and the credit owed to him. Not a substitute for the thesis."),
    "report": ("",
            "<strong>Field report.</strong> Part of the implementation project, "
            "published from the repository nearly as-is — pre-registration kept in "
            "the open rather than tidied for an audience."),
    "inside": ("",
            "<strong>From the inside.</strong> A candid, first-person document, "
            "published unedited."),
}


def tex2mathml(content: str, opts: dict) -> str:
    display = bool(opts.get("display_mode"))
    try:
        return latex2mathml.converter.convert(
            content, display="block" if display else "inline"
        )
    except Exception:
        # Never lose content: fall back to the verbatim source.
        tag = "div" if display else "span"
        return f'<{tag} class="tex-fallback"><code>{html.escape(content)}</code></{tag}>'


def make_md() -> MarkdownIt:
    md = (
        MarkdownIt("commonmark", {"html": False, "typographer": True, "linkify": True})
        .enable(["table", "strikethrough"])
        .use(footnote_plugin)
        .use(dollarmath_plugin, double_inline=True, renderer=tex2mathml)
    )
    return md


def source_url(src: str) -> str:
    return f"https://github.com/emberian/stella/blob/dev/{src}"


def nav(active: str, prefix: str) -> str:
    def link(href, label, key):
        cls = "site-nav__link is-active" if key == active else "site-nav__link"
        return f'<a class="{cls}" href="{prefix}{href}">{label}</a>'
    return (
        f'<nav class="site-nav">'
        f'<a class="site-nav__brand" href="{prefix}index.html">'
        f'<span class="mark"><img src="{prefix}assets/stella/glyphs/star.svg" alt="" /></span>'
        f'<span><span class="site-nav__name">Stellar resolution</span>'
        f'<span class="site-nav__sub">a computational model · after Eng</span></span></a>'
        f'<div class="site-nav__links">'
        + link("index.html", "The model", "home")
        + link("r/eng-ch8.html", "The exegesis", "exegesis")
        + link("r/internals.html", "The engine", "engine")
        + link("explore.html", "Explore", "explore")
        + link("r/primer.html", "A first reading", "primer")
        + "</div></nav>"
    )


# The stellar TOC opens with two generated pages (not digests).
STELLAR_TOP = [
    {"slug": "primer", "title": "A first reading"},
    {"slug": "notation", "title": "Notation & glossary"},
]

# The engine pages — generated, not digests; about the implementation
# itself (techniques, an illustrative visualizer, the open measurement).
ENGINE = [
    {"slug": "internals",  "title": "How the engine is built"},
    {"slug": "visualize",  "title": "Watch a step, by hand"},
    {"slug": "measure",    "title": "Measure, don't guess"},
]


def order_for(coll_name: str) -> list[dict]:
    """Linear reading order, for prev/next."""
    if coll_name == "stellar":
        return STELLAR_TOP + STELLAR
    if coll_name == "engine":
        return ENGINE
    return CMI


def pager(coll_name: str, slug: str) -> str:
    """Prev/next footer within a collection (all pages live in r/)."""
    seq = order_for(coll_name)
    i = next((k for k, d in enumerate(seq) if d["slug"] == slug), None)
    if i is None:
        return ""
    prev_d = seq[i - 1] if i > 0 else None
    next_d = seq[i + 1] if i + 1 < len(seq) else None
    L = (f'<a class="fj-pager__l" href="{prev_d["slug"]}.html">'
         f'<span class="fj-pager__dir">‹ Previous</span>'
         f'<span class="fj-pager__t">{html.escape(prev_d["title"])}</span></a>'
         if prev_d else "<span></span>")
    R = (f'<a class="fj-pager__r" href="{next_d["slug"]}.html">'
         f'<span class="fj-pager__dir">Next ›</span>'
         f'<span class="fj-pager__t">{html.escape(next_d["title"])}</span></a>'
         if next_d else "<span></span>")
    return f'<nav class="fj-pager">{L}{R}</nav>'


def toc(collection: list[dict], active_slug: str, label: str, glyph: str,
        home_href: str, home_label: str, prefix: str,
        extra_top: list[dict] | None = None) -> str:
    items = [
        f'<a class="fj-toc__home" href="{prefix}{home_href}">'
        f'<span class="mark"><img src="{prefix}assets/stella/glyphs/{glyph}.svg" alt="" /></span>'
        f"{home_label}</a>",
        f'<div class="fj-toc__section">'
        f'<img src="{prefix}assets/stella/glyphs/{glyph}.svg" alt="" /> {label}</div>',
    ]
    seq = (extra_top or []) + collection
    for i, d in enumerate(seq):
        cls = "fj-toc__item" + (" is-active" if d["slug"] == active_slug else "")
        items.append(
            f'<a class="{cls}" href="{d["slug"]}.html">'
            f'<span class="fj-toc__num">{i + 1:02d}</span>'
            f'<span>{html.escape(d["title"])}</span></a>'
        )
    return f'<aside class="fj-toc" aria-label="Contents">{"".join(items)}</aside>'


PAGE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>{title} — Stellar resolution</title>
<meta name="description" content="{desc}" />
<meta property="og:type" content="article" />
<meta property="og:site_name" content="Stellar resolution" />
<meta property="og:title" content="{title}" />
<meta property="og:description" content="{desc}" />
<meta name="twitter:card" content="summary" />{robots}
<link rel="icon" href="{prefix}assets/stella/logo/stella-mark.svg" />
<link rel="stylesheet" href="{prefix}assets/stella/colors_and_type.css" />
<link rel="stylesheet" href="{prefix}assets/stella/stella.css" />
<link rel="stylesheet" href="{prefix}assets/stella/journal.css" />
<link rel="stylesheet" href="{prefix}assets/site.css" />
</head>
<body class="stella-paper">
<a class="skip-link" href="#article">Skip to the reading</a>
{nav}
<div class="fj-layout">
{toc}
<main class="fj-reader">
<article class="fj-article" id="article">
<div class="fj-eyebrow"><img src="{prefix}assets/stella/glyphs/star.svg" alt="" /> {eyebrow}</div>
<h1 class="fj-title">{title}</h1>
<p class="fj-lede">{lede}</p>
<div class="fj-meta"><span class="by">Stella</span><span class="dot">·</span>
<span>{section}</span><span class="dot">·</span><span>{mins} min read</span>
<span style="margin-left:auto"><a class="st-btn st-btn--ghost st-btn--sm" href="{src_url}">View source</a></span></div>
<div class="fj-source {prov_cls}">{prov_html}</div>
<div class="fj-prose">
{body}
</div>
{footer}
</article>
</main>
</div>
</body>
</html>
"""


def reading_time(text: str) -> int:
    return max(1, round(len(re.findall(r"\S+", text)) / 220))


def render_doc(d: dict, collection: list[dict], coll_name: str) -> str:
    raw = (ROOT / d["src"]).read_text(encoding="utf-8")
    body_md = re.sub(r"\A\s*#\s+.*(?:\r?\n)+", "", raw, count=1)  # drop leading H1
    # Ensure a standalone $$…$$ is a *block* equation: dollarmath only treats
    # it as a block when it is set off by blank lines.
    body_md = re.sub(
        r"(?m)^[ \t]*(\$\$.+?\$\$)[ \t]*$",
        lambda m: "\n" + m.group(1) + "\n",
        body_md,
    )
    body = make_md().render(body_md)
    prov_cls, prov_html = PROVENANCE[d["kind"]]

    if coll_name == "stellar":
        the_nav = nav("exegesis" if d["slug"].startswith("eng") else "home", "../")
        the_toc = toc(collection, d["slug"], "The exegesis · after Boris Eng",
                      "leaf", "index.html", "The model", "../",
                      extra_top=STELLAR_TOP)
        section = "The exegesis"
    else:
        the_nav = nav("cmi", "../")
        the_toc = toc(collection, d["slug"], "The implementation project",
                      "mushroom", "cmi/index.html", "Implementation", "../")
        section = "Implementation project"

    robots = ('\n<meta name="robots" content="noindex,nofollow" />'
              if coll_name == "cmi" else "")
    return PAGE.format(
        prefix="../",
        robots=robots,
        title=html.escape(d["title"]),
        desc=html.escape(d["lede"]),
        nav=the_nav,
        toc=the_toc,
        eyebrow=html.escape(d["eyebrow"]),
        lede=html.escape(d["lede"]),
        section=section,
        mins=reading_time(raw),
        src_url=source_url(d["src"]),
        prov_cls=prov_cls,
        prov_html=prov_html,
        body=body,
        footer=pager(coll_name, d["slug"]),
    )


# ── The primer: a worked example, prebaked from the engine ──────────────────
# build.py runs the real engine (`stella-viz --steps`) and renders each step as
# the *same* star/ray markup the live explorer uses — but static. No Graphviz,
# no JavaScript: the figures are in the HTML, so a web-archive snapshot keeps
# the whole worked example.

def _split_top(s: str) -> list[str]:
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1; cur += ch
        elif ch == ")":
            depth -= 1; cur += ch
        elif ch == "," and depth == 0:
            parts.append(cur); cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def _ray_pol(r: str) -> str:
    r = r.strip()
    if r.startswith("+"):
        return "pos"
    if r.startswith("-") or r.startswith("−"):
        return "neg"
    return "neu"


def _constellation_html(psi_stars: list[str], hot: tuple[int, int] | None) -> str:
    if not psi_stars:
        return ('<div class="stx-constellation">'
                '<div class="stx-star stx-star--empty">∅ — empty interaction '
                'space</div></div>')
    out = []
    for si, star in enumerate(psi_stars):
        inner = star.strip()
        if inner.startswith("["):
            inner = inner[1:]
        if inner.endswith("]"):
            inner = inner[:-1]
        rays = _split_top(inner)
        cells = []
        for ri, r in enumerate(rays):
            is_hot = hot is not None and hot == (si, ri)
            cells.append(
                f'<span class="stx-ray stx-ray--{_ray_pol(r)}'
                f'{" is-next" if is_hot else ""}">{html.escape(r)}</span>'
            )
        active = " is-active" if hot is not None and hot[0] == si else ""
        out.append(f'<div class="stx-star{active}">'
                   + '<span class="stx-comma">,</span>'.join(cells) + "</div>")
    return f'<div class="stx-constellation">{"".join(out)}</div>'


_HOT_RE = re.compile(r"star\[(\d+)\]\s*ray\[(\d+)\]")


def engine_steps() -> list[dict] | None:
    """Run the real engine to get every preset's per-step trace, or None."""
    try:
        r = subprocess.run(
            ["cargo", "run", "-q", "-p", "stella-viz", "--", "--steps"],
            cwd=ROOT, capture_output=True, text=True, timeout=900,
        )
    except Exception as e:  # noqa: BLE001
        print(f"  primer: engine unavailable ({e}); skipping")
        return None
    if r.returncode != 0:
        print(f"  primer: engine failed (rc={r.returncode}); skipping")
        return None
    try:
        return json.loads(r.stdout)
    except json.JSONDecodeError as e:
        print(f"  primer: bad engine JSON ({e}); skipping")
        return None


PRIMER_INTRO = """
<p>Stellar resolution is small enough to hold in your head. This page
introduces it from nothing, then runs one example all the way to its answer —
not with a diagram drawn by hand, but with the same engine the
<a href="../explore.html">explorer</a> uses, its every step rendered here as
static text. Nothing on this page runs; it has already run.</p>

<h2>Three definitions</h2>
<p>A <strong>ray</strong> is a first-order term — a variable, or a function
symbol applied to rays — optionally carrying a <em>polarity</em>, written
<code>+</code> or <code>−</code>. A <strong>star</strong> is a finite set of
rays, written between brackets: <code>[+f(X), −g(X)]</code>. A
<strong>constellation</strong> is a finite set of stars. By convention an
uppercase head is a variable; everything else is a function symbol, and a
symbol with no arguments is a constant.</p>

<p>That is the entire ontology. There is no state, no store, no clock.</p>

<h2>One rule</h2>
<p>Two rays are <em>matchable</em> when they have the same underlying symbol,
opposite polarity, and their arguments <em>unify</em> — there is a substitution
of terms for variables making them syntactically equal. When a positive ray in
one star is matchable with a negative ray in another, the constellation can
<strong>resolve</strong> there: the two stars fuse into one, the matched pair
of rays is consumed, and the most general unifier is applied to everything that
remains. Resolution repeats until no matchable pair is left. A constellation in
that state is in <strong>normal form</strong>, and the normal form is the
result of the computation.</p>

<p>Crucially there is no order to any of this. Every matchable pair is a place
the constellation could resolve, all at once; the engine here happens to take
the first in a left-to-right reading, but that is an implementation's choice,
not the model's. This is what is meant by computing as <em>interaction</em>
rather than <em>stepping</em>.</p>

<h2>A worked example: 2 + 2</h2>
<p>Addition on the unary naturals (<code>0</code>, <code>s(0)</code>,
<code>s(s(0))</code>, …) is two stars — the reference constellation Φ:</p>
<pre><code>[+add(0, Y, Y)]
[−add(X, Y, Z), +add(s(X), Y, s(Z))]</code></pre>
<p>The first says <em>0 + Y = Y</em>. The second says <em>if X + Y = Z then
s(X) + Y = s(Z)</em> — the negative <code>−add</code> ray is a request, the
positive one its conclusion. To ask for 2 + 2 we put a query into the
interaction space Ψ — a request for the sum, paired with a neutral ray
<code>R</code> that will carry the answer out:</p>
<pre><code>[−add(s(s(0)), s(s(0)), R), R]</code></pre>
<p>Now we let it resolve. Each step below is the interaction space at that
point; the highlighted ray is the one that resolves next, and the unifier it
computes is shown beneath.</p>
"""


def build_primer(presets: list[dict]) -> bool:
    target = next(
        (p for p in presets if "Horn addition" in p.get("name", "")), None
    )
    if target is None or not target.get("steps"):
        print("  primer: no Horn-addition preset; skipping")
        return False
    steps = target["steps"]
    figs = []
    for k, s in enumerate(steps):
        m = _HOT_RE.search(s.get("active_ray") or "")
        hot = (int(m.group(1)), int(m.group(2))) if m else None
        last = s.get("is_final") or k == len(steps) - 1
        if last:
            cap = ("<span class=\"num\">Normal form</span>No matchable pair "
                   "remains. The neutral rays left in Ψ are the answer — "
                   "<code>2 + 2 = s(s(s(s(0))))</code>.")
        else:
            mgu = s.get("mgu") or []
            binds = " · ".join(f"{v} ↦ {t}" for v, t in mgu) or "—"
            cap = (f'<span class="num">Step {s["step"]}</span>'
                   f"The highlighted ray resolves next; "
                   f"most general unifier: <code>{html.escape(binds)}</code>.")
        figs.append(
            '<figure class="stx-figure stx-figure--static">'
            + _constellation_html(s.get("psi_stars", []), hot)
            + f'<figcaption>{cap}</figcaption></figure>'
        )

    closing = (
        "<h2>What just happened</h2>"
        "<p>Each step fused the query with the second star of Φ, peeling one "
        "<code>s</code> off the first argument and remembering it on the "
        "result, until the first argument reached <code>0</code> and the base "
        "case discharged the request. No step was privileged; the engine simply "
        "kept resolving until nothing matched. The same machinery, unchanged, "
        "is what Eng's exegesis turns on automata, linear logic, circuits and "
        "tiles — read on, or open the "
        '<a href="../explore.html?preset=Horn%20addition">explorer</a> and run '
        "it yourself.</p>"
    )
    body = PRIMER_INTRO + "".join(figs) + closing

    out = PAGE.format(
        prefix="../",
        robots="",
        title="Stellar resolution — a first reading",
        desc="Stellar resolution from first principles, with a worked example "
             "run all the way to normal form — prebaked, static, no scripting.",
        nav=nav("home", "../"),
        toc=toc(STELLAR, "primer", "The exegesis · after Boris Eng", "leaf",
                "index.html", "The model", "../", extra_top=STELLAR_TOP),
        eyebrow="A first reading",
        lede="The model from nothing, then one example resolved to its answer "
             "by the engine itself.",
        section="Primer",
        mins=8,
        src_url="https://github.com/emberian/stella/blob/dev/site/build.py",
        prov_cls="",
        prov_html="<strong>Prebaked by the engine.</strong> Every figure below "
                  "was produced by running <code>stella-core</code> at build "
                  "time and rendering each step as static markup — the page "
                  "contains no script and fetches nothing.",
        body=body,
        footer=pager("stellar", "primer"),
    )
    (OUT / "primer.html").write_text(out, encoding="utf-8")
    print("  baked r/primer.html  ← engine (Horn addition, prebaked)")
    return True


NOTATION = """
<p>Stellar resolution and the literature it comes from use a compact notation.
This page is a key to the symbols and a glossary of the terms, so the
<a href="eng-ch8.html">exegesis</a> can be read without decoding as you go.</p>

<h2>Symbols</h2>
<table>
<thead><tr><th>Symbol</th><th>Reads as</th><th>Meaning</th></tr></thead>
<tbody>
<tr><td><code>+f</code> / <code>−f</code></td><td>polarised symbol</td>
  <td>A ray's head carrying a polarity. Only opposite polarities of the same
  underlying symbol can match.</td></tr>
<tr><td><code>[ r₁, r₂, … ]</code></td><td>a star</td>
  <td>A finite set of rays. The bracket is the star; commas separate rays.</td></tr>
<tr><td><code>Φ</code></td><td>phi — reference constellation</td>
  <td>The constellation supplying the rules; in IEx it is available without
  being consumed.</td></tr>
<tr><td><code>Ψ</code></td><td>psi — interaction space</td>
  <td>The constellation being resolved (the query and its evolving state).</td></tr>
<tr><td><code>⊢</code></td><td>turnstile</td>
  <td><code>Φ ⊢ Ψ</code>: resolving Ψ with reference Φ.</td></tr>
<tr><td><code>↝</code> / <code>↝*</code></td><td>resolves to (one / many steps)</td>
  <td>One resolution step; its reflexive-transitive closure.</td></tr>
<tr><td><code>★</code></td><td>encoding</td>
  <td><code>w★</code>, <code>M★</code>: the constellation encoding a word /
  machine.</td></tr>
<tr><td><code>IEx</code> · <code>Ex</code> · <code>AEx</code></td>
  <td>interactive / abstract / annotated execution</td>
  <td>The execution modes; IEx is the step-by-step one this site shows.</td></tr>
<tr><td><code>ɟ</code></td><td>concealing + noise filter</td>
  <td>An observation operator: erase polarised residue, keep the unpolarised
  rays — the visible output.</td></tr>
<tr><td><code>⊎</code> · <code>⋈</code></td><td>disjoint union · matchable</td>
  <td>Union of constellations; the relation that two rays can resolve.</td></tr>
<tr><td><code>ε</code> · <code>□</code></td><td>empty word · blank</td>
  <td>Constants used in the automata encodings.</td></tr>
</tbody>
</table>

<h2>Glossary</h2>
<p><strong>Ray.</strong> A first-order term, optionally polarised — the unit
that matches.</p>
<p><strong>Star.</strong> A finite set of rays; the thing that fuses.</p>
<p><strong>Constellation.</strong> A finite set of stars; the object that
resolves.</p>
<p><strong>Unification.</strong> A substitution of terms for variables making
two terms syntactically equal; the engine shows the <em>most general</em> one
at each step.</p>
<p><strong>Resolution / interaction.</strong> Replacing a matched ±ray pair by
fusing their stars and propagating the unifier. Concurrent: every matchable
pair is a site of interaction, not a scheduled step.</p>
<p><strong>Normal form.</strong> A constellation in which no pair is matchable;
its unpolarised rays are the result.</p>
<p><strong>Polycomputation.</strong> Computation realised as concurrent
interaction across a structured space rather than a sequence of steps — the
property that makes stellar resolution interesting as a substrate.</p>
<p>Read on with the <a href="../index.html">model</a>, the
<a href="primer.html">first reading</a>, or the
<a href="../explore.html">explorer</a>.</p>
"""


def build_notation() -> None:
    out = PAGE.format(
        prefix="../",
        robots="",
        title="Notation & glossary",
        desc="A key to the symbols of stellar resolution and transcendental "
             "syntax, and a short glossary.",
        nav=nav("home", "../"),
        toc=toc(STELLAR, "notation", "The exegesis · after Boris Eng", "leaf",
                "index.html", "The model", "../", extra_top=STELLAR_TOP),
        eyebrow="Reference",
        lede="A key to the symbols, and a short glossary of the terms.",
        section="Reference",
        mins=4,
        src_url="https://github.com/emberian/stella/blob/dev/site/build.py",
        prov_cls="",
        prov_html="<strong>Reference.</strong> A reading aid for the exegesis; "
                  "definitions follow Eng's usage.",
        body=NOTATION,
        footer=pager("stellar", "notation"),
    )
    (OUT / "notation.html").write_text(out, encoding="utf-8")
    print("  baked r/notation.html  ← reference")


# ── The engine pages ─────────────────────────────────────────────────────────
# Three generated pages about the implementation itself: the techniques (each
# claim links to the exact source line it rests on), an illustrative
# visualizer, and the honest, still-open measurement story. These are not
# digests of Eng; they are about the Rust in this repository, and every
# technical assertion is anchored to a file:line a reader can open.

GH = "https://github.com/emberian/stella/blob/dev"


def src(path: str, line: int | None = None, label: str | None = None) -> str:
    """An inline citation link to a source line on GitHub."""
    anchor = f"#L{line}" if line else ""
    shown = label or (f"{path.split('/')[-1]}:{line}" if line else path.split('/')[-1])
    return f'<a class="src-cite" href="{GH}/{path}{anchor}"><code>{shown}</code></a>'


INTERNALS = f"""
<p>The reading on stellar resolution is about a model. This page is about the
program that runs it: <code>stella-core</code>, a Rust implementation of the
operational semantics. It explains four techniques the engine uses, and the
discipline that keeps them honest. Every technical claim below links to the
exact source line it rests on — open them; the prose is only a guide.</p>

<p>One idea organises all four. There is a <strong>reference</strong>
implementation that is deliberately simple and is treated as the definition of
what the answer <em>is</em> — {src("crates/stella-core/src/interactive.rs", 861, "iex")},
the textbook left-to-right resolver. Everything faster is a separate
<strong>speculative</strong> tier that must produce a result the reference
would accept, checked by a single proven predicate
({src("crates/stella-core/src/faithfulness.rs", 115, "psi_compatible")}), with
a fall-back to the reference when it does not. Speed is never allowed to define
correctness.</p>

<h2>1 · The near-linear unifier</h2>

<p>Resolution is unification, run over and over, and the textbook unifier is
the dominant cost. {src("crates/stella-core/src/unify.rs", None, "unify.rs")}
is the Martelli–Montanari reference: after binding a variable it eagerly
re-applies that binding across the whole remaining worklist
({src("crates/stella-core/src/unify.rs", 100, "unify.rs:100–108")}) and
re-walks each term's variables per equation. The module header of the
replacement records the measurement that motivated it: that <code>unify</code>
is about <strong>53% of engine wall time</strong> at one galaxy workload
(Φ = 405 stars) — the single largest cost
({src("crates/stella-core/src/unify_fast.rs", 1, "unify_fast.rs:1–8")}).</p>

<p>{src("crates/stella-core/src/unify_fast.rs", 110, "unify_fast")} keeps the
same accept/reject behaviour but changes the data structures:</p>

<ul>
<li><strong>Triangular substitution + union-find.</strong> A variable points
either at another variable (a union-find link) or at a single non-variable
term — never eagerly expanded. <code>resolve</code> walks the chain with path
compression
({src("crates/stella-core/src/unify_fast.rs", 53, "unify_fast.rs:53–81")}), so
a binding costs O(1) instead of a sweep over every pending equation.</li>
<li><strong>A visited memo on resolved term pairs.</strong> Terms are
hash-consed, so each distinct subterm pair is structurally decomposed at most
once — the near-linear behaviour on the shared structure that DAG-shaped terms
produce
({src("crates/stella-core/src/unify_fast.rs", 143, "unify_fast.rs:143–148")}).</li>
<li><strong>A deferred occurs-check.</strong> Binding is O(1); acyclicity is
checked once, at the end, by a single iterative depth-first search over the
triangular store
({src("crates/stella-core/src/unify_fast.rs", 239, "store_has_cycle")}). A
cyclic store is exactly a genuine occurs-failure. This is the Martelli–
Montanari almost-linear arrangement.</li>
</ul>

<p>Measured effect on that galaxy workload: about <strong>2× total</strong>
engine time, with <code>unify</code> dropping from 53% to 9%
({src("docs/14-staged-compilation-futamura.md", 23, "docs/14 §0")}). It is a
per-step constant-factor win, not an asymptotic one — a distinction the
measurement page returns to.</p>

<p>Honesty about <em>this</em> claim is mechanised. The same module carries a
differential fuzz test that builds thousands of random term pairs and asserts
that <code>unify_fast</code> and the reference <code>unify</code> agree on
accept/reject, and that the fast unifier's substitution actually unifies the
inputs
({src("crates/stella-core/src/unify_fast.rs", 391, "fuzz_result_equivalent_to_reference_unify")}).
The most general unifier is unique only up to variable renaming, so the
faithfulness predicate compares answers up to that renaming rather than by
bytes
({src("crates/stella-core/src/unify_fast.rs", 19, "unify_fast.rs:19–22")}).</p>

<h2>2 · Σ(Φ) — the first Futamura projection, concretely</h2>

<p>The galaxy program is a fixed constellation Φ — 405 stars that never change
during a run. The generic interpreter still rediscovers, every single step,
which star to use and how its variables bind. Partial evaluation says: since Φ
is fixed, do that rediscovery <em>once</em>.</p>

<p>The first Futamura projection is the equation
<code>specialise(interpreter, program) = compiled&nbsp;program</code>. Here the
program is Φ and the residual is a closed, head-keyed transition table built
once per Φ — {src("crates/stella-core/src/spec_phi.rs", None, "spec_phi.rs")},
the module named <code>Σ(Φ)</code>. The classification is structural, not by
name. Every Φ star has the Krivine-machine shape
<code>[ −P(st(Mₙ,πₙ)), +P(st(Mₚ,πₚ)) ]</code>, and each maps to one closed
transition ({src("crates/stella-core/src/spec_phi.rs", 38, "spec_phi.rs:38–49")}):</p>

<table>
<thead><tr><th>Φ-star shape (structural)</th><th>Transition</th><th>What the step becomes</th></tr></thead>
<tbody>
<tr><td><code>Mₙ = a(_, _)</code> — an application node</td>
  <td><code>Unwind</code></td>
  <td>The verbatim Push rule <code>a(M,N)⋆π ↝ M⋆(N·π)</code>. A structural
  rewrite; no unification.</td></tr>
<tr><td><code>Mₙ = H()</code> nullary, <code>πₙ</code> a bare variable equal
  to <code>πₚ</code></td>
  <td><code>Delta(body)</code></td>
  <td>A definition <code>:N ↦ body•</code>. The body is closed, so the most
  general unifier is definitionally <code>{{π ↦ the live stack}}</code> — no
  scan, no renaming, no unification, no substitution.</td></tr>
<tr><td><code>Mₙ = H()</code> nullary, <code>πₙ = p₁·…·pₖ·Var</code> (every
  frame a variable)</td>
  <td><code>Splice {{ params, body }}</code></td>
  <td>A combinator: pop <code>k</code> stack frames, instantiate the fixed
  contractum positionally.</td></tr>
<tr><td>anything else (constructor-guarded <code>isnil</code>, strict numeric
  ops with no star)</td>
  <td><em>absent</em></td>
  <td>Deliberately not in the table — delegated to the generic forced path.
  This is the §49.50 boundary, kept exactly where the design needs it.</td></tr>
</tbody>
</table>

<p>The closed transition table for the galaxy is dominated by
<code>Delta</code>: 392 of the 405 stars are definition unfoldings. For those,
a step that was "rebuild the colour set, scan Φ, α-rename the matched star,
unify, apply the substitution" collapses to "look up the head, splice one
node". An invariant test asserts every <code>Delta</code> body is closed —
the property that makes the no-unification shortcut sound
({src("crates/stella-core/src/spec_phi.rs", 292, "delta_bodies_are_ground")}).
Another asserts the boundary holds: <code>isnil</code> and the strict numeric
ops are <em>not</em> specialised
({src("crates/stella-core/src/spec_phi.rs", 254, "galaxy_table_delta_count_and_boundary")}).</p>

<p>The design is explicit that this is a per-step lever, not a termination
fix: it makes a long reduction faster, not finite
({src("docs/14-staged-compilation-futamura.md", 214, "docs/14 §2")},
{src("docs/17-futamura-implementation-plan.md", 7, "docs/17 §0")}). Why it is
nonetheless sound to special-case at all: a δ-transition <em>is</em> the
literal denotation of its δ-star — provable by inspecting the one rule, not by
testing — so the speculative driver cannot drift from the reference by
construction
({src("docs/14-staged-compilation-futamura.md", 238, "docs/14 §3")}).</p>

<h2>3 · Verified speculation: two tiers and deopt</h2>

<p>This is the discipline that lets the engine be fast without ever letting
fast define correct. The reference resolver
{src("crates/stella-core/src/interactive.rs", 861, "iex")} is the oracle: it
hard-codes the reference unifier and is statically unreachable from any fast
tier. Each accelerated tier (the <code>unify_fast</code> seam, the tabled
tier, the Σ(Φ) driver) is a sibling that runs only on the fast path and is
checked against the oracle by
{src("crates/stella-core/src/faithfulness.rs", 115, "psi_compatible")}.</p>

<p>That predicate is the whole trust boundary, so it is worth stating exactly
what it does: it conceals the polarised scaffolding, keeps the visible
unpolarised rays, canonicalises each surviving star up to variable renaming,
and compares the two results <em>as multisets</em>. It is decision-only — it
builds no witness — and it is sound in the precise sense that it never returns
true when the visible answers genuinely differ: a missing, extra, duplicated,
or structurally changed answer is always caught
({src("crates/stella-core/src/faithfulness.rs", 104, "faithfulness.rs:104–119")}).</p>

<p>When a fast tier's answer is not accepted, that run falls back to the
reference resolver — the deopt. The internal map to the GraalVM/Truffle model
is recorded as: reference <code>iex</code> is "the interpreter is the spec",
the fast tiers are the optimizing tier, and verified-jet + differential oracle
+ deopt is Graal-style speculation <em>plus</em> a validation step — a
verified speculative runtime
({src("docs/07-engine-subproject-open-threads.md", 387, "docs/07 §H")}).</p>

<h2>4 · The galaxy reducer is a Krivine machine, as a constellation</h2>

<p>The applied workload is the ICFP-2020 <code>galaxy.txt</code>: 392 named
definitions in a binder-free combinator language
({src("crates/stella-core/src/galaxy.rs", 1, "galaxy.rs:1–12")}). It runs not
on a separate evaluator but as resolution. Eng's exegesis (§57.19) gives the
Krivine Abstract Machine as a constellation; this engine uses that directly. A
process is the single ray <code>+P(st(M, π))</code> — a focused term
<code>M</code> over a stack <code>π</code>
({src("crates/stella-core/src/galaxy.rs", 917, "initial_psi")}). Two rules do
most of the work:</p>

<ul>
<li><strong>Push</strong> — <code>a(M,N)⋆π ↝ M⋆(N·π)</code>, uncurrying an
application onto the stack
({src("crates/stella-core/src/galaxy.rs", 422, "galaxy.rs:422–423")}).</li>
<li><strong>δ</strong> — each named definition becomes one star
<code>[ −P(st(:N,π)), +P(st(body•,π)) ]</code>, rewriting the name to its
encoded body ({src("crates/stella-core/src/galaxy.rs", 398, "delta_star")}).</li>
</ul>

<p>Laziness and strictness sit on top. {src("crates/stella-core/src/galaxy.rs", 925, "eval_forced")}
drives the process, preserving the KAM stack across resumes. When a strict
primitive (<code>add</code>, <code>eq</code>, <code>isnil</code>, …) needs an
operand evaluated, {src("crates/stella-core/src/galaxy.rs", 753, "drive_strict")}
calls {src("crates/stella-core/src/galaxy.rs", 685, "force_value")}, which
recursively reduces that operand to weak head normal form and reads it back.
Closed sub-results are memoised
({src("crates/stella-core/src/galaxy.rs", 698, "galaxy.rs:698–703")}); a
budget-exhausted result is deliberately <em>not</em> cached as if final, so a
measured stop is never mistaken for a term's true normal form
({src("crates/stella-core/src/galaxy.rs", 734, "galaxy.rs:734–741")}).
<code>drive_strict</code> is the only place new strict work is minted — which
is exactly why Σ(Φ) refuses to specialise across it.</p>

<p>The illustrative <a href="visualize.html">visualizer</a> animates a Push and
a δ step by hand; the <a href="../explore.html">explorer</a> runs the real
engine in WebAssembly. The <a href="measure.html">measurement page</a> is the
honest, still-open question of what this reducer actually does on one galaxy
image.</p>
"""


VISUALIZE = """
<p>This page animates two things from the <a href="internals.html">engine
page</a>, one step at a time: a single stellar-resolution
<strong>fusion</strong> (ray matching, the most general unifier, the
substitution), and a single KAM <strong>Push / δ</strong> reduction. Use the
buttons, or focus the panel and press <kbd>←</kbd> / <kbd>→</kbd>.</p>

<p class="viz-note">This is an illustration, not the engine. It plays a fixed,
hand-authored script — it does not parse, unify, or resolve anything. The steps
it shows are the steps <code>stella-core</code> actually takes on these exact
inputs (the same conclusions the live WebAssembly build on
<a href="../explore.html">/explore</a> reaches), drawn here with plain
JavaScript and no dependencies so a static archive keeps the whole thing. For a
worked example produced by the real engine at build time, see the
<a href="primer.html">first reading</a>; to drive the engine yourself, open the
<a href="../explore.html">explorer</a>.</p>

<h2>One fusion step</h2>
<p>The reference constellation Φ defines addition on unary naturals; the query
asks for 1 + 1. Watch a positive and a negative <code>add</code> ray of
opposite polarity match, the most general unifier appear, the two stars fuse,
and the substitution propagate — repeating until no matchable pair remains and
the neutral ray left behind is the answer.</p>

<div id="viz-fusion" aria-label="Stellar-resolution fusion, step by step"></div>

<h2>One KAM Push / δ step</h2>
<p>The galaxy reducer is a Krivine machine written as a constellation: a
process is the single ray <code>+P(st(M, π))</code>. Here a small definition
<code>:double X = add X X</code> is applied to <code>2</code>. Watch the Push
rule uncurry the application onto the stack, the δ-star unfold the definition
to its closed body, and the strict primitive fire.</p>

<div id="viz-kam" aria-label="KAM Push and delta reduction, step by step"></div>

<p>The mechanics here are described, with source citations, on the
<a href="internals.html">engine page</a> (§2 and §4). Nothing on this page is
load-bearing for any claim; it is a picture of the rules.</p>

<script type="module" src="../assets/visualize.js"></script>
"""


MEASURE = """
<p>This project has one cardinal rule for engine work:
<strong>measure, don't guess</strong>. This page is the story of that rule
doing its job — including, and especially, the part where a conclusion was
reached, written down, and then retracted because the next measurement
contradicted it. That retraction is not an embarrassment to tuck away; it is
the method working. The question this page describes is
<strong>still open</strong>.</p>

<h2>The blocker</h2>
<p>The applied workload is the ICFP-2020 galaxy program. Most of it runs
end-to-end. One thing does not: forcing a single image element,
<code>data[0]</code>, did not terminate within a generous budget. The
question — what, exactly, is expensive about <code>data[0]</code> — drove a
sequence of research surveys and a decision record
(<a href="https://github.com/emberian/stella/blob/dev/docs/16-galaxy-execution-decision.md">docs/16</a>).</p>

<h2>The decision: build a discriminator, not a guess</h2>
<p>Four independent analyses converged on a single diagnosis:
<code>data[0]</code> was a long, non-redundant, transition-count-bound
reduction, so only a step-count collapse (recurrence acceleration, or
interaction nets) could make it finite — every per-step lever, including the
2× unifier and Σ(Φ), is bounded and cannot cross a termination boundary
(<a href="https://github.com/emberian/stella/blob/dev/docs/16-galaxy-execution-decision.md#L18">docs/16 §1</a>).
Crucially, the decision record did <em>not</em> then start building the
expensive termination-crosser. It identified two competing falsifiable
hypotheses for <em>why</em> the reduction was long and called for a cheap,
read-only, bounded measurement to choose between them with data — because the
cause "is an empirical fact about <code>data[0]</code>'s real trace, to be
measured, not guessed"
(<a href="https://github.com/emberian/stella/blob/dev/docs/16-galaxy-execution-decision.md#L33">docs/16 §2–3</a>).</p>

<h2>What the measurement found — and the over-conclusion</h2>
<p>The discriminator was built and run. It found that forcing
<code>data[0]</code> reaches an <code>isnil</code> applied to an unforced
application thunk and then the outer loop spins non-productively: steps grew
with the <em>budget</em> while the count of actual forcings stayed at one. The
reasonable-looking reading was written into the open-threads log: the blocker
is not a step-count asymptotic at all, it is a constructor-strictness gap, and
the load-bearing premise of the decision record is
<strong>falsified by measurement</strong>
(<a href="https://github.com/emberian/stella/blob/dev/docs/07-engine-subproject-open-threads.md#L607">docs/07, "DISCRIMINATOR RESULT"</a>).</p>

<p>That conclusion was wrong, and the next pass caught it.</p>

<h2>The retraction</h2>
<p>On a call to measure deeper before acting, reading
<a href="https://github.com/emberian/stella/blob/dev/crates/stella-core/src/galaxy.rs#L753"><code>drive_strict</code></a>
refuted the previous conclusion: constructor-strict <code>isnil</code> is in
fact already fully implemented and faithful — it calls
<a href="https://github.com/emberian/stella/blob/dev/crates/stella-core/src/galaxy.rs#L685"><code>force_value</code></a>
on its argument and maps the forced constructor. The "spin" the discriminator
saw was a recursion-budget exhaustion deep inside a nested <code>force_value</code>
call — invisible to a probe that only read the <em>outer</em> result ray, not
an absent rule. So the earlier "premise falsified" claim was itself
<strong>premature and retracted</strong>
(<a href="https://github.com/emberian/stella/blob/dev/docs/07-engine-subproject-open-threads.md#L657">docs/07, "CORRECTION"</a>).</p>

<p>What is genuinely measured and true is narrower than either earlier
statement: the outer reduction is short (about 200 lazy steps to the first
<code>isnil</code>); the real cost lives in the nested <code>force_value</code>
recursion, which the discriminator never observed. The decision record's
central question is therefore <strong>re-opened, not closed</strong>: does the
nested recursion for <code>data[0]</code> terminate-but-deep, or is it
genuinely unbounded? The honest answer right now is: <em>not yet
known</em> — it is to be settled by a deeper, layer-resolved trace, and the
decision record is left unrevised until that measurement lands.</p>

<h2>Why this is the story</h2>
<p>The log entry is explicit that the correction "IS the
measure-don't-guess discipline working: a wrong conclusion caught by the next
measurement before it drove a build"
(<a href="https://github.com/emberian/stella/blob/dev/docs/07-engine-subproject-open-threads.md#L684">docs/07</a>).
A guess, confidently written, would have sent weeks of work at the wrong
problem twice over — first the termination-crosser, then the strictness
"fix". Two cheap measurements stopped both. The discipline does not promise
the first measurement is right. It promises the next one gets to overrule it,
and that the overruling is recorded in the open as part of the result rather
than quietly papered over.</p>

<p>The honest current state, in one line: the cost of <code>data[0]</code> is
located in nested forced evaluation; whether it terminates is an open empirical
question; the per-step accelerators (<a href="internals.html">the unifier and
Σ(Φ)</a>) are real wins that were never claimed to settle it.</p>
"""


ENGINE_BODIES = {
    "internals": dict(
        body=INTERNALS,
        eyebrow="The engine",
        title="How the engine is built",
        lede="Four techniques in stella-core — the near-linear unifier, the "
             "Σ(Φ) Futamura projection, verified speculation, and the KAM "
             "reducer — each claim anchored to its source line.",
        desc="The implementation techniques behind the stellar-resolution "
             "engine, with file:line citations: unify_fast, Σ(Φ), the "
             "two-tier verified-speculative model, and the galaxy KAM.",
        mins=12,
        prov="<strong>About the implementation.</strong> Every technical "
             "claim links to the exact source line it rests on; the prose is "
             "a guide to the code, not a substitute for it.",
        script=False,
    ),
    "visualize": dict(
        body=VISUALIZE,
        eyebrow="Illustration",
        title="Watch a step, by hand",
        lede="A dependency-free animation of one fusion step and one KAM "
             "Push / δ step — illustrative, hand-fed, not the live engine.",
        desc="An illustrative, dependency-free visualizer: one "
             "stellar-resolution fusion step and one KAM Push/δ reduction, "
             "animated step by step. Not the engine — see /explore for that.",
        mins=4,
        prov="<strong>Illustrative.</strong> A hand-authored animation, not "
             "the engine. For the real engine see the "
             "<a href=\"../explore.html\">explorer</a>; for an engine-produced "
             "worked example see the <a href=\"primer.html\">first reading</a>.",
        script=True,
    ),
    "measure": dict(
        body=MEASURE,
        eyebrow="Research narrative",
        title="Measure, don't guess",
        lede="The still-open galaxy-execution question — and the conclusion "
             "that was reached, written down, and then retracted because the "
             "next measurement overruled it. The retraction is the method.",
        desc="An honest, ongoing research narrative: the data[0] blocker, "
             "the measure-don't-guess decision, and the over-conclusion that "
             "was caught and retracted. The question is still open.",
        mins=7,
        prov="<strong>Field report — open and ongoing.</strong> This "
             "describes a question that is not resolved. The retracted "
             "conclusion is kept in view on purpose.",
        script=False,
    ),
}


def build_engine() -> int:
    n = 0
    for d in ENGINE:
        slug = d["slug"]
        meta = ENGINE_BODIES[slug]
        out = PAGE.format(
            prefix="../",
            robots="",
            title=html.escape(meta["title"]),
            desc=html.escape(meta["desc"]),
            nav=nav("engine", "../"),
            toc=toc(ENGINE, slug, "The engine · stella-core", "grove",
                    "index.html", "The model", "../"),
            eyebrow=html.escape(meta["eyebrow"]),
            lede=html.escape(meta["lede"]),
            section="The engine",
            mins=meta["mins"],
            src_url="https://github.com/emberian/stella/blob/dev/site/build.py",
            prov_cls="",
            prov_html=meta["prov"],
            body=meta["body"],
            footer=pager("engine", slug),
        )
        (OUT / f"{slug}.html").write_text(out, encoding="utf-8")
        n += 1
        print(f"  baked r/{slug}.html  ← engine page")
    return n


def write_sitemap(slugs: list[str]) -> None:
    base = "https://emberian.github.io/stella/"
    urls = [base, base + "explore.html"]
    urls += [f"{base}r/{s}.html" for s in slugs]
    body = "".join(f"<url><loc>{u}</loc></url>" for u in urls)
    (SITE / "sitemap.xml").write_text(
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'
        f"{body}</urlset>\n",
        encoding="utf-8",
    )
    (SITE / "robots.txt").write_text(
        "User-agent: *\nAllow: /\nDisallow: /cmi/\n"
        f"Sitemap: {base}sitemap.xml\n",
        encoding="utf-8",
    )


def check_links(slugs: set[str]) -> None:
    """Warn on dangling internal r/ links and any TeX fallback."""
    href_re = re.compile(r'href="([^":/?#]+\.html)(?:[#?][^"]*)?"')
    problems = 0
    for f in sorted(OUT.glob("*.html")):
        txt = f.read_text(encoding="utf-8")
        if "tex-fallback" in txt:
            print(f"  ! {f.name}: TeX fallback present (math failed to convert)")
            problems += 1
        for href in href_re.findall(txt):
            base = href.removesuffix(".html")
            if base not in slugs:
                print(f"  ! {f.name}: dangling link → {href}")
                problems += 1
    print(f"  link/render check: {problems} problem(s)")


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    n = 0
    for coll_name, coll in (("stellar", STELLAR), ("cmi", CMI)):
        for d in coll:
            if not (ROOT / d["src"]).exists():
                print(f"  skip {d['slug']}: {d['src']} not in tree")
                continue
            (OUT / f"{d['slug']}.html").write_text(
                render_doc(d, coll, coll_name), encoding="utf-8"
            )
            n += 1
            print(f"  baked r/{d['slug']}.html  ← {d['src']}")

    build_notation()
    n += 1
    n += build_engine()
    presets = engine_steps()
    if presets and build_primer(presets):
        n += 1

    # Public (advertised) slugs vs. all built slugs. CMI is built and
    # deployed (shareable by direct link) but kept out of the sitemap and
    # unlinked from the public site — discoverable only if you have the URL.
    public = (
        ["notation"]
        + (["primer"] if (OUT / "primer.html").exists() else [])
        + [d["slug"] for d in ENGINE if (OUT / f"{d['slug']}.html").exists()]
        + [d["slug"] for d in STELLAR if (OUT / f"{d['slug']}.html").exists()]
    )
    all_slugs = public + [
        d["slug"] for d in CMI if (OUT / f"{d['slug']}.html").exists()
    ]
    write_sitemap(public)
    check_links(set(all_slugs))
    print(f"{n} reading pages prebaked → site/r/")


if __name__ == "__main__":
    main()
