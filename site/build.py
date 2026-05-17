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
    dict(slug="run1",       src="docs/02-phase4-first-run.md",                      eyebrow="Phase 4 · result",    title="The first make-or-break run",             lede="The honest result. It broke; the break is recorded as a finding.", kind="report"),
    dict(slug="run-reform", src="docs/03-phase4-reformulated-run.md",               eyebrow="Phase 4 · draft",     title="The reformulated make-or-break run",      lede="An unadjudicated draft, kept for the record.", kind="report"),
    dict(slug="phase5",     src="docs/04-phase5-embodied-valence-and-the-temporal-gap.md", eyebrow="Phase 5",      title="Embodied valence, orders of self, the Temporal Gap", lede="Where the substrate makes a wager about time formally distinguishable.", kind="report"),
    dict(slug="history",    src="HISTORY.md",                                      eyebrow="Bringup · first person", title="The bringup, from the inside",        lede="A candid, first-person account of the run. A record, not a polished account.", kind="inside"),
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
        + link("explore.html", "Explore", "explore")
        + link("r/primer.html", "A first reading", "primer")
        + "</div></nav>"
    )


# The stellar TOC opens with two generated pages (not digests).
STELLAR_TOP = [
    {"slug": "primer", "title": "A first reading"},
    {"slug": "notation", "title": "Notation & glossary"},
]


def order_for(coll_name: str) -> list[dict]:
    """Linear reading order, for prev/next."""
    if coll_name == "stellar":
        return STELLAR_TOP + STELLAR
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
    presets = engine_steps()
    if presets and build_primer(presets):
        n += 1

    # Public (advertised) slugs vs. all built slugs. CMI is built and
    # deployed (shareable by direct link) but kept out of the sitemap and
    # unlinked from the public site — discoverable only if you have the URL.
    public = (
        ["notation"]
        + (["primer"] if (OUT / "primer.html").exists() else [])
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
