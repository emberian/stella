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
import pathlib
import re

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
        + link("cmi/index.html", "Implementation", "cmi")
        + "</div></nav>"
    )


def toc(collection: list[dict], active_slug: str, label: str, glyph: str,
        home_href: str, home_label: str, prefix: str) -> str:
    items = [
        f'<a class="fj-toc__home" href="{prefix}{home_href}">'
        f'<span class="mark"><img src="{prefix}assets/stella/glyphs/{glyph}.svg" alt="" /></span>'
        f"{home_label}</a>",
        f'<div class="fj-toc__section">'
        f'<img src="{prefix}assets/stella/glyphs/{glyph}.svg" alt="" /> {label}</div>',
    ]
    for i, d in enumerate(collection):
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
    body = make_md().render(body_md)
    prov_cls, prov_html = PROVENANCE[d["kind"]]

    if coll_name == "stellar":
        the_nav = nav("exegesis" if d["slug"].startswith("eng") else "home", "../")
        the_toc = toc(collection, d["slug"], "The exegesis · after Boris Eng",
                      "leaf", "index.html", "The model", "../")
        section = "The exegesis"
    else:
        the_nav = nav("cmi", "../")
        the_toc = toc(collection, d["slug"], "The implementation project",
                      "mushroom", "cmi/index.html", "Implementation", "../")
        section = "Implementation project"

    return PAGE.format(
        prefix="../",
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
    )


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
    print(f"{n} reading pages prebaked → site/r/")


if __name__ == "__main__":
    main()
