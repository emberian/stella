"""PDF -> doc.md + meta.json + chunks.jsonl via a single marker model pass.

Output per paper: refs/extracted/<slug>/{doc.md, meta.json, chunks.jsonl, images/}
The marker model pass is the expensive step, so we build the Document once and
run both the markdown and chunk renderers over it.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from rich.console import Console

from . import config
from .chunking import Block, chunk_blocks

console = Console()


def _sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def _build_converter():
    from marker.converters.pdf import PdfConverter
    from marker.models import create_model_dict

    artifacts = create_model_dict(device=config.DEVICE, dtype=config.DTYPE)
    return PdfConverter(artifact_dict=artifacts)


def ingest_one(pdf: Path, converter, md_renderer, chunk_renderer) -> dict:
    pdf = pdf.resolve()
    slug = config.slug(pdf)
    out_dir = config.EXTRACTED_DIR / slug
    img_dir = out_dir / "images"
    out_dir.mkdir(parents=True, exist_ok=True)
    img_dir.mkdir(exist_ok=True)

    document = converter.build_document(str(pdf))  # single expensive pass
    md_out = md_renderer(document)
    chunk_out = chunk_renderer(document)

    (out_dir / "doc.md").write_text(md_out.markdown, encoding="utf-8")
    for name, img in (md_out.images or {}).items():
        img.save(img_dir / name)

    md_cls = md_renderer.md_cls  # html -> markdown, preserves LaTeX

    # marker's section_hierarchy maps heading-level -> SectionHeader block id,
    # not -> title text. Build an id -> heading-text map from the headers
    # themselves (they appear in reading order before the blocks citing them).
    from bs4 import BeautifulSoup

    def plain(html: str) -> str:
        return BeautifulSoup(html, "html.parser").get_text(" ", strip=True)

    header_text = {
        fb.id: plain(fb.html)
        for fb in chunk_out.blocks
        if fb.block_type == "SectionHeader"
    }

    def resolve_section(hierarchy: dict[int, str] | None) -> str:
        if not hierarchy:
            return ""
        parts = [header_text.get(hierarchy[k], "") for k in sorted(hierarchy)]
        return " > ".join(p for p in parts if p)

    blocks: list[Block] = []
    for fb in chunk_out.blocks:
        text = md_cls.convert(fb.html).strip()
        blocks.append(
            Block(
                page=fb.page,  # marker's printed page label — citation-friendly
                section=resolve_section(fb.section_hierarchy),
                text=text,
                block_type=fb.block_type,
            )
        )

    chunks = chunk_blocks(
        blocks,
        paper=slug,
        source_pdf=str(pdf.relative_to(config.REPO_ROOT)),
        target_tokens=config.CHUNK_TARGET_TOKENS,
        overlap_tokens=config.CHUNK_OVERLAP_TOKENS,
    )

    with (out_dir / "chunks.jsonl").open("w", encoding="utf-8") as f:
        for c in chunks:
            f.write(json.dumps(c.__dict__, ensure_ascii=False) + "\n")

    toc = [
        {"title": e.get("title"), "page": e.get("page_id")}
        for e in (md_out.metadata or {}).get("table_of_contents", [])
    ]
    meta = {
        "paper": slug,
        "source_pdf": str(pdf.relative_to(config.REPO_ROOT)),
        "pdf_sha256": _sha256_file(pdf),
        "n_pages": len(chunk_out.page_info),
        "n_chunks": len(chunks),
        "table_of_contents": toc,
    }
    (out_dir / "meta.json").write_text(
        json.dumps(meta, indent=2, ensure_ascii=False, default=str), encoding="utf-8"
    )
    return meta


def ingest_all(pdfs: list[Path] | None = None) -> list[dict]:
    from marker.renderers.chunk import ChunkRenderer
    from marker.renderers.markdown import MarkdownRenderer

    if pdfs is None:
        pdfs = sorted(config.ORIGINALS_DIR.glob("*.pdf"))
    if not pdfs:
        raise SystemExit(f"No PDFs in {config.ORIGINALS_DIR}")

    console.print(f"[bold]Loading marker models[/] (device={config.DEVICE} dtype={config.DTYPE})…")
    converter = _build_converter()
    md_renderer = MarkdownRenderer()
    chunk_renderer = ChunkRenderer()

    metas = []
    for pdf in pdfs:
        console.print(f"[cyan]Extracting[/] {pdf.name}")
        m = ingest_one(pdf, converter, md_renderer, chunk_renderer)
        console.print(f"  → {m['n_pages']} pages, {m['n_chunks']} chunks")
        metas.append(m)
    return metas
