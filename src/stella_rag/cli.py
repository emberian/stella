"""`stella` CLI: ingest -> index -> ask. All steps rebuildable from the repo."""
from __future__ import annotations

import typer
from rich.console import Console
from rich.panel import Panel

app = typer.Typer(add_completion=False, help="Local hybrid RAG over refs/")
console = Console()


@app.command()
def ingest(
    pdfs: list[str] = typer.Argument(
        None, help="specific PDFs to (re)ingest; default = all of refs/originals/"
    ),
):
    """Extract PDFs -> refs/extracted/<slug>/ (marker). Incremental: naming
    specific PDFs only re-runs those, leaving other papers' output intact."""
    from pathlib import Path

    from .ingest import ingest_all

    ingest_all([Path(p) for p in pdfs] if pdfs else None)


@app.command()
def index():
    """Build the Qdrant hybrid index from refs/extracted/*/chunks.jsonl."""
    from .index import build_index

    build_index()


@app.command()
def ask(
    query: str,
    keep: int = typer.Option(8, help="passages to return after rerank"),
):
    """Hybrid-retrieve + rerank; print cited passages (evidence, not generation)."""
    from .query import Retriever

    hits = Retriever().retrieve(query, keep=keep)
    if not hits:
        console.print("[red]No results — is the index built?[/]")
        raise typer.Exit(1)
    from rich.markup import escape

    for i, h in enumerate(hits, 1):
        console.print(
            Panel(
                escape(h.text),
                title=escape(f"{i}. {h.citation}"),
                subtitle=f"rerank={h.score:.3f}",
                title_align="left",
            )
        )


if __name__ == "__main__":
    app()
