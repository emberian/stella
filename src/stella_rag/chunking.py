"""Heading-aware, token-budgeted chunking over marker's flat blocks.

Chunks never span a section boundary (keeps citations meaningful) and never
exceed the token budget (keeps the embedder happy). Token count is a cheap
chars/4 estimate so corpus build needs no model/tokenizer download.
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Iterable

# Running headers/footers are noise for retrieval.
SKIP_BLOCK_TYPES = {"PageHeader", "PageFooter"}


@dataclass
class Block:
    page: int
    section: str
    text: str
    block_type: str


@dataclass
class Chunk:
    id: str
    paper: str
    source_pdf: str
    page_start: int
    page_end: int
    section: str
    text: str
    sha256: str = field(default="")

    def finalize(self) -> "Chunk":
        self.sha256 = hashlib.sha256(self.text.encode("utf-8")).hexdigest()
        return self


def est_tokens(text: str) -> int:
    return max(1, len(text) // 4)


def chunk_blocks(
    blocks: Iterable[Block],
    paper: str,
    source_pdf: str,
    target_tokens: int,
    overlap_tokens: int,
) -> list[Chunk]:
    chunks: list[Chunk] = []
    buf: list[Block] = []
    buf_tokens = 0
    idx = 0

    def flush(carry_overlap: bool) -> list[Block]:
        nonlocal idx, buf_tokens
        if not buf:
            return []
        text = "\n\n".join(b.text for b in buf).strip()
        if text:
            c = Chunk(
                id=f"{paper}:p{buf[0].page:04d}:c{idx:02d}",
                paper=paper,
                source_pdf=source_pdf,
                page_start=buf[0].page,
                page_end=buf[-1].page,
                section=buf[0].section,
                text=text,
            ).finalize()
            chunks.append(c)
            idx += 1
        if not carry_overlap:
            return []
        # Carry trailing blocks up to the overlap budget into the next chunk.
        carried: list[Block] = []
        acc = 0
        for b in reversed(buf):
            t = est_tokens(b.text)
            if acc + t > overlap_tokens:
                break
            carried.insert(0, b)
            acc += t
        return carried

    cur_section: str | None = None
    for b in blocks:
        if b.block_type in SKIP_BLOCK_TYPES or not b.text.strip():
            continue
        if cur_section is None:
            cur_section = b.section
        section_changed = b.section != cur_section
        bt = est_tokens(b.text)
        if buf and (section_changed or buf_tokens + bt > target_tokens):
            carried = flush(carry_overlap=not section_changed)
            buf = list(carried)
            buf_tokens = sum(est_tokens(x.text) for x in buf)
            cur_section = b.section
        buf.append(b)
        buf_tokens += bt

    flush(carry_overlap=False)
    return chunks
