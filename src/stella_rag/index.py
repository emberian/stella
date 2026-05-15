"""Build the embedded Qdrant hybrid index from chunks.jsonl.

Dense = Harrier-OSS-v1-27b, sparse = BM25 (fastembed). Qdrant runs in embedded
persistent mode at index/qdrant/ — no server, no Docker. This collection is a
rebuildable cache; the canonical source is refs/extracted/*/chunks.jsonl.
"""
from __future__ import annotations

import json
import uuid
from pathlib import Path

from rich.console import Console

from . import config
from .embed import DenseEmbedder

console = Console()
_NS = uuid.UUID("00000000-0000-0000-0000-0000573e11a0")  # stable id namespace


def _load_chunks() -> list[dict]:
    rows: list[dict] = []
    for jsonl in sorted(config.EXTRACTED_DIR.glob("*/chunks.jsonl")):
        for line in jsonl.read_text(encoding="utf-8").splitlines():
            if line.strip():
                rows.append(json.loads(line))
    return rows


def build_index() -> int:
    from fastembed import SparseTextEmbedding
    from qdrant_client import QdrantClient, models

    chunks = _load_chunks()
    if not chunks:
        raise SystemExit(
            f"No chunks under {config.EXTRACTED_DIR} — run `stella ingest` first."
        )
    console.print(f"[bold]Indexing[/] {len(chunks)} chunks")

    dense = DenseEmbedder()
    dim = dense.dim
    sparse_model = SparseTextEmbedding(config.SPARSE_MODEL)

    config.QDRANT_PATH.mkdir(parents=True, exist_ok=True)
    client = QdrantClient(path=str(config.QDRANT_PATH))

    client.delete_collection(config.COLLECTION)  # full rebuild, deterministic
    client.create_collection(
        config.COLLECTION,
        vectors_config={
            "dense": models.VectorParams(size=dim, distance=models.Distance.COSINE)
        },
        sparse_vectors_config={
            "bm25": models.SparseVectorParams(modifier=models.Modifier.IDF)
        },
    )

    texts = [c["text"] for c in chunks]
    dense_vecs = dense.embed_documents(texts)
    sparse_vecs = list(sparse_model.embed(texts))

    points = []
    for c, dv, sv in zip(chunks, dense_vecs, sparse_vecs):
        points.append(
            models.PointStruct(
                id=str(uuid.uuid5(_NS, c["id"])),
                vector={
                    "dense": dv,
                    "bm25": models.SparseVector(
                        indices=sv.indices.tolist(), values=sv.values.tolist()
                    ),
                },
                payload=c,
            )
        )
    client.upsert(config.COLLECTION, points=points)
    console.print(f"[green]Indexed[/] {len(points)} points into '{config.COLLECTION}'")
    return len(points)
