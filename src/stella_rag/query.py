"""Hybrid retrieve (dense + BM25, RRF-fused) then Qwen3-Reranker-8B.

RRF is done in-process from two independent searches rather than relying on
Qdrant local-mode fusion parity — transparent and stable across versions.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property

from . import config
from .embed import DenseEmbedder

RRF_K = 60


@dataclass
class Hit:
    chunk_id: str
    paper: str
    source_pdf: str
    page_start: int
    page_end: int
    section: str
    text: str
    score: float

    @property
    def citation(self) -> str:
        # marker's printed page labels aren't monotonic in book-form PDFs, so
        # first/last block pages can invert — display the true min..max span.
        lo, hi = sorted((self.page_start, self.page_end))
        pages = f"p.{lo}" if lo == hi else f"pp.{lo}-{hi}"
        sec = f" §{self.section}" if self.section else ""
        return f"[{self.paper} {pages}{sec}]"


class Retriever:
    def __init__(self):
        self.dense = DenseEmbedder()

    @cached_property
    def _client(self):
        from qdrant_client import QdrantClient

        return QdrantClient(path=str(config.QDRANT_PATH))

    @cached_property
    def _sparse(self):
        from fastembed import SparseTextEmbedding

        return SparseTextEmbedding(config.SPARSE_MODEL)

    @cached_property
    def _reranker(self):
        from sentence_transformers import CrossEncoder

        return CrossEncoder(
            config.RERANK_MODEL,
            device=config.DEVICE,
            model_kwargs={"torch_dtype": config.DTYPE},
        )

    def _search(self, query: str) -> dict[str, dict]:
        from qdrant_client import models

        fused: dict[str, dict] = {}

        dv = self.dense.embed_query(query)
        dense_res = self._client.query_points(
            config.COLLECTION, query=dv, using="dense",
            limit=config.DENSE_TOPK, with_payload=True,
        ).points

        sv = next(iter(self._sparse.embed([query])))
        sparse_res = self._client.query_points(
            config.COLLECTION,
            query=models.SparseVector(
                indices=sv.indices.tolist(), values=sv.values.tolist()
            ),
            using="bm25", limit=config.SPARSE_TOPK, with_payload=True,
        ).points

        for res in (dense_res, sparse_res):
            for rank, pt in enumerate(res, start=1):
                entry = fused.setdefault(
                    pt.id, {"payload": pt.payload, "score": 0.0}
                )
                entry["score"] += 1.0 / (RRF_K + rank)
        return fused

    def retrieve(self, query: str, keep: int | None = None) -> list[Hit]:
        keep = keep or config.RERANK_KEEP
        fused = self._search(query)
        if not fused:
            return []
        candidates = sorted(
            fused.values(), key=lambda e: e["score"], reverse=True
        )[: max(keep * 4, keep)]

        payloads = [c["payload"] for c in candidates]
        ranked = self._reranker.rank(
            query, [p["text"] for p in payloads], top_k=keep
        )
        hits: list[Hit] = []
        for r in ranked:
            p = payloads[r["corpus_id"]]
            hits.append(
                Hit(
                    chunk_id=p["id"],
                    paper=p["paper"],
                    source_pdf=p["source_pdf"],
                    page_start=p["page_start"],
                    page_end=p["page_end"],
                    section=p["section"],
                    text=p["text"],
                    score=float(r["score"]),
                )
            )
        return hits
