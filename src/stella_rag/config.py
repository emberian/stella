"""Central config: paths and model IDs. Override via env vars (STELLA_*)."""
from __future__ import annotations

import os
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
REFS_DIR = REPO_ROOT / "refs"
ORIGINALS_DIR = REFS_DIR / "originals"
EXTRACTED_DIR = REFS_DIR / "extracted"
INDEX_DIR = REPO_ROOT / "index"
QDRANT_PATH = INDEX_DIR / "qdrant"  # embedded persistent mode, no server/docker

COLLECTION = os.environ.get("STELLA_COLLECTION", "stella_refs")

# Dense embeddings: Microsoft Harrier-OSS-v1 27B (MIT, decoder-only, last-token
# pool + L2 norm). Queries take a one-sentence instruction; documents do not.
DENSE_MODEL = os.environ.get("STELLA_DENSE_MODEL", "microsoft/harrier-oss-v1-27b")
DENSE_QUERY_INSTRUCTION = os.environ.get(
    "STELLA_DENSE_INSTRUCTION",
    "Retrieve passages from technical papers on logic, proof theory, and "
    "consciousness that answer the query",
)

# Sparse (lexical) side: BM25 via fastembed. Critical for exact-symbol queries
# (linear-logic notation, author names, defined terms) that dense vectors miss.
SPARSE_MODEL = os.environ.get("STELLA_SPARSE_MODEL", "Qdrant/bm25")

# Reranker: Qwen3-Reranker-8B (SOTA open-weight cross-encoder).
RERANK_MODEL = os.environ.get("STELLA_RERANK_MODEL", "Qwen/Qwen3-Reranker-8B")

# Torch device/dtype. MPS on Apple Silicon; bfloat16 keeps the 27B within
# unified-memory budget alongside the reranker.
DEVICE = os.environ.get("STELLA_DEVICE", "mps")
DTYPE = os.environ.get("STELLA_DTYPE", "bfloat16")

# Chunking: heading-aware first, then a token budget so no chunk overflows the
# embedder while keeping section context intact.
CHUNK_TARGET_TOKENS = int(os.environ.get("STELLA_CHUNK_TOKENS", "512"))
CHUNK_OVERLAP_TOKENS = int(os.environ.get("STELLA_CHUNK_OVERLAP", "64"))

# Retrieval defaults.
DENSE_TOPK = int(os.environ.get("STELLA_DENSE_TOPK", "30"))
SPARSE_TOPK = int(os.environ.get("STELLA_SPARSE_TOPK", "30"))
RERANK_KEEP = int(os.environ.get("STELLA_RERANK_KEEP", "8"))


def slug(pdf_path: Path) -> str:
    """Stable per-paper slug used for refs/extracted/<slug>/ and chunk ids."""
    return pdf_path.stem
