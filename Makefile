# stella RAG — reproducible from a clean checkout. No manual laptop setup.
.PHONY: setup fetch-models ingest index rebuild ask clean-cache clean-index

# 1. Project-local, locked Python env (does NOT use ~/.venv).
setup:
	uv sync

# 2. Pre-download the (large) models into the HF cache. Resumable.
fetch-models:
	uv run python -c "from huggingface_hub import snapshot_download as d; \
	d('microsoft/harrier-oss-v1-27b'); d('Qwen/Qwen3-Reranker-8B')"

# 3. PDFs -> markdown + chunks (marker single model pass per paper).
ingest:
	uv run stella ingest

# 4. chunks.jsonl -> embedded Qdrant hybrid index (dense + BM25).
index:
	uv run stella index

rebuild: ingest index

# Ad-hoc query: make ask Q="what does Painful Intelligence argue about suffering?"
ask:
	uv run stella ask "$(Q)"

clean-cache:
	rm -rf refs/extracted

clean-index:
	rm -rf index
