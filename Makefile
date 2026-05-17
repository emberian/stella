# stella RAG — reproducible from a clean checkout. No manual laptop setup.
.PHONY: setup fetch-models ingest index rebuild ask clean-cache clean-index \
        site site-wasm site-content site-serve clean-site

# 1. Project-local, locked Python env (does NOT use ~/.venv).
setup:
	uv sync

# 2. Pre-download the models into the HF cache. Resumable.
fetch-models:
	uv run python -c "from huggingface_hub import snapshot_download as d; \
	d('microsoft/harrier-oss-v1-0.6b'); d('Qwen/Qwen3-Reranker-8B')"

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

# ── The literate site (emberian.github.io/stella) ────────────────────────────
# `make site` prebakes a fully static, self-contained build under site/.
# Hand-authored HTML/CSS/JS is committed; r/ (prebaked pages) and pkg/ (WASM)
# are generated. The reading pages contain no runtime fetch or scripting — a
# web-archive snapshot of any page is the whole page.

# Render the repository markdown → static HTML + MathML (no client JS).
site-build:
	uv run --script site/build.py

# Compile stella-core to wasm32 and stage the bundle the explorer imports.
# (The explorer is an optional tool; the reading does not depend on it.)
site-wasm:
	cd crates/stella-viz && ./build-wasm.sh
	mkdir -p site/pkg
	cp crates/stella-viz/web/pkg/stella_viz_wasm.js \
	   crates/stella-viz/web/pkg/stella_viz_wasm_bg.wasm site/pkg/

site: site-build site-wasm
	@echo "site/ prebaked — serve it with: make site-serve"

# Local preview. The pages are static; http is only needed for the WASM module.
site-serve: site
	cd site && python3 -m http.server 8080

clean-site:
	rm -rf site/r site/pkg site/content
