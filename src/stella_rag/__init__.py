"""Local hybrid RAG over the stella reference corpus.

Pipeline: marker (PDF -> markdown + structured blocks) -> heading/token chunks
-> Qdrant embedded index (Harrier-OSS-v1-27b dense + BM25 sparse) -> hybrid
retrieve -> Qwen3-Reranker-8B -> cited answers.

Canonical source of truth = refs/originals/*.pdf + these scripts. Everything
under refs/extracted/ and index/ is a rebuildable cache.
"""
