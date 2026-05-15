"""Dense embeddings via Microsoft Harrier-OSS-v1-27b.

Loaded directly through transformers (AutoModel + AutoTokenizer), NOT
sentence-transformers: ST 5.5 unconditionally calls AutoProcessor, and for the
gemma3 family that resolves a multimodal processor demanding image config the
text-only Harrier repo doesn't ship. We implement the model card's documented
recipe ourselves: decoder-only, last-token pooling, L2 normalization. Queries
get a one-sentence instruction prefix; documents are embedded plain.
"""
from __future__ import annotations

from functools import cached_property

import torch

from . import config

_DTYPES = {
    "bfloat16": torch.bfloat16,
    "float16": torch.float16,
    "float32": torch.float32,
}


class DenseEmbedder:
    def __init__(
        self,
        model_name: str = config.DENSE_MODEL,
        device: str = config.DEVICE,
        dtype: str = config.DTYPE,
        instruction: str = config.DENSE_QUERY_INSTRUCTION,
        max_length: int = 2048,
    ):
        self.model_name = model_name
        self.device = device
        self.torch_dtype = _DTYPES[dtype]
        self.instruction = instruction
        self.max_length = max_length

    @cached_property
    def _tokenizer(self):
        from transformers import AutoTokenizer

        return AutoTokenizer.from_pretrained(self.model_name)

    @cached_property
    def _model(self):
        from transformers import AutoModel

        model = AutoModel.from_pretrained(
            self.model_name,
            dtype=self.torch_dtype,
            low_cpu_mem_usage=True,
        )
        model.eval()
        return model.to(self.device)

    @property
    def dim(self) -> int:
        return self._model.config.hidden_size

    def _pool(self, hidden: torch.Tensor, mask: torch.Tensor) -> torch.Tensor:
        # Last-token pooling. Tokenizer is left-padded, so the final position is
        # always a real token; fall back to a mask gather if padding is right.
        if self._tokenizer.padding_side == "left":
            emb = hidden[:, -1]
        else:
            last = mask.sum(dim=1) - 1
            emb = hidden[torch.arange(hidden.size(0)), last]
        return torch.nn.functional.normalize(emb, p=2, dim=1)

    @torch.inference_mode()
    def _encode(
        self, texts: list[str], batch_size: int, progress: bool = False
    ) -> list[list[float]]:
        # Plain flushed prints, not a rich bar: this runs piped to a log
        # (non-TTY), where a live bar renders nothing until the end and
        # recreates a black box. Periodic stdout lines stay observable.
        import sys
        import time

        out: list[list[float]] = []
        total = len(texts)
        starts = list(range(0, total, batch_size))
        t0 = time.time()
        for n, i in enumerate(starts, 1):
            batch = texts[i : i + batch_size]
            enc = self._tokenizer(
                batch, padding=True, truncation=True,
                max_length=self.max_length, return_tensors="pt",
            ).to(self.device)
            hidden = self._model(**enc).last_hidden_state
            emb = self._pool(hidden, enc["attention_mask"])
            out.extend(emb.float().cpu().tolist())
            if progress and (n == 1 or n % 25 == 0 or n == len(starts)):
                done = min(i + batch_size, total)
                el = time.time() - t0
                eta = el / done * (total - done)
                print(
                    f"  embed {done}/{total} | {el:.0f}s elapsed | "
                    f"~{eta:.0f}s remaining | {done / el:.1f} chunks/s",
                    flush=True,
                )
        return out

    def embed_documents(self, texts: list[str], batch_size: int = 4) -> list[list[float]]:
        return self._encode(texts, batch_size, progress=True)

    def embed_query(self, text: str) -> list[float]:
        prompt = f"Instruct: {self.instruction}\nQuery: {text}"
        return self._encode([prompt], batch_size=1)[0]
