"""Dense embeddings via Microsoft Harrier-OSS-v1-27b.

Queries get a one-sentence instruction prefix ("Instruct: …\\nQuery: …");
documents are embedded plain (per the model card). Decoder-only with last-token
pooling + L2 norm — sentence-transformers applies the model's own pooling.
"""
from __future__ import annotations

from functools import cached_property

from . import config


class DenseEmbedder:
    def __init__(
        self,
        model_name: str = config.DENSE_MODEL,
        device: str = config.DEVICE,
        dtype: str = config.DTYPE,
        instruction: str = config.DENSE_QUERY_INSTRUCTION,
    ):
        self.model_name = model_name
        self.device = device
        self.dtype = dtype
        self.instruction = instruction

    @cached_property
    def _model(self):
        from sentence_transformers import SentenceTransformer

        return SentenceTransformer(
            self.model_name,
            device=self.device,
            model_kwargs={"torch_dtype": self.dtype},
        )

    @property
    def dim(self) -> int:
        return self._model.get_sentence_embedding_dimension()

    def embed_documents(self, texts: list[str], batch_size: int = 8) -> list[list[float]]:
        vecs = self._model.encode(
            texts, batch_size=batch_size, normalize_embeddings=True,
            show_progress_bar=True,
        )
        return [v.tolist() for v in vecs]

    def embed_query(self, text: str) -> list[float]:
        prompt = f"Instruct: {self.instruction}\nQuery: "
        vec = self._model.encode(
            [text], prompt=prompt, normalize_embeddings=True,
            show_progress_bar=False,
        )[0]
        return vec.tolist()
