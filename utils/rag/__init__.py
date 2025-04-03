"""
RAG (Retrieval-Augmented Generation) package for the CBMC harness generator.

This package provides a unified database for storing and retrieving embeddings
for code functions, patterns, errors, and solutions.
"""
from utils.rag.db import get_unified_db, UnifiedEmbeddingDB

# Expose the main interface at the package level
__all__ = ['get_unified_db', 'UnifiedEmbeddingDB']