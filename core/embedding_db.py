"""
Database setup and querying functions for code embeddings and patterns.
This module works with both direct ChromaDB access and the unified RAG database.
"""
import os
import chromadb
from chromadb.utils import embedding_functions
from typing import Dict, List, Any
import logging

def _initialize_pattern_collection():
    """Initialize pattern collection with common memory and arithmetic patterns."""
    pattern_collection.add(
        ids=[
            # Memory patterns
            "pattern1", "pattern2", "pattern3", "pattern4", "pattern5",
            # Arithmetic patterns
            "pattern6", "pattern7", "pattern8", "pattern9", "pattern10",
            # CBMC verification knowledge
            "cbmc1", "cbmc2", "cbmc3", "cbmc4", "cbmc5", "cbmc6"
        ],
        documents=[
            # Memory patterns
            "Allocation without corresponding deallocation (malloc without free)",
            "Nested malloc calls with potential for partial free",
            "Conditional free that might not execute in all paths",
            "Memory leak through improper return path",
            "Double free or invalid free operations",
            
            # Arithmetic patterns
            "Integer overflow in arithmetic operations",
            "Division by zero risk",
            "Buffer overflow through array indexing",
            "Pointer arithmetic exceeding bounds",
            "Type conversion issues leading to data loss",
            
            # CBMC verification knowledge
            "CBMC memory-leak-check verification for allocated but not freed memory",
            "CBMC memory-cleanup-check verification for proper memory cleanup before exit",
            "CBMC bounds-check verification for array access within bounds",
            "CBMC pointer-overflow-check verification for pointer arithmetic operations",
            "CBMC conversion-check verification for problematic type conversions",
            "CBMC div-by-zero-check verification for division by zero risks"
        ],
        metadatas=[
            # Memory patterns metadata (simplified for brevity)
            {"name": "malloc_without_free", "category": "memory", "description": "Allocation without corresponding deallocation", "severity": "high"},
            {"name": "nested_malloc", "category": "memory", "description": "Nested malloc calls with potential for partial free", "severity": "medium"},
            {"name": "conditional_free", "category": "memory", "description": "Conditional free that might not execute", "severity": "medium"},
            {"name": "return_leak", "category": "memory", "description": "Memory leak through improper return path", "severity": "medium"},
            {"name": "double_free", "category": "memory", "description": "Double free or invalid free operations", "severity": "high"},
            
            # Arithmetic patterns metadata (simplified for brevity)
            {"name": "integer_overflow", "category": "arithmetic", "description": "Integer overflow in arithmetic operations", "severity": "medium"},
            {"name": "division_by_zero", "category": "arithmetic", "description": "Division by zero risk", "severity": "high"},
            {"name": "buffer_overflow", "category": "arithmetic", "description": "Buffer overflow through array indexing", "severity": "high"},
            {"name": "pointer_arithmetic", "category": "arithmetic", "description": "Pointer arithmetic exceeding bounds", "severity": "high"},
            {"name": "type_conversion", "category": "arithmetic", "description": "Type conversion issues leading to data loss", "severity": "low"},
            
            # CBMC verification knowledge metadata (simplified for brevity)
            {"name": "cbmc_memory_leak_check", "category": "cbmc_verification", "description": "Checks for memory that is allocated but not freed"},
            {"name": "cbmc_memory_cleanup_check", "category": "cbmc_verification", "description": "Verifies all allocated memory is properly freed before program exit"},
            {"name": "cbmc_bounds_check", "category": "cbmc_verification", "description": "Verifies array accesses are within bounds"},
            {"name": "cbmc_pointer_overflow_check", "category": "cbmc_verification", "description": "Detects pointer arithmetic that results in overflow"},
            {"name": "cbmc_conversion_check", "category": "cbmc_verification", "description": "Detects problematic type conversions"},
            {"name": "cbmc_div_by_zero_check", "category": "cbmc_verification", "description": "Checks for division by zero errors"}
        ]
    )

# Set up logging
logger = logging.getLogger("embedding_db")

# Set up ChromaDB - Initialize directly first
# Later this can be updated to use unified RAG database
chroma_client = chromadb.Client()
sentence_transformer_ef = embedding_functions.SentenceTransformerEmbeddingFunction(model_name="all-MiniLM-L6-v2")

# Initialize collections
try:
    code_collection = chroma_client.get_collection(
        name="code_embeddings",
        embedding_function=sentence_transformer_ef
    )
    logger.info("Retrieved existing code collection")
except:
    code_collection = chroma_client.create_collection(
        name="code_embeddings",
        embedding_function=sentence_transformer_ef,
        metadata={"hnsw:space": "cosine"}
    )
    logger.info("Created new code collection")

try:
    pattern_collection = chroma_client.get_collection(
        name="pattern_embeddings",
        embedding_function=sentence_transformer_ef
    )
    logger.info("Retrieved existing pattern collection")
except:
    pattern_collection = chroma_client.create_collection(
        name="pattern_embeddings",
        embedding_function=sentence_transformer_ef,
        metadata={"hnsw:space": "cosine"}
    )
    _initialize_pattern_collection()
    logger.info("Created new pattern collection with initial patterns")



def initialize_collections():
    """
    Initialize and return the code and pattern collections.
    
    Returns:
        A tuple of (code_collection, pattern_collection)
    """
    return code_collection, pattern_collection

def query_pattern_db(query: str) -> Dict[str, Any]:
    """
    Queries the pattern database for known memory leak patterns.
    
    This is a baseline implementation that will be replaced with the
    unified RAG database version when available.
    
    Args:
        query: The query text
        
    Returns:
        A dictionary with matching patterns
    """
    # Query the pattern collection to find relevant patterns
    results = pattern_collection.query(
        query_texts=[query],
        n_results=3  # Get the top 3 matching patterns
    )
    
    # Also check via metadata if the function contains known indicators
    if "malloc(" in query and "free(" not in query:
        # Direct metadata match for malloc without free
        direct_match = "malloc_without_free"
    elif "if" in query and "free(" in query:
        # Potential conditional free
        direct_match = "conditional_free"
    elif query.count("malloc(") > 1:
        # Multiple malloc calls
        direct_match = "nested_malloc"
    else:
        direct_match = None
    
    # Process results
    matching_patterns = {}
    
    # Add patterns from semantic search
    if len(results['ids']) > 0:
        for i, (pattern_id, metadata, distance) in enumerate(zip(
            results['ids'][0],
            results['metadatas'][0],
            results['distances'][0]
        )):
            # Only include if reasonably close in embedding space
            if distance < 0.3:
                matching_patterns[metadata['name']] = {
                    "description": metadata["description"],
                    "severity": metadata["severity"],
                    "verification_strategy": metadata.get("verification_strategy", "Check for potential issues"),
                    "similarity_score": 1.0 - distance  # Convert to similarity
                }
    
    # Add direct match if found and not already included
    if direct_match and direct_match not in matching_patterns:
        # Find the metadata for this pattern
        pattern_match_idx = ['malloc_without_free', 'nested_malloc', 'conditional_free'].index(direct_match) + 1
        pattern_id = f"pattern{pattern_match_idx}"
        metadata_results = pattern_collection.get(ids=[pattern_id])
        if metadata_results['ids']:
            for metadata in metadata_results['metadatas']:
                if metadata['name'] == direct_match:
                    matching_patterns[direct_match] = {
                        "description": metadata["description"],
                        "severity": metadata["severity"],
                        "verification_strategy": metadata.get("verification_strategy", "Check for potential issues"),
                        "similarity_score": 1.0  # Direct match gets perfect score
                    }
                    break
    
    return {
        "matching_patterns": matching_patterns,
        "message": f"Found {len(matching_patterns)} potential matching patterns via ChromaDB"
    }

# This function will be replaced by main.py when the RAG system is initialized
# with an updated version that uses the unified RAG database