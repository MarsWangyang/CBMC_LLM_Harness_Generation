"""
Database setup and querying functions for code embeddings and patterns.
"""
import os
import chromadb
from chromadb.utils import embedding_functions
from typing import Dict, List, Any

# Set up ChromaDB
chroma_client = chromadb.Client()
sentence_transformer_ef = embedding_functions.SentenceTransformerEmbeddingFunction(model_name="all-MiniLM-L6-v2")

# Initialize collections
def initialize_collections():
    """Initialize and return the code and pattern collections."""
    # Create or get code collection
    try:
        code_collection = chroma_client.get_collection("code_embeddings")
    except:
        code_collection = chroma_client.create_collection(
            name="code_embeddings",
            embedding_function=sentence_transformer_ef,
            metadata={"hnsw:space": "cosine"}
        )

    # Create or get pattern collection
    try:
        pattern_collection = chroma_client.get_collection("pattern_embeddings")
    except:
        pattern_collection = chroma_client.create_collection(
            name="pattern_embeddings",
            embedding_function=sentence_transformer_ef,
            metadata={"hnsw:space": "cosine"}
        )
        
        # Initialize pattern collection with memory and arithmetic patterns
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
                # Memory patterns metadata
                {
                    "name": "malloc_without_free",
                    "category": "memory",
                    "description": "Allocation without corresponding deallocation",
                    "severity": "high",
                    "verification_strategy": "Check all execution paths for memory deallocation",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(ptr == NULL, \"Memory leak detected\");"
                },
                {
                    "name": "nested_malloc",
                    "category": "memory",
                    "description": "Nested malloc calls with potential for partial free",
                    "severity": "medium",
                    "verification_strategy": "Ensure all allocations are freed in all execution paths",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(ptr1 == NULL && ptr2 == NULL, \"Nested memory leak detected\");"
                },
                {
                    "name": "conditional_free",
                    "category": "memory",
                    "description": "Conditional free that might not execute",
                    "severity": "medium",
                    "verification_strategy": "Verify all conditions that lead to memory release",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(condition || ptr == NULL, \"Conditional path may leak memory\");"
                },
                {
                    "name": "return_leak",
                    "category": "memory",
                    "description": "Memory leak through improper return path",
                    "severity": "medium",
                    "verification_strategy": "Check all return paths for proper memory cleanup",
                    "cbmc_flags": "--memory-leak-check --memory-cleanup-check",
                    "assertion_template": "__CPROVER_assert(returned_ptr == NULL, \"Function may leak memory through return\");"
                },
                {
                    "name": "double_free",
                    "category": "memory",
                    "description": "Double free or invalid free operations",
                    "severity": "high",
                    "verification_strategy": "Ensure each pointer is freed exactly once",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(!freed[ptr_index], \"Potential double free\");"
                },
                
                # Arithmetic patterns metadata
                {
                    "name": "integer_overflow",
                    "category": "arithmetic",
                    "description": "Integer overflow in arithmetic operations",
                    "severity": "medium",
                    "verification_strategy": "Check bounds of integer arithmetic",
                    "cbmc_flags": "--conversion-check",
                    "assertion_template": "__CPROVER_assert(result >= INT_MIN && result <= INT_MAX, \"Integer overflow detected\");"
                },
                {
                    "name": "division_by_zero",
                    "category": "arithmetic",
                    "description": "Division by zero risk",
                    "severity": "high",
                    "verification_strategy": "Verify divisors are non-zero",
                    "cbmc_flags": "--div-by-zero-check",
                    "assertion_template": "__CPROVER_assume(divisor != 0);"
                },
                {
                    "name": "buffer_overflow",
                    "category": "arithmetic",
                    "description": "Buffer overflow through array indexing",
                    "severity": "high",
                    "verification_strategy": "Ensure array indices are within bounds",
                    "cbmc_flags": "--bounds-check",
                    "assertion_template": "__CPROVER_assert(index >= 0 && index < array_size, \"Buffer overflow detected\");"
                },
                {
                    "name": "pointer_arithmetic",
                    "category": "arithmetic",
                    "description": "Pointer arithmetic exceeding bounds",
                    "severity": "high",
                    "verification_strategy": "Verify pointer arithmetic stays within allocated bounds",
                    "cbmc_flags": "--pointer-overflow-check",
                    "assertion_template": "__CPROVER_assert(ptr >= base && ptr < base + size, \"Pointer arithmetic out of bounds\");"
                },
                {
                    "name": "type_conversion",
                    "category": "arithmetic",
                    "description": "Type conversion issues leading to data loss",
                    "severity": "low",
                    "verification_strategy": "Check for potential data loss in type conversions",
                    "cbmc_flags": "--conversion-check",
                    "assertion_template": "__CPROVER_assert(orig_value == (OrigType)((DestType)orig_value), \"Data loss in type conversion\");"
                },
                
                # CBMC verification knowledge metadata
                {
                    "name": "cbmc_memory_leak_check",
                    "category": "cbmc_verification",
                    "description": "Checks for memory that is allocated but not freed",
                    "verification_details": "Detects allocated memory that is never freed, memory that becomes unreachable, and double free operations",
                    "harness_usage": "Create appropriate memory allocations and verify they are properly freed",
                    "flag": "--memory-leak-check"
                },
                {
                    "name": "cbmc_memory_cleanup_check",
                    "category": "cbmc_verification",
                    "description": "Verifies all allocated memory is properly freed before program exit",
                    "verification_details": "More stringent than memory-leak-check, requires explicit cleanup of all allocations",
                    "harness_usage": "Ensure all memory allocations have corresponding free operations",
                    "flag": "--memory-cleanup-check"
                },
                {
                    "name": "cbmc_bounds_check",
                    "category": "cbmc_verification",
                    "description": "Verifies array accesses are within bounds",
                    "verification_details": "Detects buffer overflows and underflows for both static and dynamic arrays",
                    "harness_usage": "Test array accesses with both valid and invalid indices",
                    "flag": "--bounds-check"
                },
                {
                    "name": "cbmc_pointer_overflow_check",
                    "category": "cbmc_verification",
                    "description": "Detects pointer arithmetic that results in overflow",
                    "verification_details": "Checks pointer arithmetic operations to prevent undefined behavior",
                    "harness_usage": "Test pointer arithmetic operations with boundary values",
                    "flag": "--pointer-overflow-check"
                },
                {
                    "name": "cbmc_conversion_check",
                    "category": "cbmc_verification",
                    "description": "Detects problematic type conversions",
                    "verification_details": "Identifies loss of information in numeric conversions and sign conversion issues",
                    "harness_usage": "Test type conversions with values that may cause information loss",
                    "flag": "--conversion-check"
                },
                {
                    "name": "cbmc_div_by_zero_check",
                    "category": "cbmc_verification",
                    "description": "Checks for division by zero errors",
                    "verification_details": "Verifies both integer and floating-point divisions and modulo operations with zero divisor",
                    "harness_usage": "Test division operations with zero and near-zero divisors",
                    "flag": "--div-by-zero-check"
                }
            ]
        )
    
    return code_collection, pattern_collection

# Initialize collections globally
code_collection, pattern_collection = initialize_collections()

def query_pattern_db(query: str) -> Dict[str, Any]:
    """Queries the ChromaDB pattern database for known memory leak patterns."""
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
                    "verification_strategy": metadata["verification_strategy"],
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
                        "verification_strategy": metadata["verification_strategy"],
                        "similarity_score": 1.0  # Direct match gets perfect score
                    }
                    break
    
    return {
        "matching_patterns": matching_patterns,
        "message": f"Found {len(matching_patterns)} potential matching patterns via ChromaDB"
    }