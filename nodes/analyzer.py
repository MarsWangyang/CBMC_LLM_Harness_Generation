"""
Analyzer node for CBMC harness generator workflow.
"""
import time
import os
from langchain_core.messages import AIMessage
from core.embedding_db import code_collection

def analyzer_node(state):
    """Analyzes code from CodeDB to identify functions with memory operations or arithmetic."""
    # Start timing for analysis phase
    analysis_start = time.time()
    
    # Get all functions from the code database
    all_functions = code_collection.get()
    target_functions = []
    
    # Get source directory path
    source_dir = state.get("source_directory", "")
    
    # Process functions to find those with memory operations or arithmetic
    # Only include functions from files directly in the source directory (not subdirectories)
    for i, metadata in enumerate(all_functions["metadatas"]):
        func_id = all_functions["ids"][i]
        func_code = all_functions["documents"][i]
        file_path = metadata.get("file_path", "")
        
        # Skip functions from files in subdirectories like include, dependency, etc.
        if file_path:
            # Check if this is a file directly in the source directory
            if os.path.dirname(file_path) == source_dir:
                # Only process files directly in source dir
                # Check for memory operations
                has_memory_ops = any(op in func_code for op in [
                    "malloc(", "calloc(", "realloc(", "free(", "alloca(", 
                    "new ", "delete ", "memcpy(", "memmove(", "memset(",
                    "&", "*", "->", "[]"  # Memory-related operators
                ])
                
                # Check for arithmetic operations
                has_arithmetic = any(op in func_code for op in [
                    "+", "-", "*", "/", "%",  # Basic arithmetic
                    "+=", "-=", "*=", "/=", "%=",  # Compound assignment
                    "++", "--",  # Increment/decrement
                    "==", "!=", "<", ">", "<=", ">=",  # Comparison operators
                    "<<", ">>", "&", "|", "^", "~",  # Bitwise operations
                    "fabs(", "sqrt(", "pow(", "sin(", "cos(",  # Math functions
                    "int ", "float ", "double ", "long "  # Numeric types
                ])
                
                # Add this function if it deals with memory or arithmetic
                if has_memory_ops or has_arithmetic:
                    target_functions.append(func_id)
    
    # Remove duplicates if any
    target_functions = list(set(target_functions))
    
    # Sort functions alphabetically for consistent processing order
    target_functions.sort()
    
    # Count functions by category
    category_count = {
        "memory": sum(1 for i, metadata in enumerate(all_functions["metadatas"]) 
                  if any(op in all_functions["documents"][i] for op in 
                         ["malloc(", "calloc(", "realloc(", "free(", "memcpy("])),
        "arithmetic": sum(1 for i, metadata in enumerate(all_functions["metadatas"]) 
                     if any(op in all_functions["documents"][i] for op in 
                            ["+", "-", "*", "/", "%", "+=", "-=", "*=", "/="]))
    }
    
    # Calculate time taken for analysis
    analysis_time = time.time() - analysis_start
    
    return {
        "messages": [AIMessage(content=f"Analysis complete in {analysis_time:.2f}s. Identified {len(target_functions)} functions with memory or arithmetic operations. Breakdown: {category_count['memory']} with memory operations, {category_count['arithmetic']} with arithmetic operations.")],
        "vulnerable_functions": target_functions,
        "total_functions": len(target_functions),
        "current_function_index": 0  # Initialize the index counter
    }