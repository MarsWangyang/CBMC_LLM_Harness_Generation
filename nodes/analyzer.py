"""
Analyzer node for CBMC harness generator workflow with unified RAG database integration.
"""
import time
import os
import re
from langchain_core.messages import AIMessage
from utils.rag import get_unified_db

def analyzer_node(state):
    """Analyzes code to identify functions with memory operations or arithmetic using unified RAG database."""
    # Start timing for analysis phase
    analysis_start = time.time()
    
    # Get source directory path
    source_dir = state.get("source_directory", "")
    print(f"DEBUG: Source directory: {source_dir}")
    
    # Get result directories for RAG storage
    result_directories = state.get("result_directories", {})
    
    # Initialize unified RAG database
    rag_db = get_unified_db(os.path.join(result_directories.get("result_base_dir", "results"), "rag_data"))
    
    # Try to get all functions from the unified database first
    # For backward compatibility, fall back to code_collection if needed
    try:
        from core.embedding_db import code_collection
        all_functions = code_collection.get()
        print(f"DEBUG: Retrieved {len(all_functions['ids'])} items from code_collection")
        
        # Store all functions in the unified database for future use
        for i, func_id in enumerate(all_functions["ids"]):
            # Skip patterns and declarations for now
            if func_id.startswith("pattern:") or func_id.startswith("declaration:"):
                continue
                
            # Add to unified database
            rag_db.add_code_function(
                func_id,
                all_functions["documents"][i],
                all_functions["metadatas"][i]
            )
            
    except Exception as e:
        print(f"ERROR: Failed to retrieve functions from database: {e}")
        all_functions = {"ids": [], "documents": [], "metadatas": []}
    
    # Detect CBMC framework patterns
    cbmc_utilities = {}
    cbmc_headers = []
    cbmc_utility_functions = {}
    
    # Look for header files with CBMC utilities
    for i, item_id in enumerate(all_functions["ids"]):
        # Check for header files related to CBMC
        if item_id.startswith("header:"):
            header_name = item_id.replace("header:", "")
            if "cbmc" in header_name.lower() or "test" in header_name.lower():
                cbmc_headers.append(header_name)
                document = all_functions["documents"][i]
                
                # Extract function declarations
                func_pattern = r"([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)\s*;"
                for match in re.finditer(func_pattern, document, re.MULTILINE):
                    return_type = match.group(1).strip()
                    func_name = match.group(2).strip()
                    params = match.group(3).strip()
                    
                    # Look for key utility functions
                    if any(pattern in func_name.lower() for pattern in ["allocate", "isvalid", "init", "create", "nondet", "malloc"]):
                        cbmc_utility_functions[func_name] = {
                            "return_type": return_type,
                            "params": params,
                            "header": header_name
                        }
    
    # Build a map of function name prefixes to likely harness naming patterns
    harness_naming_patterns = {}
    for i, item_id in enumerate(all_functions["ids"]):
        if "_harness" in item_id:
            parts = item_id.split("_harness")
            orig_func_name = parts[0].split(":")[-1] if ":" in parts[0] else parts[0]
            if orig_func_name:
                # Extract the function name before _harness
                harness_naming_patterns[orig_func_name] = f"{orig_func_name}_harness"
    
    target_functions = []
    
    # Process all functions in the database
    print(f"DEBUG: Processing {len(all_functions['ids'])} functions from database...")
    for i, func_id in enumerate(all_functions["ids"]):
        # Skip if not a regular function (e.g., declaration or header)
        if func_id.startswith("header:") or func_id.startswith("declaration:"):
            continue
            
        metadata = all_functions["metadatas"][i]
        func_code = all_functions["documents"][i]
        file_path = metadata.get("file_path", "")
        
        # Only process files that are in the source directory (not subdirectories)
        if file_path and os.path.exists(file_path):
            # Get the directory of the file
            file_dir = os.path.dirname(file_path)
            
            # Check if this is a file directly in the source directory (not subdirectory)
            is_source_file = False
            
            # Normalize paths for comparison
            norm_file_dir = os.path.normpath(file_dir)
            norm_source_dir = os.path.normpath(source_dir)
            
            # Check if file is directly in source directory
            if norm_file_dir == norm_source_dir:
                is_source_file = True
            
            # Only include source directory files (not dependency files)
            if is_source_file:
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
                ])
                
                # Add this function if it deals with memory or arithmetic
                if has_memory_ops or has_arithmetic:
                    print(f"DEBUG: Adding target function: {func_id} (from {file_path})")
                    target_functions.append(func_id)
                else:
                    print(f"DEBUG: Skipping function {func_id} - no memory/arithmetic ops")
            else:
                print(f"DEBUG: Skipping {func_id} - not in source directory (in {file_dir})")
        else:
            print(f"DEBUG: Skipping {func_id} - no valid file path")
    
    # Remove duplicates if any
    target_functions = list(set(target_functions))
    
    # Sort functions alphabetically for consistent processing order
    target_functions.sort()
    
    # If we still have no functions, we might need a fallback
    if not target_functions:
        print("WARNING: No functions match source directory criteria. Trying to find any .c files...")
        for i, func_id in enumerate(all_functions["ids"]):
            # Only check regular functions
            if not (func_id.startswith("header:") or func_id.startswith("declaration:")):
                metadata = all_functions["metadatas"][i]
                file_path = metadata.get("file_path", "")
                
                # Check if this is a .c or .cpp file
                if file_path and (file_path.endswith(".c") or file_path.endswith(".cpp")):
                    # Extract filename for debugging
                    filename = os.path.basename(file_path)
                    print(f"DEBUG: Adding fallback function: {func_id} (from {filename})")
                    target_functions.append(func_id)
    
    # Count functions by category
    category_count = {
        "memory": sum(1 for i, func_id in enumerate(all_functions["ids"]) 
                  if func_id in target_functions and
                     any(op in all_functions["documents"][i] for op in 
                     ["malloc(", "calloc(", "realloc(", "free(", "memcpy("])),
        "arithmetic": sum(1 for i, func_id in enumerate(all_functions["ids"]) 
                     if func_id in target_functions and
                        any(op in all_functions["documents"][i] for op in 
                        ["+", "-", "*", "/", "%", "+=", "-=", "*=", "/="]))
    }
    
    # Calculate time taken for analysis
    analysis_time = time.time() - analysis_start
    
    print(f"DEBUG: Will process {len(target_functions)} functions")
    for i, func_id in enumerate(target_functions[:10]):  # Print first 10 for debugging
        print(f"DEBUG: Target function {i}: {func_id}")
    
    return {
        "messages": [AIMessage(content=f"Analysis complete in {analysis_time:.2f}s. Identified {len(target_functions)} functions with memory or arithmetic operations. Breakdown: {category_count['memory']} with memory operations, {category_count['arithmetic']} with arithmetic operations.")],
        "vulnerable_functions": target_functions,
        "total_functions": len(target_functions),
        "current_function_index": 0,  # Initialize the index counter
        "cbmc_framework": {
            "has_framework": len(cbmc_utility_functions) > 0,
            "utility_functions": cbmc_utility_functions,
            "cbmc_headers": cbmc_headers,
            "harness_naming_patterns": harness_naming_patterns
        }
    }