"""
Code parsing utilities for the CBMC harness generator.
"""
import os
import re
import json
from tqdm import tqdm
from core.embedding_db import code_collection
import logging

logger = logging.getLogger("code_parser")

def sanitize_metadata(metadata):
    """
    Sanitize metadata to ensure all values are compatible with chromadb requirements.
    Replaces None values with empty strings and ensures lists are JSON-serialized.
    
    Args:
        metadata: Dictionary of metadata to sanitize
        
    Returns:
        Dictionary with sanitized metadata values
    """
    if not isinstance(metadata, dict):
        logger.warning(f"sanitize_metadata called with non-dict type: {type(metadata)}")
        return {}
    
    sanitized = {}
    for key, value in metadata.items():
        if value is None:
            # Replace None with empty string
            sanitized[key] = ""
        elif isinstance(value, (list, dict, set, tuple)):
            # JSON serialize complex types
            try:
                sanitized[key] = json.dumps(value)
            except Exception as e:
                logger.warning(f"Failed to JSON serialize {key}: {str(e)}")
                sanitized[key] = str(value)  # Fallback to string representation
        else:
            # Keep primitive types as is
            sanitized[key] = value
    
    return sanitized

def extract_header_information(content, file_path):
    """Extract includes, macros, and declarations from header files."""
    header_info = {
        "includes": [],
        "macros": [],
        "type_definitions": [],
        "function_declarations": [],
        "file_path": file_path
    }
    
    # Extract includes
    include_pattern = r'#include\s+[<"]([^>"]+)[>"]'
    header_info["includes"] = re.findall(include_pattern, content)
    
    # Extract macro definitions - ENHANCED to capture more macro formats
    macro_pattern = r'#define\s+(\w+)(?:\(([^)]*)\))?\s+(.+?)(?=(?:\n#)|$)'
    macro_matches = re.finditer(macro_pattern, content, re.MULTILINE | re.DOTALL)
    for match in macro_matches:
        macro_name = match.group(1)
        macro_params = match.group(2)
        macro_value = match.group(3).strip()
        header_info["macros"].append({
            "name": macro_name,
            "params": macro_params,
            "value": macro_value,
            "full_definition": match.group(0)
        })
    
    # Also look for multi-line macros using backslash continuation
    multiline_macro_pattern = r'#define\s+(\w+)(?:\(([^)]*)\))?\s+(.*?\\(?:\r?\n).*?)(?=(?:\n#)|$)'
    multiline_macro_matches = re.finditer(multiline_macro_pattern, content, re.MULTILINE | re.DOTALL)
    for match in multiline_macro_matches:
        macro_name = match.group(1)
        macro_params = match.group(2)
        macro_value = match.group(3).replace('\\\n', ' ').strip()
        header_info["macros"].append({
            "name": macro_name,
            "params": macro_params,
            "value": macro_value,
            "full_definition": match.group(0),
            "is_multiline": True
        })
    
    # Extract type definitions (structs, enums, typedefs)
    typedef_pattern = r'typedef\s+([^;]+);'
    struct_pattern = r'(?:typedef\s+)?struct\s+(\w+)\s*{([^}]+)}'
    enum_pattern = r'(?:typedef\s+)?enum\s+(\w+)\s*{([^}]+)}'
    
    for typedef in re.finditer(typedef_pattern, content, re.MULTILINE | re.DOTALL):
        header_info["type_definitions"].append({
            "type": "typedef",
            "definition": typedef.group(0)
        })
    
    for struct in re.finditer(struct_pattern, content, re.MULTILINE | re.DOTALL):
        header_info["type_definitions"].append({
            "type": "struct",
            "name": struct.group(1),
            "definition": struct.group(0)
        })
        
    for enum in re.finditer(enum_pattern, content, re.MULTILINE | re.DOTALL):
        header_info["type_definitions"].append({
            "type": "enum",
            "name": enum.group(1),
            "definition": enum.group(0)
        })
    
    # Extract function declarations (not definitions)
    func_decl_pattern = r'([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)\s*;'
    for match in re.finditer(func_decl_pattern, content, re.MULTILINE):
        return_type = match.group(1).strip()
        func_name = match.group(2)
        params = match.group(3).strip()
        
        # Store all declarations, including ones that match keywords
        # Just add a flag to identify keyword matches
        is_keyword = func_name in ['if', 'for', 'while', 'switch', 'return', 'include', 'sizeof']
            
        header_info["function_declarations"].append({
            "name": func_name,
            "return_type": return_type,
            "params": params,
            "declaration": match.group(0),
            "is_keyword": is_keyword
        })
    
    return header_info

def embed_code(code: str, file_path: str = None) -> dict:
    """Embeds source code and stores it in the ChromaDB embedding database."""
    # Parse the code to extract functions
    functions = {}
    header_chunks = {}
    code_patterns = {}  # For storing other code patterns like control structures
    
    # Skip if code is empty
    if not code:
        logger.warning("Empty code provided for embedding")
        return {"functions": {}, "headers": {}, "code_patterns": {}, "message": "No code to embed"}
    
    # Use a thread-safe flag to clear the collection only once per run
    # This static variable approach is better than using a global
    if not hasattr(embed_code, "_collection_cleared"):
        embed_code._collection_cleared = False
    
    # Clear existing collection only once at the start
    if not embed_code._collection_cleared:
        try:
            logger.info("First file being processed - clearing existing code collection")
            existing_ids = code_collection.get()["ids"]
            if existing_ids:
                logger.info(f"Deleting {len(existing_ids)} existing entries from code collection")
                code_collection.delete(ids=existing_ids)
            embed_code._collection_cleared = True
        except Exception as e:
            logger.error(f"Error clearing code collection: {str(e)}")
            embed_code._collection_cleared = True  # Mark as cleared even if it failed
    
    # Show file info
    file_name = os.path.basename(file_path) if file_path else "inline"
    logger.info(f"Processing file: {file_name}")
    
    # Special handling for header files
    is_header = file_path and file_path.endswith(('.h', '.hpp'))
    
    if is_header:
        # Process header file specially
        header_info = extract_header_information(code, file_path)
        
        # Store header file information with file path as key
        header_id = os.path.basename(file_path)
        header_chunks[header_id] = header_info
        
        # Add each function declaration to the function database
        for decl in header_info["function_declarations"]:
            func_id = f"{header_id}:{decl['name']}"
            
            # Add special prefix for keyword matches to avoid confusion with real functions
            if decl.get("is_keyword", False):
                func_id = f"pattern:{func_id}"
            
            functions[func_id] = {
                "return_type": decl["return_type"],
                "params": decl["params"],
                "body": "",  # No body for declarations
                "full_text": decl["declaration"],
                "file_path": file_path,
                "original_name": decl["name"],
                "is_declaration_only": True,
                "is_keyword": decl.get("is_keyword", False)
            }
            
        # Add header information to the database
        try:
            # Create a more detailed header document including macro count
            header_document = (
                f"Header file: {header_id}\n"
                f"Includes: {', '.join(header_info['includes'])}\n"
                f"Function declarations: {len(header_info['function_declarations'])}\n"
                f"Type definitions: {len(header_info['type_definitions'])}\n"
                f"Macros: {len(header_info['macros'])}"
            )
            
            # Add macro names to the header document if any exist
            if header_info['macros']:
                header_document += "\nMacro names: " + ", ".join([m["name"] for m in header_info['macros']])
            
            # Add header to collection with serialized list fields and macro information
            header_metadata = {
                "type": "header",
                "file_path": file_path,
                "includes": header_info["includes"],
                "declaration_count": len(header_info["function_declarations"]),
                "typedef_count": len(header_info["type_definitions"]),
                "macro_count": len(header_info["macros"]),
                "macros": [m["name"] for m in header_info["macros"]],
                "has_multiline_macros": any(m.get("is_multiline", False) for m in header_info["macros"])
            }
            
            # Use sanitize_metadata to properly handle all values
            header_metadata = sanitize_metadata(header_metadata)
            
            # Add to collection
            code_collection.add(
                ids=[f"header:{header_id}"],
                documents=[header_document],
                metadatas=[header_metadata]
            )
            
            # Add function declarations to collection separately
            for decl in header_info["function_declarations"]:
                # Create appropriate ID based on whether it's a keyword match
                decl_id = f"declaration:{header_id}:{decl['name']}"
                if decl.get("is_keyword", False):
                    decl_id = f"pattern:{decl_id}"
                
                # Create metadata
                decl_metadata = {
                    "type": "function_declaration",
                    "name": decl["name"],
                    "return_type": decl["return_type"],
                    "params": decl["params"],
                    "file_path": file_path,
                    "header": header_id,
                    "is_keyword": decl.get("is_keyword", False)
                }
                
                # Use sanitize_metadata function to handle all values properly
                decl_metadata = sanitize_metadata(decl_metadata)
                
                code_collection.add(
                    ids=[decl_id],
                    documents=[decl["declaration"]],
                    metadatas=[decl_metadata]
                )
            
            # Add macro definitions separately
            for macro in header_info["macros"]:
                # Create macro ID
                macro_id = f"macro:{header_id}:{macro['name']}"
                
                # Generate a macro definition document
                if macro.get("params"):
                    macro_doc = f"#define {macro['name']}({macro['params']}) {macro['value']}"
                else:
                    macro_doc = f"#define {macro['name']} {macro['value']}"
                
                # Create macro metadata
                macro_metadata = {
                    "type": "macro",
                    "name": macro["name"],
                    "params": macro.get("params", ""),
                    "value": macro["value"],
                    "header": header_id,
                    "file_path": file_path,
                    "is_multiline": macro.get("is_multiline", False)
                }
                
                # Use sanitize_metadata function to handle all values properly
                macro_metadata = sanitize_metadata(macro_metadata)
                
                code_collection.add(
                    ids=[macro_id],
                    documents=[macro_doc],
                    metadatas=[macro_metadata]
                )
            
            logger.info(f"Processed header file {header_id} with {len(header_info['function_declarations'])} declarations and {len(header_info['macros'])} macros")
        except Exception as e:
            logger.error(f"Error adding header information to database: {str(e)}")
        
        return {"functions": functions, "headers": header_chunks, "code_patterns": code_patterns, "message": "Processed header file declarations and macros"}
    
    try:
        # Use a more comprehensive pattern for C/C++ functions
        # This pattern matches both standard C functions and functions with additional specifiers
        c_func_pattern = r"((?:static|extern|inline|const|volatile|__attribute__\([^)]*\)\s*)*\s*[\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)\s*(?:(?:const|volatile|throw\([^)]*\)|noexcept)\s*)*\s*\{"
        
        # Use direct search instead of splitting first
        matches = list(re.finditer(c_func_pattern, code, re.MULTILINE))
        
        # Process each potential function without progress bar
        function_ids = []
        function_texts = []
        function_metadatas = []
        
        # Keep track of functions by file and name to avoid duplicates but allow same name in different files
        processed_func_keys = set()
        
        # Track patterns and structures that may be misidentified as functions
        pattern_ids = []
        pattern_texts = []
        pattern_metadatas = []
        
        # Statistics tracking
        match_categories = {
            "normal_function": 0,
            "keyword_match": 0,
            "brace_mismatch": 0,
            "duplicate": 0,
            "empty_body": 0,
            "other_error": 0
        }
        
        # Process functions without tqdm progress bar
        logger.info(f"Analyzing {len(matches)} potential functions in {file_name}")
        processed_count = 0
        keyword_count = 0
        
        # List of C/C++ keywords that might appear in matching patterns
        c_keywords = [
            'if', 'for', 'while', 'switch', 'return', 'include', 'sizeof',
            'do', 'case', 'default', 'goto', 'typedef', 'enum', 'struct',
            'union', 'continue', 'break'
        ]
        
        for match in matches:
            func_key = None
            try:
                return_type = match.group(1).strip()
                func_name = match.group(2).strip()
                params = match.group(3).strip()
                
                # Create function key for deduplication
                if file_path:
                    file_basename = os.path.basename(file_path)
                    func_key = f"{file_basename}:{func_name}"
                else:
                    func_key = func_name
                
                # Check if func_name is a keyword - still process but mark it
                is_keyword = func_name in c_keywords
                
                if is_keyword:
                    match_categories["keyword_match"] += 1
                    keyword_count += 1
                    # Use a special prefix for keyword matches in the ID
                    if file_path:
                        func_id = f"pattern:{file_basename}:{func_name}"
                    else:
                        func_id = f"pattern:{func_name}"
                else:
                    # Regular function
                    if file_path:
                        func_id = f"{file_basename}:{func_name}"
                    else:
                        func_id = func_name
                
                # Skip if we've already processed this function in this file
                if func_key in processed_func_keys:
                    match_categories["duplicate"] += 1
                    continue
                
                # Log functions being considered
                logger.debug(f"Processing potential {'pattern' if is_keyword else 'function'}: {func_key}")
                
                # Find function body with improved algorithm
                start_pos = match.end()
                brace_count = 1
                end_pos = start_pos
                
                # Find the matching closing brace by counting
                try:
                    while brace_count > 0 and end_pos < len(code):
                        if code[end_pos] == '{':
                            brace_count += 1
                        elif code[end_pos] == '}':
                            brace_count -= 1
                        end_pos += 1
                except IndexError:
                    logger.debug(f"Index error finding body end for {func_key}")
                    match_categories["brace_mismatch"] += 1
                    continue
                
                # If we couldn't find matching braces, skip this function
                if brace_count > 0:
                    logger.debug(f"Unbalanced braces in {func_key}, skipping")
                    match_categories["brace_mismatch"] += 1
                    continue
                
                # Extract body including braces (the first { until the matching })
                body = code[start_pos-1:end_pos]
                
                # Verify body validity - should have at least one statement
                if len(body.strip()) <= 2:  # Just {} with possibly whitespace
                    logger.debug(f"Empty function body for {func_key}, skipping")
                    match_categories["empty_body"] += 1
                    continue
                
                # Create function ID with file info if provided
                
                # Get full function text
                full_text = f"{return_type} {func_name}({params}) {body}"
                
                # Extract function calls within this function
                function_calls = re.findall(r'\b(\w+)\s*\(', body)
                # Remove duplicates while preserving order
                function_calls = list(dict.fromkeys(function_calls))
                
                # Prepare common metadata
                common_metadata = {
                    "name": func_name,
                    "id": func_id,
                    "return_type": return_type,
                    "params": params,
                    "has_malloc": "malloc(" in body,
                    "has_free": "free(" in body,
                    "allocation_without_free": "malloc(" in body and "free(" not in body,
                    "file_path": file_path if file_path else "inline",
                    "function_calls": json.dumps(function_calls),  # Convert list to JSON string
                    "is_implementation": True,
                    "is_keyword": is_keyword
                }
                
                # Store in appropriate result structure
                processed_func_keys.add(func_key)
                
                if is_keyword:
                    # Store as a code pattern
                    code_patterns[func_id] = {
                        "pattern_type": "control_structure",
                        "keyword": func_name,
                        "return_type": return_type,
                        "params": params,
                        "body": body,
                        "full_text": full_text,
                        "file_path": file_path,
                        "original_name": func_name,
                    }
                    
                    # Add to pattern arrays for ChromaDB
                    pattern_ids.append(func_id)
                    pattern_texts.append(full_text)
                    pattern_metadatas.append(dict(common_metadata, type="code_pattern"))
                    
                else:
                    # Store as a regular function
                    match_categories["normal_function"] += 1
                    functions[func_id] = {
                        "return_type": return_type,
                        "params": params,
                        "body": body,
                        "full_text": full_text,
                        "file_path": file_path,
                        "original_name": func_name,
                        "has_malloc": "malloc(" in body,
                        "has_free": "free(" in body,
                        "function_calls": function_calls,
                        "is_declaration_only": False
                    }
                    
                    # Add to function arrays for ChromaDB
                    function_ids.append(func_id)
                    function_texts.append(full_text)
                    function_metadatas.append(dict(common_metadata, type="function"))
                
                processed_count += 1
                # Log progress periodically (every 10 functions)
                if processed_count % 10 == 0:
                    logger.debug(f"Processed {processed_count}/{len(matches)} functions")
                    
            except Exception as e:
                match_categories["other_error"] += 1
                logger.debug(f"Error processing function: {str(e)}")
        
        # Log detailed statistics
        logger.info(f"Successfully processed {processed_count} code structures from {file_name}")
        logger.info(f"Classification: {match_categories}")
        
        # Add functions to ChromaDB in batches
        if function_ids:
            # Add in batches to avoid potential memory issues with large codebases
            batch_size = 100
            for i in range(0, len(function_ids), batch_size):
                end_idx = min(i + batch_size, len(function_ids))
                batch_ids = function_ids[i:end_idx]
                batch_texts = function_texts[i:end_idx]
                batch_metadatas = function_metadatas[i:end_idx]
                
                logger.info(f"Adding batch of {len(batch_ids)} functions to ChromaDB (batch {i//batch_size + 1})")
                try:
                    # Sanitize all metadata in the batch
                    sanitized_metadatas = [sanitize_metadata(metadata) for metadata in batch_metadatas]
                    
                    code_collection.add(
                        ids=batch_ids,
                        documents=batch_texts,
                        metadatas=sanitized_metadatas
                    )
                except Exception as e:
                    logger.error(f"Error adding batch to ChromaDB: {str(e)}")
                    # Try to add individually to isolate problematic functions
                    for j in range(len(batch_ids)):
                        try:
                            # Sanitize individual metadata
                            sanitized_metadata = sanitize_metadata(batch_metadatas[j])
                            
                            code_collection.add(
                                ids=[batch_ids[j]],
                                documents=[batch_texts[j]],
                                metadatas=[sanitized_metadata]
                            )
                        except Exception as e2:
                            logger.error(f"Failed to add function {batch_ids[j]}: {str(e2)}")
            
            logger.info(f"Added total of {len(function_ids)} functions to ChromaDB")
        
        # Add code patterns to ChromaDB
        if pattern_ids:
            logger.info(f"Adding {len(pattern_ids)} code patterns to ChromaDB")
            try:
                # Sanitize all pattern metadata
                sanitized_pattern_metadatas = [sanitize_metadata(metadata) for metadata in pattern_metadatas]
                
                code_collection.add(
                    ids=pattern_ids,
                    documents=pattern_texts,
                    metadatas=sanitized_pattern_metadatas
                )
                logger.info(f"Added {len(pattern_ids)} code patterns to ChromaDB")
            except Exception as e:
                logger.error(f"Error adding code patterns to ChromaDB: {str(e)}")
                # Try to add individually
                for i in range(len(pattern_ids)):
                    try:
                        # Sanitize individual pattern metadata
                        sanitized_metadata = sanitize_metadata(pattern_metadatas[i])
                        
                        code_collection.add(
                            ids=[pattern_ids[i]],
                            documents=[pattern_texts[i]],
                            metadatas=[sanitized_metadata]
                        )
                    except Exception as e2:
                        logger.error(f"Failed to add pattern {pattern_ids[i]}: {str(e2)}")
    
    except Exception as e:
        logger.error(f"Error embedding code: {str(e)}")
    
    return {
        "functions": functions,
        "headers": header_chunks,
        "code_patterns": code_patterns,
        "message": f"Successfully embedded {len(functions)} functions and {len(code_patterns)} code patterns from {file_path}"
    }