"""
Code parsing utilities for the CBMC harness generator.
"""
import os
import re
from tqdm import tqdm
from core.embedding_db import code_collection

def embed_code(code: str, file_path: str = None) -> dict:
    """Embeds source code and stores it in the ChromaDB embedding database."""
    # Parse the code to extract functions
    functions = {}
    
    # Skip if code is empty
    if not code:
        return {"functions": {}, "message": "No code to embed"}
    
    # Clear existing collection first - only do this once at the start, not for each file
    if file_path and "core_http_client.c" in file_path:  # Only clear on first file
        try:
            existing_ids = code_collection.get()["ids"]
            if existing_ids:
                code_collection.delete(ids=existing_ids)
        except Exception as e:
            pass
    
    # Show file info
    file_name = os.path.basename(file_path) if file_path else "inline"
    
    try:
        # Use a simpler function pattern that's more reliable
        c_func_pattern = r"([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)\s*\{"
        
        # Use direct search instead of splitting first
        matches = list(re.finditer(c_func_pattern, code, re.MULTILINE))
        
        # Process each potential function with progress bar
        function_ids = []
        function_texts = []
        function_metadatas = []
        
        # Keep a set of function names to avoid duplicates
        seen_functions = set()
        
        # Skip header files for faster processing
        if file_path and file_path.endswith(('.h', '.hpp')):
            # Handle header files with a different approach
            header_pattern = r"([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)\s*;"
            header_matches = re.finditer(header_pattern, code)
            for match in header_matches:
                func_name = match.group(2).strip()
                # Skip if func_name is a keyword
                if func_name in ['if', 'for', 'while', 'switch', 'return', 'include']:
                    continue
                # Create a function ID
                func_id = func_name
                if file_path:
                    file_basename = os.path.basename(file_path)
                    func_id = f"{file_basename}:{func_name}"
                functions[func_id] = {
                    "return_type": match.group(1).strip(),
                    "params": match.group(3).strip(),
                    "body": "",  # No body for header declarations
                    "full_text": match.group(0),
                    "file_path": file_path,
                    "original_name": func_name
                }
            return {"functions": functions, "message": "Processed header file declarations"}
        
        # Use tqdm for progress tracking
        with tqdm(total=len(matches), desc=f"Analyzing {file_name}", unit="funcs") as pbar:
            for match in matches:
                try:
                    return_type = match.group(1).strip()
                    func_name = match.group(2).strip()
                    params = match.group(3).strip()
                    
                    # Update progress bar
                    pbar.set_description(f"Analyzing {func_name}")
                    
                    # Skip if func_name is a keyword
                    if func_name in ['if', 'for', 'while', 'switch', 'return', 'include']:
                        pbar.update(1)
                        continue
                    
                    # Skip if we've already seen this function
                    if func_name in seen_functions:
                        pbar.update(1)
                        continue
                    
                    # Find function body
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
                        pbar.update(1)
                        continue
                    
                    # If we couldn't find the end, set a max size
                    if brace_count > 0:
                        end_pos = min(start_pos + 10000, len(code))
                    
                    # Extract body including braces
                    body = code[start_pos-1:end_pos]
                    
                    # Create function ID with file info if provided
                    func_id = func_name
                    if file_path:
                        file_basename = os.path.basename(file_path)
                        func_id = f"{file_basename}:{func_name}"
                    
                    # Get full function text
                    full_text = f"{return_type} {func_name}({params}) {body}"
                    
                    # Store in our result structures
                    seen_functions.add(func_name)
                    functions[func_id] = {
                        "return_type": return_type,
                        "params": params,
                        "body": body,
                        "full_text": full_text,
                        "file_path": file_path,
                        "original_name": func_name,
                        "has_malloc": "malloc(" in body,
                        "has_free": "free(" in body
                    }
                    
                    # Add to arrays for ChromaDB
                    function_ids.append(func_id)
                    function_texts.append(full_text)
                    function_metadatas.append({
                        "name": func_name,
                        "id": func_id,
                        "return_type": return_type,
                        "params": params,
                        "has_malloc": "malloc(" in body,
                        "has_free": "free(" in body,
                        "allocation_without_free": "malloc(" in body and "free(" not in body,
                        "file_path": file_path if file_path else "inline"
                    })
                    
                    # Update progress bar with function count
                    pbar.set_postfix(functions=len(functions))
                except Exception:
                    pass
                
                pbar.update(1)
        
        # Add to ChromaDB
        if function_ids:
            code_collection.add(
                ids=function_ids,
                documents=function_texts,
                metadatas=function_metadatas
            )
    
    except Exception as e:
        pass
    
    return {
        "functions": functions,
        "message": f"Successfully embedded {len(functions)} functions from {file_path}"
    }