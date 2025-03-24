"""
Code embedding node for CBMC harness generator workflow.
"""
import os
from langchain_core.messages import AIMessage
from utils.code_parser import embed_code

def code_embedding_node(state):
    """Embeds and stores code in the database."""
    
    # Check if we're in directory mode
    if state.get("is_directory_mode", False):
        source_files = state.get("source_files", {})
        
        # Process each file separately and combine the results
        all_embeddings = {"functions": {}}
        file_counts = {}
        
        # Process C source files first, then headers
        c_files = {}
        h_files = {}
        
        for file_path, file_content in source_files.items():
            if file_path.endswith(('.c', '.cpp')):
                c_files[file_path] = file_content
            else:
                h_files[file_path] = file_content
        
        # Process C files first (implementations)
        print(f"Processing {len(c_files)} C source files...")
        for file_path, file_content in c_files.items():
            print(f"Embedding file: {os.path.basename(file_path)}")
            file_result = embed_code(file_content, file_path)
            all_embeddings["functions"].update(file_result.get("functions", {}))
            file_counts[file_path] = len(file_result.get("functions", {}))
            print(f"Found {file_counts[file_path]} functions in {os.path.basename(file_path)}")
        
        # Process header files 
        print(f"Processing {len(h_files)} header files...")
        for file_path, file_content in h_files.items():
            print(f"Embedding file: {os.path.basename(file_path)}")
            file_result = embed_code(file_content, file_path)
            # Only add functions that haven't been found in C files
            new_funcs = 0
            for func_id, func_data in file_result.get("functions", {}).items():
                if func_id not in all_embeddings["functions"]:
                    all_embeddings["functions"][func_id] = func_data
                    new_funcs += 1
            file_counts[file_path] = new_funcs
            print(f"Found {new_funcs} new functions in {os.path.basename(file_path)}")
        
        # Create a summary of files processed
        file_summary = "\n".join([f"- {path}: {count} functions" for path, count in file_counts.items() if count > 0])
        
        return {
            "messages": [AIMessage(content=f"Source code embedded successfully across multiple files.\n\nSummary:\n{file_summary}\n\nTotal functions found: {len(all_embeddings['functions'])}")],
            "embeddings": all_embeddings
        }
    else:
        # Original single file processing
        result = embed_code(state.get("source_code", ""))
        
        return {
            "messages": [AIMessage(content=f"Source code embedded successfully. Found {len(result['functions'])} functions.")],
            "embeddings": result
        }