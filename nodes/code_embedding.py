"""
Code embedding node for CBMC harness generator workflow.
"""
import os
from langchain_core.messages import AIMessage
from utils.code_parser import embed_code
import logging

logger = logging.getLogger("code_embedding")

def code_embedding_node(state):
    """Embeds and stores code in the database."""

    logger.info("Starting code embedding process")
    
    # Check if we're in directory mode
    if state.get("is_directory_mode", False):
        source_files = state.get("source_files", {})
        
        # Process each file separately and combine the results
        all_embeddings = {"functions": {}, "headers": {}, "available_headers": []}
        file_counts = {}
        
        # Process C source files first, then headers, finally CBMC test files
        c_files = {}
        h_files = {}
        cbmc_files = {}
        
        for file_path, file_content in source_files.items():
            if "test/cbmc" in file_path:
                cbmc_files[file_path] = file_content
            elif file_path.endswith(('.h', '.hpp')):
                h_files[file_path] = file_content
            elif file_path.endswith(('.c', '.cpp')):
                c_files[file_path] = file_content
        
        # Process header files first to build the header database
        print(f"Processing {len(h_files)} header files...")
        for file_path, file_content in h_files.items():
            print(f"Embedding header file: {os.path.basename(file_path)}")
            file_result = embed_code(file_content, file_path)
            all_embeddings["headers"].update(file_result.get("headers", {}))
            all_embeddings["functions"].update(file_result.get("functions", {}))
            # Add to available headers list
            all_embeddings["available_headers"].append(os.path.basename(file_path))
            file_counts[file_path] = len(file_result.get("functions", {}))
            print(f"Found {file_counts[file_path]} declarations in {os.path.basename(file_path)}")
        
        # Process C files next for implementations
        logger.info(f"Processing {len(c_files)} C source files for embedding")
        for file_path, file_content in c_files.items():
            print(f"Embedding file: {os.path.basename(file_path)}")
            file_result = embed_code(file_content, file_path)
            all_embeddings["functions"].update(file_result.get("functions", {}))
            file_counts[file_path] = len(file_result.get("functions", {}))
            print(f"Found {file_counts[file_path]} functions in {os.path.basename(file_path)}")

        # Special handling for CBMC test files - highest priority
        if cbmc_files:
            print(f"Processing {len(cbmc_files)} CBMC test files for embedding")
            for file_path, file_content in cbmc_files.items():
                print(f"Embedding CBMC file: {os.path.basename(file_path)}")
                file_result = embed_code(file_content, file_path)
                # Add all CBMC functions, even if they would override others
                # Since CBMC verification uses these specifically
                all_embeddings["functions"].update(file_result.get("functions", {}))
                if file_path.endswith(('.h', '.hpp')):
                    all_embeddings["headers"].update(file_result.get("headers", {}))
                    all_embeddings["available_headers"].append(os.path.basename(file_path))
                file_counts[file_path] = len(file_result.get("functions", {}))
                print(f"Found {file_counts[file_path]} test functions in {os.path.basename(file_path)}")
        
        # Create a summary of files processed
        file_summary = "\n".join([f"- {path}: {count} functions" for path, count in file_counts.items() if count > 0])
        header_summary = "\n".join([f"- {h}" for h in all_embeddings["available_headers"]])
        
        return {
            "messages": [AIMessage(content=f"Source code embedded successfully across multiple files.\n\nSummary:\n{file_summary}\n\nAvailable Headers:\n{header_summary}\n\nTotal functions found: {len(all_embeddings['functions'])}")],
            "embeddings": all_embeddings
        }
    else:
        # Original single file processing
        result = embed_code(state.get("source_code", ""))
        
        return {
            "messages": [AIMessage(content=f"Source code embedded successfully. Found {len(result['functions'])} functions.")],
            "embeddings": result
        }