"""
Frontend node for CBMC harness generator workflow.
"""
import os
import re
import time
from langchain_core.messages import AIMessage, HumanMessage
from utils.file_utils import process_directory
import logging

logger = logging.getLogger("frontend")

def frontend_node(state):
    """Extracts source code from user messages and initializes timing."""
    # Start timing the overall process
    start_time = time.time()

    logger.info("Processing incoming source code request")
    
    # Check if the user specified a directory path
    directory_path = None
    multiple_files = {}
    
    for message in reversed(state["messages"]):
        if isinstance(message, HumanMessage) and "directory:" in message.content.lower():
            # Extract directory path using regex
            dir_match = re.search(r'directory:\s*([^\s]+)', message.content, re.IGNORECASE)
            if dir_match:
                directory_path = dir_match.group(1)
                print(f"Directory path detected: {directory_path}")
                multiple_files = process_directory(directory_path)
                
                # Add CBMC test files to embedding
                cbmc_dirs = [
                    os.path.join(directory_path, "test", "cbmc", "include"),
                    os.path.join(directory_path, "test", "cbmc", "stubs"),
                    os.path.join(directory_path, "test", "cbmc", "sources")
                ]

                # Look one level up if not found
                if not any(os.path.exists(d) for d in cbmc_dirs):
                    cbmc_dirs = [
                        os.path.join(os.path.dirname(directory_path), "test", "cbmc", "include"),
                        os.path.join(os.path.dirname(directory_path), "test", "cbmc", "stubs"),
                        os.path.join(os.path.dirname(directory_path), "test", "cbmc", "sources")
                    ]

                # Process CBMC files
                for cbmc_dir in cbmc_dirs:
                    if os.path.exists(cbmc_dir):
                        print(f"Adding CBMC test files from {cbmc_dir}")
                        cbmc_files = process_directory(cbmc_dir)
                        # Add to our source files dictionary
                        multiple_files.update(cbmc_files)
                
                if multiple_files:
                    # Determine source subdirectory for reporting
                    source_subdir = os.path.join(directory_path, "source")
                    if not os.path.isdir(source_subdir):
                        source_subdir = directory_path
                    
                    # Initialize file_functions dictionary to track functions per file
                    file_functions = {}
                    
                    # Create a combined source for backward compatibility
                    combined_source = ""
                    for file_path, content in multiple_files.items():
                        combined_source += f"/* File: {file_path} */\n{content}\n\n"
                        file_functions[file_path] = []  # Initialize empty function list for each file
                    
                    logger.info(f"Found {len(multiple_files)} C source files in {directory_path}")
                    print(f"Combined source code length: {len(combined_source)} bytes")
                    
                    return {
                        "messages": [AIMessage(content=f"Processing directory: {directory_path}. Found {len(multiple_files)} C source files in source code directory.")],
                        "source_files": multiple_files,
                        "source_code": combined_source,  # For backward compatibility
                        "start_time": start_time,
                        "is_directory_mode": True,
                        "source_directory": source_subdir,
                        "file_functions": file_functions  # Initialize tracking of functions per file
                    }
                else:
                    logger.warning(f"No C source files found in {directory_path}")
                    return {
                        "messages": [AIMessage(content=f"No C source files found in source directory of: {directory_path}")],
                        "source_code": "",
                        "source_files": {},
                        "start_time": start_time,
                        "is_directory_mode": False,
                        "file_functions": {}
                    }
    
    # Fall back to the original single file processing if no directory is specified
    if not state.get("source_code"):
        for message in reversed(state["messages"]):
            if isinstance(message, HumanMessage) and "```" in message.content:
                match = re.search(r'```(?:\w+)?\n(.+?)\n```', message.content, re.DOTALL)
                if match:
                    source_code = match.group(1)
                    return {
                        "messages": [AIMessage(content=f"Received source code ({len(source_code)} characters). Proceeding with code embedding.")],
                        "source_code": source_code,
                        "source_files": {"inline_code": source_code},  # Add to source_files for consistency
                        "start_time": start_time,
                        "is_directory_mode": False,
                        "file_functions": {"inline_code": []}  # Initialize tracking for single file
                    }
    
    # If no source code found or already exists
    return {
        "messages": [AIMessage(content=f"Proceeding with code embedding.")],
        "source_code": state.get("source_code", ""),
        "source_files": state.get("source_files", {}),
        "start_time": start_time,
        "is_directory_mode": state.get("is_directory_mode", False),
        "file_functions": state.get("file_functions", {})
    }