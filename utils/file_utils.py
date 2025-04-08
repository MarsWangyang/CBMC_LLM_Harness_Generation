"""
File handling utilities for the CBMC harness generator.
"""
import os
import glob
import shutil
import logging
import datetime
import fnmatch

logger = logging.getLogger("file_utils")

def process_directory(directory_path: str) -> dict:
    """
    Process all C source files in the given directory and all its subdirectories.
    
    Args:
        directory_path: Path to the directory containing C source files
        
    Returns:
        Dictionary mapping file paths to their content
    """
    source_files = {}
    
    # Check if the directory exists
    if not os.path.isdir(directory_path):
        logger.error(f"Directory '{directory_path}' does not exist")
        return source_files
    
    # Look for source subdirectory
    source_subdir = os.path.join(directory_path, "source")
    if not os.path.isdir(source_subdir):
        logger.warning(f"'{source_subdir}' directory not found. Using top directory.")
        source_subdir = directory_path
    
    logger.info(f"Looking for source files in: {source_subdir}")
    
    # Find all C source files in the source directory and all subdirectories
    c_file_patterns = ['*.c', '*.h', '*.cpp', '*.hpp']
    
    # Process all subdirectories recursively
    for root, dirs, files in os.walk(source_subdir):
        for pattern in c_file_patterns:
            for filename in fnmatch.filter(files, pattern):
                file_path = os.path.join(root, filename)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        if not content:
                            print(f"Warning: Empty file: {file_path}")
                        source_files[file_path] = content
                        print(f"Processed file: {file_path} ({len(content)} bytes)")
                except UnicodeDecodeError:
                    # Try with a different encoding if UTF-8 fails
                    try:
                        with open(file_path, 'r', encoding='latin-1') as f:
                            content = f.read()
                            source_files[file_path] = content
                            print(f"Processed file with latin-1 encoding: {file_path} ({len(content)} bytes)")
                    except Exception as e:
                        print(f"Error reading file {file_path}: {str(e)}")
                except Exception as e:
                    print(f"Error reading file {file_path}: {str(e)}")
    
    # Add statistics about found files
    print(f"Found {len(source_files)} source files in total")
    extension_counts = {}
    for file_path in source_files:
        ext = os.path.splitext(file_path)[1]
        extension_counts[ext] = extension_counts.get(ext, 0) + 1
    
    for ext, count in extension_counts.items():
        print(f"  {ext}: {count} files")
    
    return source_files

def calculate_recursion_limit(num_files):
    """Calculate a safe recursion limit based on estimated complexity."""
    # Estimate number of functions based on number of files
    # On average, a C file might have 5-10 functions
    estimated_functions_per_file = 20
    estimated_functions = num_files * estimated_functions_per_file
    
    # Default max refinements per function
    max_refinements = 9
    
    # Base recursion limit
    base_limit = 20
    
    # Calculate limit based on estimated functions and refinements
    # Formula: base + (estimated_functions * (refinements + 1) * nodes_per_function_cycle)
    nodes_per_function_cycle = 4  # junction, generator, cbmc, evaluator
    function_recursion = estimated_functions * (max_refinements + 1) * nodes_per_function_cycle
    
    # Add safety buffer - minimum 100, scales with function count
    safe_limit = max(100, base_limit + function_recursion)
    
    print(f"Set recursion limit to {safe_limit} (estimated {estimated_functions} functions from {num_files} files)")
    
    return safe_limit

def setup_verification_directories(llm_used="claude"):
    """
    Set up the directory structure for verification with model and timestamp.
    
    Args:
        llm_used: The LLM model being used (claude, openai, or gemini)
        
    Returns:
        dict: Dictionary containing the paths to the created directories
    """
    # Create timestamp for the run
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    
    # Create base result directory
    result_base = os.path.join("results", llm_used, timestamp)
    
    # Create the directory structure
    directories = {
        "result_base": result_base,
        "harnesses": os.path.join(result_base, "harnesses"),
        "verification": os.path.join(result_base, "verification"),
        "reports": os.path.join(result_base, "reports")
    }
    
    # Create all directories
    for directory in directories.values():
        os.makedirs(directory, exist_ok=True)
        
    logger.info(f"Created result directories in {result_base}")
    
    return directories