"""
File handling utilities for the CBMC harness generator.
"""
import os
import glob
import shutil

def process_directory(directory_path: str) -> dict:
    """
    Process all C source files in the source/source_code subdirectory of the given directory.
    
    Args:
        directory_path: Path to the directory containing C source files
        
    Returns:
        Dictionary mapping file paths to their content
    """
    source_files = {}
    
    # Check if the directory exists
    if not os.path.isdir(directory_path):
        print(f"Error: Directory '{directory_path}' does not exist")
        return source_files
    
    # Look for source/source_code subdirectory
    source_subdir = os.path.join(directory_path, "source")
    if not os.path.isdir(source_subdir):
        print(f"Warning: '{source_subdir}' directory not found. Using top directory.")
        source_subdir = directory_path
    
    print(f"Looking for source files in: {source_subdir}")
    
    # Find all C source files in the source subdirectory
    c_file_patterns = ['*.c', '*.h', '*.cpp', '*.hpp']
    for pattern in c_file_patterns:
        file_paths = glob.glob(os.path.join(source_subdir, "**", pattern), recursive=True)
        for file_path in file_paths:
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
    
    return source_files

def calculate_recursion_limit(num_files):
    """Calculate a safe recursion limit based on estimated complexity."""
    # Estimate number of functions based on number of files
    # On average, a C file might have 5-10 functions
    estimated_functions_per_file = 10
    estimated_functions = num_files * estimated_functions_per_file
    
    # Default max refinements per function
    max_refinements = 3
    
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

def setup_verification_directories():
    """
    Set up the directory structure for verification.
    """
    # Create organized directory structure
    directories = [
        "harnesses",
        "verification",
        "verification/src",
        "verification/include",
        "verification/stubs",
        "verification/sources",
        "reports"
    ]
    
    for directory in directories:
        os.makedirs(directory, exist_ok=True)
    
    return directories