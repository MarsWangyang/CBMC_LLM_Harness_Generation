"""
CBMC execution node for harness generator workflow with optimized file selection.
"""
import os
import time
import shutil
import subprocess
import glob
import json
from langchain_core.messages import AIMessage
import logging
from utils.cbmc_parser import process_cbmc_output

logger = logging.getLogger("cbmc")

# Define CBMC_MAX_OBJECT_SIZE
cbmc_max_object_size = 1024 * 1024  # 1MB is a typical reasonable size

def get_minimal_verification_files(func_name, rag_db, verification_include_dir):
    """
    Get minimal set of files needed for verification based on function dependencies.
    
    Args:
        func_name: Name of the function being verified
        rag_db: The RAG database instance
        verification_include_dir: Directory with include files
        
    Returns:
        List of file paths to include in verification
    """
    # Get function metadata from RAG
    function_data = rag_db.get_code_function(func_name)
    if not function_data:
        logger.warning(f"No function data found for {func_name} in RAG database")
        return []
        
    # Get original source files for dependencies
    required_files = set()
    
    # Get original file for the function
    orig_file = None
    if "metadata" in function_data and "file_path" in function_data["metadata"]:
        orig_file = os.path.basename(function_data["metadata"]["file_path"])
        required_files.add(orig_file)
        logger.info(f"Required original file: {orig_file}")
    
    # Get files for dependencies
    try:
        if "metadata" in function_data and "function_calls" in function_data["metadata"]:
            function_calls_json = function_data["metadata"].get("function_calls", "[]")
            
            # Handle both string and list formats
            if isinstance(function_calls_json, str):
                try:
                    function_calls = json.loads(function_calls_json)
                except json.JSONDecodeError:
                    function_calls = [call.strip() for call in function_calls_json.split(',')]
            else:
                function_calls = function_calls_json
            
            logger.info(f"Function calls for {func_name}: {function_calls}")
            
            for call in function_calls:
                # Skip common library functions and keywords
                if call in ["if", "for", "while", "switch", "return", "malloc", "free",
                            "memset", "memcpy", "printf", "fprintf", "sprintf"]:
                    continue
                    
                call_data = rag_db.get_code_function(call)
                if call_data and "metadata" in call_data and "file_path" in call_data["metadata"]:
                    dep_file = os.path.basename(call_data["metadata"]["file_path"])
                    required_files.add(dep_file)
                    logger.info(f"Added dependency file: {dep_file} for function call {call}")
    except Exception as e:
        logger.error(f"Error processing function calls: {str(e)}")
    
    # Find corresponding files in verification directories
    verification_files = []
    
    # Check both include and project source directories
    for search_dir in [verification_include_dir]:
        if not os.path.exists(search_dir):
            continue
            
        for file in os.listdir(search_dir):
            # Only consider C source files
            if not file.endswith(('.c', '.h', '.cpp', '.hpp')):
                continue
                
            # Check if this file matches any required file (by basename)
            if file in required_files:
                full_path = os.path.join(search_dir, file)
                verification_files.append(full_path)
                logger.info(f"Added verification file: {full_path}")
    
    # If no files found, return empty list
    if not verification_files:
        logger.warning(f"No verification files found for {func_name} with dependencies: {required_files}")
        return []
    
    return verification_files

def cbmc_node(state):
    """Executes CBMC verification on the current function's harness using optimized file selection."""
    verification_start = time.time()
    
    func_name = state.get("current_function", "")
    harnesses = state.get("harnesses", {})
    harness_code = harnesses.get(func_name, "")

    logger.info(f"Starting CBMC verification for function {func_name}")
    
    # Get result directories from state
    result_directories = state.get("result_directories", {})
    verification_base_dir = result_directories.get("verification_dir", "verification")
    harnesses_dir = result_directories.get("harnesses_dir", "harnesses")
    
    if not harness_code:
        logger.error(f"No harness available for function {func_name}")
        return {
            "messages": [AIMessage(content=f"Error: No harness available for function {func_name}.")],
            "next": "junction"  # Return to junction to process next function
        }
    
    # Extract file path from function name if it includes file info
    file_basename = None
    original_func_name = func_name
    
    if ":" in func_name:
        file_basename, original_func_name = func_name.split(":", 1)
    
    # Create function-specific directory
    func_verification_dir = os.path.join(verification_base_dir, func_name)
    os.makedirs(func_verification_dir, exist_ok=True)
    
    # Create proper directory structure for verification
    verification_harness_dir = os.path.join(verification_base_dir, "harness_files")
    verification_include_dir = os.path.join(verification_base_dir, "includes")
    os.makedirs(verification_harness_dir, exist_ok=True)
    os.makedirs(verification_include_dir, exist_ok=True)
    
    # Create a separate directory for project source files
    verification_project_src_dir = os.path.join(verification_base_dir, "project_src")
    os.makedirs(verification_project_src_dir, exist_ok=True)
    
    # Determine version number from refinement attempts
    refinement_num = state.get("refinement_attempts", {}).get(func_name, 0)
    version_num = refinement_num + 1
    
    # Create CBMC definitions header if it doesn't exist
    cbmc_defs_header = os.path.join(verification_include_dir, "cbmc_defs.h")
    if not os.path.exists(cbmc_defs_header):
        with open(cbmc_defs_header, "w") as f:
            f.write("""/*
 * Auto-generated CBMC definitions header
 * This file provides definitions needed for CBMC verification
 */

#ifndef CBMC_DEFS_H
#define CBMC_DEFS_H

#include <stddef.h>
#include <limits.h>

/* CBMC object size constraints */
#ifndef CBMC_OBJECT_BITS
#define CBMC_OBJECT_BITS 8
#endif

#ifndef CBMC_MAX_OBJECT_SIZE
#define CBMC_MAX_OBJECT_SIZE (SIZE_MAX>>(CBMC_OBJECT_BITS+1))
#endif

#endif /* CBMC_DEFS_H */
""")
    
    # For directory mode, handle project file copying
    if state.get("is_directory_mode", False):
        # Get original source directory from state
        original_source_dir = state.get("source_directory", "")
        
        # Get directory path, removing "/source" if present
        directory_path = original_source_dir.replace("/source", "") if "/source" in original_source_dir else original_source_dir
        
        # Predefined paths for CBMC test files
        test_cbmc_paths = [
            os.path.join(directory_path, "test", "cbmc", "include"),
            os.path.join(directory_path, "test", "cbmc", "sources"),
            os.path.join(directory_path, "test", "cbmc", "stubs")
        ]
        
        # Find the specific source file for this function from embeddings
        embeddings = state.get("embeddings", {})
        functions = embeddings.get("functions", {})
        
        if func_name in functions and "file_path" in functions[func_name]:
            file_path = functions[func_name]["file_path"]
            if file_path and os.path.exists(file_path):
                # Copy to the project source directory
                dest_file = os.path.join(verification_project_src_dir, os.path.basename(file_path))
                shutil.copy2(file_path, dest_file)
                print(f"Copied main source file: {file_path} → {dest_file}")
        
        # Copy necessary headers to include directory, prioritizing source and CBMC directories
        header_paths = []
        if original_source_dir and os.path.exists(original_source_dir):
            header_paths.append(original_source_dir)
        
        # Add all CBMC test include paths that exist
        for path in test_cbmc_paths:
            if os.path.exists(path):
                header_paths.append(path)
                print(f"Found CBMC test directory: {path}")
        
        # Copy headers from all found paths
        for src_dir in header_paths:
            for root, dirs, files in os.walk(src_dir):
                for file in files:
                    # Copy headers and important source files to include directory
                    if file.endswith(('.h', '.hpp', '.c', '.cbmc')):
                        src_file = os.path.join(root, file)
                        dest_file = os.path.join(verification_include_dir, file)
                        
                        # Avoid overwriting
                        if not os.path.exists(dest_file):
                            shutil.copy2(src_file, dest_file)
                            print(f"Copied test/verification file: {file}")
        
        # Additional CBMC-specific copies for known utility files
        cbmc_utility_files = ['assert.h', 'nondet.h', 'proof_api.h']
        for util_file in cbmc_utility_files:
            for path in test_cbmc_paths:
                potential_file = os.path.join(path, util_file)
                if os.path.exists(potential_file):
                    dest_file = os.path.join(verification_include_dir, util_file)
                    shutil.copy2(potential_file, dest_file)
                    print(f"Copied CBMC utility file: {util_file}")
    
    # Write harness to file
    harness_filename = original_func_name if ":" not in func_name else original_func_name
    harness_file = os.path.join(verification_harness_dir, f"{harness_filename}_harness.c")
    with open(harness_file, "w") as f:
        # Add include for the CBMC definitions header
        f.write("#include \"cbmc_defs.h\"\n\n")
        f.write(harness_code)
    
    # Build CBMC command parameters
    cbmc_cmd = [
        "cbmc",
        "--function", "main",  # Use main as the entry point in generated harnesses
        "--object-bits", "8",
        "-DCBMC_MAX_OBJECT_SIZE=" + str(cbmc_max_object_size)
    ]

    # Add the harness file first
    cbmc_cmd.append(harness_file)

    # Add all C files from verification/includes directory
    c_files_in_includes = glob.glob(os.path.join(verification_include_dir, "*.c"))
    cbmc_cmd.extend(c_files_in_includes)

    # Get the unified RAG database
    from utils.rag import get_unified_db
    rag_db = get_unified_db(os.path.join(result_directories.get("result_base_dir", "results"), "rag_data"))

    # OPTIMIZATION: Add any targeted dependency files based on function dependencies
    verification_files = get_minimal_verification_files(
        func_name, 
        rag_db, 
        verification_include_dir
    )

    # Add these files if they're not already included
    for file in verification_files:
        if file not in c_files_in_includes:
            cbmc_cmd.append(file)

    # Add verification flags
    cbmc_cmd.extend([
        # Performance optimizations
        "--slice-formula",  # Add formula slicing to reduce complexity
        "--no-unwinding-assertions",
        "--partial-loops",  # Use partial loops to reduce the state space
        "--unwind", "1",  # Limit unwinding to 1 to speed up verification (can be adjusted)
        "--no-assertions",
        # Targeted verification flags - focus on essential properties
        "--memory-leak-check",
        "--div-by-zero-check",
        "--pointer-overflow-check",
    ])

    # Add necessary include paths with additional check for CBMC test files
    # Important to add all the -I options at the end
    include_paths = [verification_include_dir]

    # Add include paths to CBMC command, ensuring they exist
    for path in include_paths:
        if os.path.exists(path):
            cbmc_cmd.extend(["-I", path])
    
    # Save the command for debugging
    cmd_file = os.path.join(func_verification_dir, f"v{version_num}_command.txt")
    with open(cmd_file, "w") as f:
        f.write(" ".join(cbmc_cmd))
    
    # Create a separate command for coverage with compatible flags
    coverage_cmd = cbmc_cmd.copy()
    coverage_cmd.extend([
        "--cover", "location",
        "--json-ui"  # Using XML format for consistent parsing
    ])
    
    # Initialize result variables
    cbmc_stdout = ""
    cbmc_stderr = ""
    cbmc_returncode = 0
    cbmc_results = state.get("cbmc_results", {}).copy()
    
    refinement_num = state.get("refinement_attempts", {}).get(func_name, 0)
    # UPDATED: Set timeout based on refinement number with new formula
    timeout_seconds = 90 + (refinement_num * 10)
    
    try:
        # Run the verification with adjusted timeout
        logger.info(f"Running CBMC verification for {func_name} with timeout {timeout_seconds}s")
        property_process = subprocess.run(
            cbmc_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout_seconds,
            check=False
        )
        
        cbmc_stdout = property_process.stdout
        cbmc_stderr = property_process.stderr
        cbmc_returncode = property_process.returncode
        
        # Save raw output immediately
        raw_output_file = os.path.join(func_verification_dir, f"v{version_num}_raw_output.txt")
        with open(raw_output_file, "w") as f:
            f.write("=== STDOUT ===\n")
            f.write(cbmc_stdout)
            f.write("\n\n=== STDERR ===\n")
            f.write(cbmc_stderr)
        
        # Run coverage checking separately with JSON output
        try:
            logger.info(f"Running coverage checking for {func_name}")
            coverage_process = subprocess.run(
                coverage_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=30,  # Shorter timeout for coverage
                check=False
            )
            
            coverage_stdout = coverage_process.stdout
            
            # Save JSON coverage output to a file
            coverage_json_file = os.path.join(func_verification_dir, f"v{version_num}_coverage.json")
            with open(coverage_json_file, "w") as f:
                f.write(coverage_stdout)
            
            # Parse the JSON coverage data
            try:
                import json
                json_data = json.loads(coverage_stdout)
                
                # Extract coverage metrics from the JSON data
                from utils.cbmc_parser import extract_coverage_metrics
                # Use the already defined cbmc_result variable (from earlier in the function)
                coverage_metrics = extract_coverage_metrics(json_data, func_name)
                
                # Add coverage metrics to cbmc_result
                for key, value in coverage_metrics.items():
                    cbmc_result[key] = value
                
            except json.JSONDecodeError as e:
                logger.error(f"Error parsing JSON coverage data: {str(e)}")
            except Exception as e:
                logger.error(f"Error processing coverage data: {str(e)}")
            
        except subprocess.TimeoutExpired:
            logger.warning(f"Coverage check timed out for {func_name}")
        except Exception as e:
            logger.error(f"Error running coverage check: {str(e)}")
        
        # Process CBMC output using our new parser
        cbmc_result = process_cbmc_output(cbmc_stdout, cbmc_stderr)
        
        # Create a structured result for the state
        cbmc_results[func_name] = {
            "function": func_name,
            "status": cbmc_result["verification_status"],
            "message": cbmc_result["message"],
            "suggestions": cbmc_result["suggestions"],
            "stdout": cbmc_stdout,
            "stderr": cbmc_stderr,
            "returncode": cbmc_returncode,
            "version": version_num,
            "error_categories": cbmc_result["error_categories"],
            "missing_functions": list(cbmc_result["missing_functions"]),
            "verification_failures": cbmc_result["verification_failures"],
            "error_locations": cbmc_result["error_locations"],
            "dependency_files_used": len(verification_files),
            # Add function-specific metrics
            "func_reachable_lines": cbmc_result["func_reachable_lines"],
            "func_covered_lines": cbmc_result["func_covered_lines"],
            "func_coverage_pct": cbmc_result["func_coverage_pct"]
        }
        
        # Save verification results to a structured file
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: {cbmc_result['verification_status']}\n")
            f.write(f"Message: {cbmc_result['message']}\n")
            if cbmc_result["suggestions"]:
                f.write(f"Suggestions: {cbmc_result['suggestions']}\n")
            
            f.write(f"\nDependency files used: {len(verification_files)}\n")
            
            f.write("\n=== PROOF METRICS ===\n")
            f.write(f"Reachable lines: {cbmc_result['reachable_lines']}\n")
            f.write(f"Covered lines: {cbmc_result['covered_lines']}\n")
            f.write(f"Coverage: {cbmc_result['coverage_pct']:.2f}%\n")
            f.write(f"Errors: {cbmc_result['errors']}\n")
            
            # Add function-specific metrics
            f.write("\n=== FUNCTION-SPECIFIC METRICS ===\n")
            f.write(f"Function reachable lines: {cbmc_result['func_reachable_lines']}\n")
            f.write(f"Function covered lines: {cbmc_result['func_covered_lines']}\n")
            f.write(f"Function coverage: {cbmc_result['func_coverage_pct']:.2f}%\n")
            
            if cbmc_result["error_categories"]:
                f.write("\n=== ERROR CATEGORIES ===\n")
                for category in cbmc_result["error_categories"]:
                    f.write(f"- {category}\n")
            
            if cbmc_result["missing_functions"]:
                f.write("\n=== MISSING FUNCTIONS ===\n")
                for func in cbmc_result["missing_functions"]:
                    f.write(f"- {func}\n")
            
            f.write("\n=== STDOUT ===\n")
            f.write(cbmc_stdout)
            f.write("\n\n=== STDERR ===\n")
            f.write(cbmc_stderr)
        
        # Generate a more helpful report in markdown format
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** {cbmc_result['verification_status']}\n\n")
            f.write(f"**Message:** {cbmc_result['message']}\n\n")
            if cbmc_result["suggestions"]:
                f.write(f"**Suggestions:** {cbmc_result['suggestions']}\n\n")
            
            # Add dependency information
            f.write(f"**Dependency Files Used:** {len(verification_files)}\n\n")
            if verification_files:
                f.write("**Files included:**\n\n")
                for file_path in verification_files:
                    f.write(f"- {os.path.basename(file_path)}\n")
                f.write("\n")
            
            # Add Proof Metrics section
            f.write(f"## Proof Metrics\n\n")
            f.write(f"| Metric | Value |\n")
            f.write(f"|--------|-------|\n")
            f.write(f"| Reachable lines | {cbmc_result['reachable_lines']} |\n")
            f.write(f"| Covered lines | {cbmc_result['covered_lines']} |\n")
            f.write(f"| Coverage | {cbmc_result['coverage_pct']:.2f}% |\n")
            f.write(f"| Errors | {cbmc_result['errors']} |\n\n")
            
            # Add Enhanced Function-Specific Metrics section
            f.write(f"## Enhanced Function-Specific Metrics\n\n")
            f.write(f"| Metric | Value |\n")
            f.write(f"|--------|-------|\n")
            f.write(f"| Function reachable lines | {cbmc_result['func_reachable_lines']} |\n")
            f.write(f"| Function covered lines | {cbmc_result['func_covered_lines']} |\n")
            f.write(f"| Function coverage | {cbmc_result['func_coverage_pct']:.2f}% |\n")
            f.write(f"| Reported errors | {cbmc_result['errors']} |\n\n")
            
            # Add error details if any
            if cbmc_result["error_categories"]:
                f.write(f"## Error Categories\n\n")
                for category in cbmc_result["error_categories"]:
                    f.write(f"- {category}\n")
                f.write("\n")
            
            # Add error locations if any
            if cbmc_result["error_locations"]:
                f.write(f"## Error Locations\n\n")
                for file, lines in cbmc_result["error_locations"].items():
                    f.write(f"**File:** {file}\n\n")
                    f.write(f"Error lines: {', '.join(map(str, sorted(lines)))}\n\n")
            
            # Add missing functions if any
            if cbmc_result["missing_functions"]:
                f.write(f"## Missing Functions\n\n")
                for func in cbmc_result["missing_functions"]:
                    f.write(f"- {func}\n")
                f.write("\n")
            
            # Add harness details
            harness_path = os.path.join(harnesses_dir, func_name, f"v{version_num}.c")
            f.write(f"## Harness Details\n\n")
            f.write(f"The harness file is located at: `{harness_path}`\n\n")
            
            f.write(f"## Verification Command\n\n")
            f.write(f"```\n{' '.join(cbmc_cmd)}\n```\n\n")
            
            f.write(f"## Next Steps\n\n")
            if cbmc_result["verification_status"] == "SUCCESS":
                f.write(f"The verification was successful. No issues were detected.\n")
            else:
                f.write(f"Based on the verification results, the following steps are recommended:\n\n")
                if cbmc_result["missing_functions"]:
                    f.write(f"1. Implement the missing functions needed by the harness\n")
                elif "memory_leak" in cbmc_result["error_categories"]:
                    f.write(f"1. Fix memory leaks by ensuring all allocated memory is freed\n")
                elif "null_pointer" in cbmc_result["error_categories"]:
                    f.write(f"1. Add null pointer checks before dereferencing pointers\n")
                elif "array_bounds" in cbmc_result["error_categories"]:
                    f.write(f"1. Add bounds checking for array accesses\n")
                else:
                    f.write(f"1. Review the verification failures and implement fixes\n")
                f.write(f"2. Run the verification again to confirm the issues are resolved\n")
    
    except subprocess.TimeoutExpired as e:
        # Handle timeout case
        if hasattr(e, 'process'):
            e.process.kill()
            e.process.wait()
        
        logger.warning(f"CBMC verification timed out for {func_name} after {timeout_seconds} seconds")
        
        # Create timeout result
        cbmc_result = {
            "verification_status": "TIMEOUT",
            "message": f"CBMC verification timed out after {timeout_seconds} seconds",
            "suggestions": "The function may have complex paths requiring longer verification time. Consider simplifying or using more targeted dependency selection.",
            "error_categories": ["timeout"],
            "missing_functions": set(),
            "verification_failures": ["timeout"],
            "error_locations": {},
            "reachable_lines": 0,
            "covered_lines": 0,
            "coverage_pct": 0.0,
            "func_reachable_lines": 0,
            "func_covered_lines": 0,
            "func_coverage_pct": 0.0,
            "errors": 0
        }
        
        # Update cbmc_results
        cbmc_results[func_name] = {
            "function": func_name,
            "status": "ERROR",
            "message": f"Error running CBMC verification: {str(e)}",
            "suggestions": "Fix the error and try again",
            "stdout": "",
            "stderr": str(e),
            "returncode": -1,
            "version": version_num,
            "error_categories": ["system_error"],
            "missing_functions": [],
            "verification_failures": ["system_error"],
            "error_locations": {},
            "dependency_files_used": len(verification_files)
        }
        
        # Save error information to files
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: ERROR\n")
            f.write(f"Message: Error running CBMC verification: {str(e)}\n")
            f.write(f"Suggestions: Fix the error and try again\n")
            f.write(f"\nDependency files used: {len(verification_files)}\n")
            
        # Create an error report
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** ERROR\n\n")
            f.write(f"**Message:** Error running CBMC verification: {str(e)}\n\n")
            f.write(f"**Suggestions:** Fix the error and try again\n\n")
            
            # Add dependency information
            f.write(f"**Dependency Files Used:** {len(verification_files)}\n\n")
            if verification_files:
                f.write("**Files included:**\n\n")
                for file_path in verification_files:
                    f.write(f"- {os.path.basename(file_path)}\n")
                f.write("\n")
            
            f.write(f"## Analysis\n\n")
            f.write(f"An error occurred during the verification process. This might be due to a system issue or a problem with the harness code.\n\n")
            
            f.write(f"## Error Details\n\n")
            f.write(f"```\n{str(e)}\n```\n\n")
            
            f.write(f"## Next Steps\n\n")
            f.write(f"1. Check if CBMC is installed and configured correctly\n")
            f.write(f"2. Review the harness code for syntax errors\n")
            f.write(f"3. Try running CBMC manually with the command above\n"), version_num, cbmc_result
        
        # Update cbmc_results
        cbmc_results[func_name] = {
            "function": func_name,
            "status": "TIMEOUT",
            "message": f"CBMC verification timed out after {timeout_seconds} seconds.",
            "suggestions": "The function may have complex paths requiring longer verification time. Consider using more selective file inclusion or increasing timeout.",
            "stdout": f"TIMEOUT: Process exceeded {timeout_seconds} second time limit",
            "stderr": "",
            "returncode": -1,
            "version": version_num,
            "error_categories": ["timeout"],
            "missing_functions": [],
            "verification_failures": ["timeout"],
            "error_locations": {},
            "dependency_files_used": len(verification_files)
        }
        
        # Save timeout information to files
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: TIMEOUT\n")
            f.write(f"Message: CBMC verification timed out after {timeout_seconds} seconds\n")
            f.write(f"Suggestions: The function may have complex paths requiring longer verification time. Consider simplifying.\n")
            f.write(f"\nDependency files used: {len(verification_files)}\n")
            
        # Create a timeout report
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** TIMEOUT\n\n")
            f.write(f"**Message:** CBMC verification timed out after 60 seconds.\n\n")
            f.write(f"**Suggestions:** The function may have complex paths requiring longer verification time. Consider simplifying.\n\n")
            
            f.write(f"## Analysis\n\n")
            f.write(f"The verification process timed out, which typically happens when the function has many complex paths or loops that CBMC needs to analyze. You may need to simplify the harness or consider using loop unwinding bounds to limit the verification scope.\n\n")
            
            f.write(f"## Next Steps\n\n")
            f.write(f"1. Review the harness implementation and simplify if possible\n")
            f.write(f"2. Add loop unwinding bounds if there are loops in the function\n")
            f.write(f"3. Consider breaking the verification into smaller parts\n")
            
    except Exception as e:
        # Handle other exceptions
        logger.error(f"Error running CBMC verification: {str(e)}", exc_info=True)
        
        # Create error result
        cbmc_result = {
            "verification_status": "ERROR",
            "message": f"Error running CBMC verification: {str(e)}",
            "suggestions": "Fix the error and try again",
            "error_categories": ["system_error"],
            "missing_functions": set(),
            "verification_failures": ["system_error"],
            "error_locations": {},
            "reachable_lines": 0,
            "covered_lines": 0,
            "coverage_pct": 0.0,
            "errors": 1
        }
        
        
        # Update cbmc_results
        cbmc_results[func_name] = {
            "function": func_name,
            "status": "ERROR",
            "message": f"Error running CBMC verification: {str(e)}",
            "suggestions": "Fix the error and try again",
            "stdout": "",
            "stderr": str(e),
            "returncode": -1,
            "version": version_num,
            "error_categories": ["system_error"],
            "missing_functions": [],
            "verification_failures": ["system_error"],
            "error_locations": {}
        }
        
        # Save error information to files
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: ERROR\n")
            f.write(f"Message: Error running CBMC verification: {str(e)}\n")
            f.write(f"Suggestions: Fix the error and try again\n")
            
        # Create an error report
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** ERROR\n\n")
            f.write(f"**Message:** Error running CBMC verification: {str(e)}\n\n")
            f.write(f"**Suggestions:** Fix the error and try again\n\n")
            
            f.write(f"## Analysis\n\n")
            f.write(f"An error occurred during the verification process. This might be due to a system issue or a problem with the harness code.\n\n")
            
            f.write(f"## Error Details\n\n")
            f.write(f"```\n{str(e)}\n```\n\n")
            
            f.write(f"## Next Steps\n\n")
            f.write(f"1. Check if CBMC is installed and configured correctly\n")
            f.write(f"2. Review the harness code for syntax errors\n")
            f.write(f"3. Try running CBMC manually with the command above\n")
    
    # Calculate verification time
    verification_time = time.time() - verification_start
    
    # Update function times dictionary
    function_times = state.get("function_times", {}).copy()
    if func_name not in function_times:
        function_times[func_name] = {}
    function_times[func_name]["verification"] = verification_time
    
    # Update result message
    result_message = f"CBMC verification for function {func_name} v{version_num} complete in {verification_time:.2f}s. Status: {cbmc_results[func_name]['status']}."
    
    return {
        "messages": [AIMessage(content=result_message)],
        "cbmc_results": cbmc_results,
        "function_times": function_times,
        "next": "evaluator"  # Always proceed to evaluator
    }

def route_from_cbmc(state):
    """Routes from CBMC to harness evaluator."""
    # Always route to evaluator
    return "evaluator"