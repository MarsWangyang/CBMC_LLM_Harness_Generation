"""
CBMC execution node for harness generator workflow with optimized file selection.
"""
import os
import re
import time
import shutil
import subprocess
import glob
import json
from langchain_core.messages import AIMessage
import logging
from utils.cbmc_parser import extract_coverage_metrics_from_json, process_cbmc_output

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
    
    # Check if we're dealing with a C keyword function and ensure we use the right name
    c_keywords = ["free", "malloc", "if", "while", "for", "return", "switch", "case", "default", "break"]
    if func_name in c_keywords:
        original_func_name = func_name
        func_name = f"function_{func_name}"
        logger.warning(f"Function name '{original_func_name}' is a C keyword. Using '{func_name}' internally to avoid conflicts.")
        # Update state for downstream processes
        state["current_function"] = func_name
        # Keep track of the original name
        state["original_function_name"] = original_func_name
    
    harnesses = state.get("harnesses", {})
    harness_code = harnesses.get(func_name, "")

    logger.info(f"Starting CBMC verification for function {func_name}")
    
    # Get result directories from state
    result_directories = state.get("result_directories", {})
    verification_base_dir = result_directories.get("verification_dir", "verification")
    harnesses_dir = result_directories.get("harnesses_dir", "harnesses")
    result_base_dir = result_directories.get("result_base_dir", "results")
    
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
            os.path.join(directory_path, "test", "include"),
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
    
    # Write harness to file with versioned filename
    harness_filename = original_func_name if ":" not in func_name else original_func_name
    harness_file = os.path.join(verification_harness_dir, f"{harness_filename}_harness_v{version_num}.c")
    
    # Remove any remaining markdown code block syntax
    harness_code = re.sub(r'```(?:c|cpp)?', '', harness_code)
    harness_code = re.sub(r'```', '', harness_code)
    harness_code = harness_code.strip()
    
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

    # Choose SAT solver
    from utils.solver_utils import setup_sat_solver
    sat_solver = setup_sat_solver()

    if sat_solver in ["kissat", "cadical"]:
        if sat_solver == "kissat":
            path = "./solvers/kissat/build/kissat"
        elif sat_solver == "cadical":
            path = "./solvers/cadical/build/cadical"
        if not os.path.exists(path):
            raise FileNotFoundError(f"{sat_solver} solver binary not found at: {path}")

        cbmc_cmd.extend(["--external-sat-solver", path])
        logger.info(f"Using {sat_solver} as CBMC sat solver")
    elif sat_solver == "minisat" or sat_solver is None:
        logger.info(f"Using default minisat as CBMC sat solver")
        pass
    else:
        # Log warning for unrecognized solver and default to no explicit solver
        logger.warning(f"Unrecognized SAT solver: {sat_solver}. Using default solver mini sat.")

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
        "--json-ui"  # Using JSON format for consistent parsing
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
            # Put STDERR first to highlight important error details
            f.write("=== STDERR (CRITICAL ERRORS) ===\n")
            f.write(cbmc_stderr)
            f.write("\n\n=== STDOUT (VERIFICATION OUTPUT) ===\n")
            f.write(cbmc_stdout)
        
        # Run coverage checking separately with JSON output
        try:
            logger.info(f"Running coverage checking for {func_name}")
            coverage_process = subprocess.run(
                coverage_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=timeout_seconds*2,  # Shorter timeout for coverage
                check=False
            )
            
            coverage_stdout = coverage_process.stdout
            
            # Save JSON coverage output to a file
            coverage_json_file = os.path.join(func_verification_dir, f"v{version_num}_coverage.json")
            with open(coverage_json_file, "w") as f:
                f.write(coverage_stdout)
            
            # Process the coverage JSON immediately
            try:
                # Parse the JSON coverage data
                json_data = json.loads(coverage_stdout)
                
                # Define function to parse line ranges
                def parse_line_ranges(line_ranges):
                    """Parse a string of line ranges into a set of unique line numbers."""
                    unique_lines = set()
                    for line_range in line_ranges.split(','):
                        if '-' in line_range:
                            start, end = map(int, line_range.split('-'))
                            unique_lines.update(range(start, end + 1))
                        else:
                            try:
                                unique_lines.add(int(line_range))
                            except ValueError:
                                pass  # Skip if not a valid integer
                    return unique_lines

                # Extract coverage metrics
                coverage_metrics = extract_coverage_metrics_from_json(json_data, func_name, version_num)
                
                # Store metrics in a dedicated file
                metrics_file = os.path.join(func_verification_dir, f"v{version_num}_metrics.json")
                with open(metrics_file, "w") as f:
                    json.dump(coverage_metrics, f, indent=2)
                    
                # Create coverage and errors directory structure for centralized collection
                coverage_dir = os.path.join(result_base_dir, "coverage", "data")
                errors_dir = os.path.join(result_base_dir, "errors", "data")
                os.makedirs(coverage_dir, exist_ok=True)
                os.makedirs(errors_dir, exist_ok=True)
                
                # Create flattened data for CSV storage
                flat_data = {
                    "function": func_name,
                    "version": version_num,
                    "total_coverage_pct": coverage_metrics.get("total_coverage_pct", 0),
                    "func_coverage_pct": coverage_metrics.get("func_coverage_pct", 0),
                    "main_total_lines": coverage_metrics.get("main_total_lines", 0),
                    "main_reachable_lines": coverage_metrics.get("main_reachable_lines", 0),
                    "main_uncovered_lines": coverage_metrics.get("main_uncovered_lines", 0),
                    "target_total_lines": coverage_metrics.get("target_total_lines", 0),
                    "target_reachable_lines": coverage_metrics.get("target_reachable_lines", 0),
                    "target_uncovered_lines": coverage_metrics.get("target_uncovered_lines", 0),
                    "total_combined_lines": coverage_metrics.get("total_combined_lines", 0),
                    "reachable_combined_lines": coverage_metrics.get("reachable_combined_lines", 0),
                }
                
                # Save as JSON for each function version
                func_metrics_file = os.path.join(coverage_dir, f"{func_name}_v{version_num}.json")
                with open(func_metrics_file, "w") as f:
                    json.dump(flat_data, f, indent=2)
                
                # Update the running CSV file
                csv_path = os.path.join(coverage_dir, "coverage_metrics.csv")
                file_exists = os.path.exists(csv_path)
                
                with open(csv_path, "a") as f:
                    # Write headers if file is new
                    if not file_exists:
                        headers = ",".join(flat_data.keys())
                        f.write(f"{headers}\n")
                    
                    # Write data row
                    values = [str(v).replace(",", ";") for v in flat_data.values()]
                    f.write(f"{','.join(values)}\n")
                
                # Print coverage summary
                print(f"\n=== Coverage Metrics for {func_name} (v{version_num}) ===")
                print(f"Main function: {coverage_metrics['main_reachable_lines']}/{coverage_metrics['main_total_lines']} lines")
                print(f"Target function: {coverage_metrics['target_reachable_lines']}/{coverage_metrics['target_total_lines']} lines")
                print(f"Total coverage: {coverage_metrics['total_coverage_pct']:.2f}%")
                print(f"Function coverage: {coverage_metrics['func_coverage_pct']:.2f}%")
                print("=" * 50)
                
                # Store coverage metrics for later use with cbmc_result
                # We'll apply them after cbmc_result is initialized
                stored_coverage_metrics = coverage_metrics.copy()
                
            except json.JSONDecodeError as e:
                logger.error(f"Error parsing JSON coverage data: {str(e)}")
            except Exception as e:
                logger.error(f"Error processing coverage data: {str(e)}")
            
        except subprocess.TimeoutExpired:
            logger.warning(f"Coverage check timed out for {func_name}")
        except Exception as e:
            logger.error(f"Error running coverage check: {str(e)}")
        
        # Process CBMC output using our enhanced parser (with stderr prioritization)
        # The process_cbmc_output function now automatically preserves stderr in the result
        cbmc_result = process_cbmc_output(cbmc_stdout, cbmc_stderr)
        
        # Double-check that stderr is included in the result for line-specific error tracing
        if "stderr" not in cbmc_result:
            cbmc_result["stderr"] = cbmc_stderr
            
        # Make sure we have at least a basic error count if stderr contains errors
        if cbmc_stderr and "error:" in cbmc_stderr.lower():
            # Count error lines in stderr
            stderr_error_count = cbmc_stderr.lower().count("error:")
            
            # Force update the error count to reflect actual errors
            if stderr_error_count > 0:
                cbmc_result["error_count"] = max(stderr_error_count, cbmc_result.get("error_count", 0))
                cbmc_result["reported_errors"] = max(stderr_error_count, cbmc_result.get("reported_errors", 0))
                
                # Ensure we have at least one error category
                if not cbmc_result.get("error_categories"):
                    cbmc_result["error_categories"] = ["generic_error"]
                
                logger.warning(f"Updated error count from stderr: {stderr_error_count} errors found")
            
        # Save error metrics to CSV similar to coverage metrics
        errors_dir = os.path.join(result_base_dir, "errors", "data")
        os.makedirs(errors_dir, exist_ok=True)
        
        # Create flattened error data for CSV storage
        error_data = {
            "function": func_name,
            "version": version_num,
            "status": cbmc_result.get("verification_status", "UNKNOWN"),
            "error_count": cbmc_result.get("error_count", 0),
            "reported_errors": cbmc_result.get("reported_errors", 0),
            "failure_count": cbmc_result.get("failure_count", 0),
            "error_categories": ";".join(cbmc_result.get("error_categories", []))
        }
        
        # Save as JSON for each function version
        error_metrics_file = os.path.join(errors_dir, f"{func_name}_v{version_num}.json")
        with open(error_metrics_file, "w") as f:
            json.dump(error_data, f, indent=2)
        
        # Update the running CSV file
        error_csv_path = os.path.join(errors_dir, "error_metrics.csv")
        error_file_exists = os.path.exists(error_csv_path)
        
        with open(error_csv_path, "a") as f:
            # Write headers if file is new
            if not error_file_exists:
                headers = ",".join(error_data.keys())
                f.write(f"{headers}\n")
            
            # Write data row
            values = [str(v).replace(",", ";") for v in error_data.values()]
            f.write(f"{','.join(values)}\n")
            
        # Extract specific error signatures from stderr for more precise error handling
        if cbmc_stderr:
            # Function to extract error signatures
            def extract_error_signatures(stderr_text):
                """Extract unique error signatures from stderr text."""
                error_sigs = []
                if not stderr_text:
                    return error_sigs
                    
                for line in stderr_text.splitlines():
                    # Focus on actual error messages, not just line numbers
                    if 'error:' in line or 'ERROR:' in line:
                        # Extract core error message without line numbers and file paths
                        parts = line.split('error:', 1)
                        if len(parts) > 1:
                            error_msg = parts[1].strip()
                            # Keep only the error message content
                            error_sigs.append(error_msg)
                return error_sigs
                
            # Get specific error messages and add to result
            error_signatures = extract_error_signatures(cbmc_stderr)
            if error_signatures:
                cbmc_result["error_signatures"] = error_signatures
                logger.info(f"Extracted error signatures: {error_signatures}")
                
                # Add specific error category types based on error signatures
                for sig in error_signatures:
                    if "function 'nondet_" in sig.lower() and "not declared" in sig.lower():
                        if "nondet_function_error" not in cbmc_result["error_categories"]:
                            cbmc_result["error_categories"].append("nondet_function_error")
                            
                    if "member" in sig.lower() and "not found" in sig.lower():
                        if "struct_member_error" not in cbmc_result["error_categories"]:
                            cbmc_result["error_categories"].append("struct_member_error")
                            
                    if "not declared" in sig.lower() or "undeclared" in sig.lower():
                        if "declaration_error" not in cbmc_result["error_categories"]:
                            cbmc_result["error_categories"].append("declaration_error")
                            
                    if "struct" in sig.lower() or "has no member" in sig.lower():
                        if "struct_error" not in cbmc_result["error_categories"]:
                            cbmc_result["error_categories"].append("struct_error")
            
        # Make sure we prioritize stderr output when there are critical errors
        # This ensures that downstream components focus on the most important error information
        if cbmc_stderr and ("error:" in cbmc_stderr or "undefined reference" in cbmc_stderr):
            logger.warning("Critical errors found in STDERR output, prioritizing these errors")
            
            # Ensure error categories reflect stderr issues
            if "redeclaration" in cbmc_stderr and "redeclaration" not in cbmc_result["error_categories"]:
                cbmc_result["error_categories"].append("redeclaration")
                
            if "undefined reference" in cbmc_stderr and "linking_error" not in cbmc_result["error_categories"]:
                cbmc_result["error_categories"].append("linking_error")
        
        # Apply the stored coverage metrics if they were successfully collected
        stored_coverage_metrics = locals().get('stored_coverage_metrics')
        if stored_coverage_metrics:
            for key, value in stored_coverage_metrics.items():
                cbmc_result[key] = value
        
        # Create a structured result for the state
        cbmc_results[func_name] = {
            "function": func_name,
            "status": cbmc_result["verification_status"],
            "message": cbmc_result["message"],
            "suggestions": cbmc_result["suggestions"],
            "stdout": cbmc_stdout,
            "stderr": cbmc_stderr,  # Make sure stderr is included
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
            "func_coverage_pct": cbmc_result["func_coverage_pct"],
            # Add new enhanced metrics
            "main_reachable_lines": cbmc_result.get("main_reachable_lines", 0),
            "main_total_lines": cbmc_result.get("main_total_lines", 0),
            "main_uncovered_lines": cbmc_result.get("main_uncovered_lines", 0),
            "target_total_lines": cbmc_result.get("target_total_lines", 0),
            "target_reachable_lines": cbmc_result.get("target_reachable_lines", 0),
            "target_uncovered_lines": cbmc_result.get("target_uncovered_lines", 0),
            "total_combined_lines": cbmc_result.get("total_combined_lines", 0),
            "reachable_combined_lines": cbmc_result.get("reachable_combined_lines", 0),
            # Add failure and error counts
            "failure_count": cbmc_result.get("failure_count", 0),
            "error_count": cbmc_result.get("error_count", 0)
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
            
            # Add enhanced metrics
            f.write("\n=== ENHANCED COVERAGE METRICS ===\n")
            f.write(f"Main Total Lines: {cbmc_result.get('main_total_lines', 0)}\n")
            f.write(f"Main Reachable Lines: {cbmc_result.get('main_reachable_lines', 0)}\n")
            f.write(f"Main Uncovered Lines: {cbmc_result.get('main_uncovered_lines', 0)}\n")
            f.write(f"Target Total Lines: {cbmc_result.get('target_total_lines', 0)}\n")
            f.write(f"Target Reachable Lines: {cbmc_result.get('target_reachable_lines', 0)}\n")
            f.write(f"Target Uncovered Lines: {cbmc_result.get('target_uncovered_lines', 0)}\n")
            f.write(f"Total Combined Lines: {cbmc_result.get('total_combined_lines', 0)}\n")
            f.write(f"Reachable Combined Lines: {cbmc_result.get('reachable_combined_lines', 0)}\n")
            
            if cbmc_result["error_categories"]:
                f.write("\n=== ERROR CATEGORIES ===\n")
                for category in cbmc_result["error_categories"]:
                    f.write(f"- {category}\n")
            
            if cbmc_result["missing_functions"]:
                f.write("\n=== MISSING FUNCTIONS ===\n")
                for func in cbmc_result["missing_functions"]:
                    f.write(f"- {func}\n")
            
            # Put STDERR first to highlight important error details
            f.write("\n=== STDERR (CRITICAL ERRORS) ===\n")
            f.write(cbmc_stderr)
            f.write("\n\n=== STDOUT (VERIFICATION OUTPUT) ===\n")
            f.write(cbmc_stdout)
        
        # Generate a more helpful report in markdown format
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** {cbmc_result['verification_status']}\n\n")
            f.write(f"**Message:** {cbmc_result['message']}\n\n")
            
            # Add specific text for successful verifications
            if cbmc_result['verification_status'] == "SUCCESS":
                f.write(f"**Verification passed successfully**. No verification failures were detected.\n\n") 
            elif cbmc_result["suggestions"]:
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
            f.write(f"| Main Total Lines | {cbmc_result.get('main_total_lines', 0)} |\n")
            f.write(f"| Main Reachable Lines | {cbmc_result.get('main_reachable_lines', 0)} |\n")
            f.write(f"| Main Uncovered Lines | {cbmc_result.get('main_uncovered_lines', 0)} |\n")
            f.write(f"| Target Total Lines | {cbmc_result.get('target_total_lines', 0)} |\n")
            f.write(f"| Target Reachable Lines | {cbmc_result.get('target_reachable_lines', 0)} |\n")
            f.write(f"| Target Uncovered Lines | {cbmc_result.get('target_uncovered_lines', 0)} |\n")
            f.write(f"| Total Combined Lines | {cbmc_result.get('total_combined_lines', 0)} |\n")
            f.write(f"| Reachable Combined Lines | {cbmc_result.get('reachable_combined_lines', 0)} |\n")
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
            
            # Add error locations if any - with enhanced line number tracing
            if cbmc_result["error_locations"]:
                f.write(f"## Error Locations - Line-Specific Tracing\n\n")
                
                # First, get any detailed error messages from stderr
                detailed_errors = {}
                if cbmc_stderr:
                    for line in cbmc_stderr.split('\n'):
                        if 'error:' in line or ('warning:' in line and any(critical in line.lower() 
                                                                 for critical in ['pointer', 'memory', 'null', 'invalid'])):
                            # Extract line information using improved regex
                            loc_match = re.search(r'([^:]+):(\d+)(?::\d+)?:', line)
                            if loc_match:
                                file_name = loc_match.group(1)
                                line_num = int(loc_match.group(2))
                                error_msg = line.split(':', 3)[-1].strip() if len(line.split(':', 3)) >= 4 else line
                                
                                key = f"{file_name}:{line_num}"
                                if key not in detailed_errors:
                                    detailed_errors[key] = []
                                detailed_errors[key].append(error_msg)
                
                # Process each file and its error lines 
                for file, lines in cbmc_result["error_locations"].items():
                    f.write(f"### File: `{file}`\n\n")
                    f.write(f"| Line | Error Details |\n")
                    f.write(f"|------|---------------|\n")
                    
                    for line_num in sorted(lines):
                        key = f"{file}:{line_num}"
                        error_detail = "No specific error details available"
                        
                        # Check if we have detailed error message for this line
                        if key in detailed_errors and detailed_errors[key]:
                            error_detail = "; ".join(detailed_errors[key])
                        
                        # If it's a harness file, try to include line content
                        if "_harness_" in file or "harness" in file:
                            f.write(f"| **{line_num}** | {error_detail} |\n")
                        else:
                            f.write(f"| **{line_num}** | {error_detail} |\n")
                
                f.write("\n> **Note:** Look at these specific line numbers in your code to identify and fix issues.\n\n")
            
            # Add missing functions if any
            if cbmc_result["missing_functions"]:
                f.write(f"## Missing Functions\n\n")
                for func in cbmc_result["missing_functions"]:
                    f.write(f"- {func}\n")
                f.write("\n")
            
            # Add harness details
            f.write(f"## Harness Details\n\n")
            f.write(f"The harness file is located at: `{harness_file}`\n\n")
            
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
    
    # Check for slow verification that might indicate potential future timeouts
    is_slow_verification = verification_time > 45  # Over 45 seconds is considered slow
    if is_slow_verification and cbmc_results[func_name].get("status") != "TIMEOUT":
        logger.warning(f"Slow verification detected for {func_name}: {verification_time:.2f}s")
        
        # Add special flag and suggestion for slow verification
        cbmc_results[func_name]["is_slow_verification"] = True
        cbmc_results[func_name]["slow_verification_time"] = verification_time
        
        # Add performance warning to error categories
        if "error_categories" not in cbmc_results[func_name]:
            cbmc_results[func_name]["error_categories"] = []
        if "performance_warning" not in cbmc_results[func_name]["error_categories"]:
            cbmc_results[func_name]["error_categories"].append("performance_warning")
        
        # Add special suggestion for performance
        if "suggestions" not in cbmc_results[func_name] or not cbmc_results[func_name]["suggestions"]:
            cbmc_results[func_name]["suggestions"] = "Consider simplifying the harness to improve verification speed and prevent future timeouts"
        else:
            cbmc_results[func_name]["suggestions"] += ". Also consider simplifying the harness to improve verification speed"
    
    # Update result message with appropriate status indicators
    status = cbmc_results[func_name].get("status", "UNKNOWN")
    status_indicator = ""
    if status == "TIMEOUT":
        status_indicator = "⏱️ TIMEOUT"
    elif status == "SUCCESS":
        status_indicator = "✅ SUCCESS"
    elif is_slow_verification:
        status_indicator = "⚠️ SLOW"
    else:
        status_indicator = "❌ FAILED"
        
    result_message = f"CBMC verification for {func_name} v{version_num} complete in {verification_time:.2f}s. Status: {status_indicator}"
    
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