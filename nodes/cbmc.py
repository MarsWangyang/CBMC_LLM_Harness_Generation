"""
CBMC execution node for harness generator workflow.
"""
import os
import re
import time
import shutil
import subprocess
from langchain_core.messages import AIMessage

def cbmc_node(state):
    """Executes CBMC verification on the current function's harness using sources from verification/sources directory."""
    verification_start = time.time()
    
    func_name = state.get("current_function", "")
    harnesses = state.get("harnesses", {})
    harness_code = harnesses.get(func_name, "")
    
    if not harness_code:
        return {
            "messages": [AIMessage(content=f"Error: No harness available for function {func_name}.")],
            "next": "junction"  # Return to junction to process next function
        }
    
    # Extract file path from function name if it includes file info
    file_basename = None
    original_func_name = func_name
    
    if ":" in func_name:
        file_basename, original_func_name = func_name.split(":", 1)
    
    # Create organized directory structure for verification
    verification_base_dir = "verification"
    os.makedirs(verification_base_dir, exist_ok=True)
    
    # Create function-specific directory
    func_verification_dir = os.path.join(verification_base_dir, func_name)
    os.makedirs(func_verification_dir, exist_ok=True)
    
    # Create proper directory structure for verification
    verification_src_dir = os.path.join(verification_base_dir, "src")
    os.makedirs(verification_src_dir, exist_ok=True)
    
    # Create include directory for headers
    verification_include_dir = os.path.join(verification_base_dir, "include")
    os.makedirs(verification_include_dir, exist_ok=True)
    
    # Create stubs directory for stubs
    verification_stubs_dir = os.path.join(verification_base_dir, "stubs")
    os.makedirs(verification_stubs_dir, exist_ok=True)
    
    # Create sources directory for CBMC sources
    verification_sources_dir = os.path.join(verification_base_dir, "sources")
    os.makedirs(verification_sources_dir, exist_ok=True)
    
    # Determine version number from refinement attempts
    refinement_num = state.get("refinement_attempts", {}).get(func_name, 0)
    version_num = refinement_num + 1
    
    # Define CBMC_MAX_OBJECT_SIZE
    cbmc_max_object_size = 1024 * 1024  # 1MB is a typical reasonable size
    
    # Create a header file with the CBMC_MAX_OBJECT_SIZE definition
    cbmc_defs_header = os.path.join(verification_include_dir, "cbmc_defs.h")
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
        
        if original_source_dir and os.path.exists(original_source_dir):
            # First, copy only the necessary source files to avoid duplication
            for root, dirs, files in os.walk(original_source_dir):
                for file in files:
                    # Only copy .c and .h files to corresponding directories
                    if file.endswith(('.c', '.cpp')):
                        src_file = os.path.join(root, file)
                        dest_file = os.path.join(verification_src_dir, file)
                        shutil.copy2(src_file, dest_file)
                    elif file.endswith(('.h', '.hpp')):
                        src_file = os.path.join(root, file)
                        dest_file = os.path.join(verification_include_dir, file)
                        shutil.copy2(src_file, dest_file)
        
        # Get specific source file for this function from embeddings if available
        file_path = None
        embeddings = state.get("embeddings", {})
        functions = embeddings.get("functions", {})
        
        if func_name in functions and "file_path" in functions[func_name]:
            file_path = functions[func_name]["file_path"]
            if file_path and os.path.exists(file_path):
                source_file = os.path.join(verification_src_dir, os.path.basename(file_path))
    else:
        # Original single-file mode - write source to a flat file
        source_file = os.path.join(verification_src_dir, "source.c")
        with open(source_file, "w") as f:
            f.write(state.get("source_code", ""))
    
    # Find source files - prioritize verification/sources directory
    source_files = []
    
    # First, look for files in the sources directory
    sources_dir_files = [f for f in os.listdir(verification_sources_dir) if f.endswith(('.c', '.cpp'))]
    if sources_dir_files:
        # Use all files from the sources directory
        for file in sources_dir_files:
            source_files.append(os.path.join(verification_sources_dir, file))
    else:
        # Fall back to src directory if no files in sources directory
        src_dir_files = [f for f in os.listdir(verification_src_dir) if f.endswith(('.c', '.cpp'))]
        if src_dir_files:
            for file in src_dir_files:
                source_files.append(os.path.join(verification_src_dir, file))
        else:
            # Create a fallback source file if no source files were found
            fallback_source = os.path.join(verification_src_dir, "source.c")
            with open(fallback_source, "w") as f:
                f.write("// Fallback source file\n")
            source_files.append(fallback_source)
            
    # Write harness to file - use original function name in the filename
    harness_filename = original_func_name if ":" not in func_name else original_func_name
    harness_file = os.path.join(verification_src_dir, f"{harness_filename}_harness.c")
    with open(harness_file, "w") as f:
        # Add include for the CBMC definitions header
        f.write("#include \"cbmc_defs.h\"\n\n")
        f.write(harness_code)

    # Copy necessary CBMC include files for verification
    # Look for test/cbmc directory relative to the project source
    project_dir = os.path.dirname(state.get("source_directory", ""))
    cbmc_include_dir = os.path.join(project_dir, "test", "cbmc", "include")
    
    # If not found, try looking one level up
    if not os.path.exists(cbmc_include_dir):
        cbmc_include_dir = os.path.join(os.path.dirname(project_dir), "test", "cbmc", "include")
    
    # If still not found, try looking in the current directory structure
    if not os.path.exists(cbmc_include_dir):
        cbmc_include_dir = "test/cbmc/include"
    
    if os.path.exists(cbmc_include_dir):
        # Copy all CBMC include files
        for file in os.listdir(cbmc_include_dir):
            src_file = os.path.join(cbmc_include_dir, file)
            dest_file = os.path.join(verification_include_dir, file)
            if os.path.isfile(src_file):
                shutil.copy2(src_file, dest_file)
                print(f"Copied CBMC include file: {file}")
                
    # Also check for stubs directory
    cbmc_stubs_dir = os.path.join(project_dir, "test", "cbmc", "stubs")
    
    # If not found, try looking one level up
    if not os.path.exists(cbmc_stubs_dir):
        cbmc_stubs_dir = os.path.join(os.path.dirname(project_dir), "test", "cbmc", "stubs")
    
    # If still not found, try looking in the current directory structure
    if not os.path.exists(cbmc_stubs_dir):
        cbmc_stubs_dir = "test/cbmc/stubs"
    
    if os.path.exists(cbmc_stubs_dir):
        # Copy all CBMC stub files
        for file in os.listdir(cbmc_stubs_dir):
            src_file = os.path.join(cbmc_stubs_dir, file)
            dest_file = os.path.join(verification_stubs_dir, file)
            if os.path.isfile(src_file):
                shutil.copy2(src_file, dest_file)
                print(f"Copied CBMC stub file: {file}")
                
    # Check for sources directory
    cbmc_sources_dir = os.path.join(project_dir, "test", "cbmc", "sources")
    
    # If not found, try looking one level up
    if not os.path.exists(cbmc_sources_dir):
        cbmc_sources_dir = os.path.join(os.path.dirname(project_dir), "test", "cbmc", "sources")
    
    # If still not found, try looking in the current directory structure
    if not os.path.exists(cbmc_sources_dir):
        cbmc_sources_dir = "test/cbmc/sources"
    
    if os.path.exists(cbmc_sources_dir):
        # Copy all CBMC source files
        for file in os.listdir(cbmc_sources_dir):
            src_file = os.path.join(cbmc_sources_dir, file)
            dest_file = os.path.join(verification_sources_dir, file)
            if os.path.isfile(src_file):
                shutil.copy2(src_file, dest_file)
                print(f"Copied CBMC source file: {file}")
    
    # Build list of CBMC command parameters - use sources from verification/sources
    cbmc_cmd = [
        "cbmc",
    ]
    
    # Add source files from verification/sources first
    for file in os.listdir(verification_sources_dir):
        if file.endswith(('.c', '.cpp')):
            source_file_path = os.path.join(verification_sources_dir, file)
            cbmc_cmd.append(source_file_path)
    
    # Add the harness file
    cbmc_cmd.append(harness_file)
    
    # Add main CBMC options
    cbmc_cmd.extend([
        "--function", "main",
        "--memory-leak-check",
        "--memory-cleanup-check",
        "--bounds-check",
        "--pointer-overflow-check",
        "--div-by-zero-check",
        f"--object-bits", "8",  # Default for CBMC_OBJECT_BITS
    ])
    
    # Add CBMC object size constraint definition
    cbmc_cmd.extend([
        "-DCBMC_MAX_OBJECT_SIZE=" + str(cbmc_max_object_size)
    ])
    
    # Add stub files as needed
    for file in os.listdir(verification_stubs_dir):
        if file.endswith(('.c', '.cpp')):
            stub_file_path = os.path.join(verification_stubs_dir, file)
            cbmc_cmd.append(stub_file_path)
    
    # Add necessary include paths in the correct order
    cbmc_cmd.extend([
        "-I", verification_include_dir,
        "-I", verification_src_dir,
        "-I", verification_stubs_dir,
        "-I", verification_sources_dir
    ])
    
    # Save the command for debugging
    cmd_file = os.path.join(func_verification_dir, f"v{version_num}_command.txt")
    with open(cmd_file, 'w') as f:
        f.write(" ".join(cbmc_cmd))
    
    # Initialize dictionaries for tracking errors if they don't exist
    cbmc_error_messages = state.get("cbmc_error_messages", {}).copy()
    harness_syntax_errors = state.get("harness_syntax_errors", {}).copy()
    parsing_issues = state.get("parsing_issues", {}).copy()
    verification_failures = state.get("verification_failures", {}).copy()
    
    try:
        # Use subprocess.run for more reliable output capture
        process = subprocess.run(
            cbmc_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=60,
            check=False  # Don't raise exception on non-zero return
        )
        
        stdout = process.stdout
        stderr = process.stderr
        returncode = process.returncode
        
        # Combine stdout and stderr for more complete output
        full_output = stdout
        if stderr:
            full_output += "\n--- STDERR ---\n" + stderr
        
        # Process results
        status = "SUCCESS" if returncode == 0 else "FAILED"
        message = "VERIFICATION SUCCESSFUL: No issues detected."
        suggestions = ""
        
        # More detailed error analysis
        if returncode != 0:
            # Check for syntax errors or parsing issues first
            syntax_error_match = re.search(r'syntax error at line (\d+)', stderr)
            if syntax_error_match:
                line_number = syntax_error_match.group(1)
                harness_syntax_errors[func_name] = f"Syntax error at line {line_number}"
                message = f"HARNESS ERROR: Syntax error in harness at line {line_number}."
                suggestions = "Fix the syntax error in the harness."
            
            # Check for parsing issues
            if "PARSING ERROR" in stderr:
                parsing_issues[func_name] = True
                
                # Extract specific parsing error
                parsing_error_match = re.search(r'(.+?): fatal error: (.+)$', stderr, re.MULTILINE)
                if parsing_error_match:
                    error_location = parsing_error_match.group(1)
                    error_message = parsing_error_match.group(2)
                    message = f"PARSING ERROR: {error_message}"
                    suggestions = f"Fix the parsing error in {error_location}."
                else:
                    message = "PARSING ERROR: Could not parse the harness."
                    suggestions = "Check for missing include files or syntax errors."
            
            # Track the specific error message for this function
            cbmc_error_messages[func_name] = message
            
            # Check for common verification failures if no syntax/parsing issues
            if "VERIFICATION FAILED" in stdout and not parsing_issues.get(func_name, False):
                failure_types = []
                
                if "memory leak detected" in stdout.lower():
                    failure_types.append("memory_leak")
                    message = "VERIFICATION FAILED: Memory leak detected."
                    suggestions = "Ensure all allocated memory is freed in all execution paths."
                
                if "dereference failure" in stdout.lower() or "NULL pointer" in stdout.lower():
                    failure_types.append("null_pointer")
                    message = "VERIFICATION FAILED: Null pointer dereference detected."
                    suggestions = "Add null pointer checks before dereferencing."
                
                if "array bounds" in stdout.lower():
                    failure_types.append("array_bounds")
                    message = "VERIFICATION FAILED: Array bounds violation detected."
                    suggestions = "Add bounds checking for array accesses."
                
                if "division by zero" in stdout.lower():
                    failure_types.append("division_by_zero")
                    message = "VERIFICATION FAILED: Division by zero detected."
                    suggestions = "Add checks to ensure divisors are non-zero."
                
                if "pointer arithmetic" in stdout.lower() and "overflow" in stdout.lower():
                    failure_types.append("pointer_overflow")
                    message = "VERIFICATION FAILED: Pointer arithmetic overflow detected."
                    suggestions = "Ensure pointer arithmetic stays within allocated bounds."
                
                if "arithmetic overflow" in stdout.lower():
                    failure_types.append("arithmetic_overflow")
                    message = "VERIFICATION FAILED: Arithmetic overflow detected."
                    suggestions = "Add overflow checking for arithmetic operations."
                
                if "type" in stdout.lower() and "conversion" in stdout.lower():
                    failure_types.append("type_conversion")
                    message = "VERIFICATION FAILED: Problematic type conversion detected."
                    suggestions = "Verify type conversions do not result in information loss."
                
                if failure_types:
                    verification_failures[func_name] = failure_types
                else:
                    # Try to extract more details from the output
                    failure_lines = [line for line in stdout.split('\n') if "FAILED" in line]
                    if failure_lines:
                        message = f"VERIFICATION FAILED: {failure_lines[0]}"
                        verification_failures[func_name] = ["general_verification_failure"]
                    else:
                        message = "VERIFICATION FAILED: Unspecified verification error."
                        verification_failures[func_name] = ["unspecified_failure"]
                    
                    # Look for any assertion failures
                    assertion_lines = [line for line in stdout.split('\n') if "assertion" in line.lower() and "failed" in line.lower()]
                    if assertion_lines:
                        suggestions = f"Review assertion failure: {assertion_lines[0]}"
                    else:
                        suggestions = "Review the full verification output for details."
            else:
                # Handle errors that aren't explicit verification failures
                if "PARSING ERROR" not in stderr and "syntax error" not in stderr:
                    message = f"VERIFICATION FAILED: Command returned error code {returncode}."
                    if "file not found" in stderr:
                        missing_file_match = re.search(r"'([^']+)' file not found", stderr)
                        if missing_file_match:
                            missing_file = missing_file_match.group(1)
                            message += f" Missing header file: '{missing_file}'."
                            suggestions = f"Make sure '{missing_file}' is available in the include path."
                    elif stderr:
                        message += f" Error: {stderr[:200]}..."
                    suggestions = suggestions or "Check the CBMC command and harness for errors."
        
        # Update the results dictionary
        cbmc_results = state.get("cbmc_results", {}).copy()
        cbmc_results[func_name] = {
            "function": func_name,
            "status": status,
            "message": message,
            "suggestions": suggestions,
            "stdout": full_output,
            "returncode": returncode,
            "version": version_num,
            "has_syntax_error": func_name in harness_syntax_errors,
            "has_parsing_issue": func_name in parsing_issues,
            "verification_failure_types": verification_failures.get(func_name, [])
        }
        
        # Save verification results to file with version
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: {status}\n")
            f.write(f"Message: {message}\n")
            if suggestions:
                f.write(f"Suggestions: {suggestions}\n")
            f.write("\nDetailed Output:\n")
            f.write(full_output)
        
        # Also save raw output for debugging
        raw_output_file = os.path.join(func_verification_dir, f"v{version_num}_raw_output.txt")
        with open(raw_output_file, "w") as f:
            f.write(full_output)
        
        # Generate a verification report for this version
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** {status}\n\n")
            f.write(f"**Message:** {message}\n\n")
            if suggestions:
                f.write(f"**Suggestions:** {suggestions}\n\n")
            
            f.write(f"## Harness Details\n\n")
            f.write(f"The harness file is located at: `harnesses/{func_name}/v{version_num}.c`\n\n")
            
            f.write(f"## Verification Command\n\n")
            f.write(f"```\n{' '.join(cbmc_cmd)}\n```\n\n")
            
            f.write(f"## Detailed Output\n\n")
            f.write("```\n")
            # Only include the first 20 lines and last 20 lines if output is very long
            if len(full_output.split('\n')) > 50:
                output_lines = full_output.split('\n')
                trimmed_output = '\n'.join(output_lines[:20] + ["\n... [output trimmed] ...\n"] + output_lines[-20:])
                f.write(trimmed_output)
                f.write("\n\nNote: Output has been trimmed. See full output in v{version_num}_raw_output.txt\n")
            else:
                f.write(full_output)
            f.write("\n```\n\n")
            
            if returncode != 0:
                f.write(f"## Analysis\n\n")
                f.write(f"The verification failed with return code {returncode}. ")
                if suggestions:
                    f.write(f"Based on the output, it is recommended to {suggestions.lower()}\n\n")
                
                f.write(f"## Next Steps\n\n")
                f.write(f"1. Review the harness implementation\n")
                f.write(f"2. Implement the suggested fixes\n")
                f.write(f"3. Run another verification iteration\n")
            else:
                f.write(f"## Analysis\n\n")
                f.write(f"The verification was successful. No issues were detected with the current harness implementation.\n\n")
        
    except subprocess.TimeoutExpired as e:
        # Handle timeout - make sure process exists before trying to kill it
        # The 'e' parameter will contain the process
        if hasattr(e, 'process'):
            e.process.kill()
            e.process.wait()
        
        # Handle timeout
        cbmc_results = state.get("cbmc_results", {}).copy()
        cbmc_results[func_name] = {
            "function": func_name,
            "status": "TIMEOUT",
            "message": "CBMC verification timed out after 60 seconds.",
            "suggestions": "The function may have complex paths requiring longer verification time. Consider simplifying.",
            "stdout": "TIMEOUT: Process exceeded 60 second time limit",
            "version": version_num,
            "has_syntax_error": False,
            "has_parsing_issue": False,
            "verification_failure_types": ["timeout"]
        }
        
        # Save timeout to file
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: TIMEOUT\n")
            f.write(f"Error: CBMC verification timed out after 60 seconds\n")
            f.write(f"Suggestions: The function may have complex paths requiring longer verification time. Consider simplifying.\n")
            
        # Generate timeout report
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
        # Handle errors
        cbmc_results = state.get("cbmc_results", {}).copy()
        cbmc_results[func_name] = {
            "function": func_name,
            "status": "ERROR",
            "message": f"Error running CBMC: {str(e)}",
            "suggestions": "Check if CBMC is installed correctly.",
            "stdout": f"ERROR: {str(e)}",
            "version": version_num,
            "has_syntax_error": False,
            "has_parsing_issue": False,
            "verification_failure_types": ["system_error"]
        }
        
        # Save error to file
        verification_file = os.path.join(func_verification_dir, f"v{version_num}_results.txt")
        with open(verification_file, "w") as f:
            f.write(f"Function: {func_name}\n")
            f.write(f"Version: {version_num}\n")
            f.write(f"Status: ERROR\n")
            f.write(f"Error: {str(e)}\n")
            
        # Generate error report
        report_file = os.path.join(func_verification_dir, f"v{version_num}_report.md")
        with open(report_file, "w") as f:
            f.write(f"# CBMC Verification Report - {func_name} (Version {version_num})\n\n")
            f.write(f"## Summary\n\n")
            f.write(f"**Status:** ERROR\n\n")
            f.write(f"**Message:** Error running CBMC: {str(e)}\n\n")
            f.write(f"**Suggestions:** Check if CBMC is installed correctly.\n\n")
            
            f.write(f"## Analysis\n\n")
            f.write(f"The verification process encountered an error. This is typically due to issues with the CBMC installation or with the harness itself.\n\n")
            
            f.write(f"## Next Steps\n\n")
            f.write(f"1. Verify your CBMC installation is working correctly\n")
            f.write(f"2. Check the harness for syntax errors\n")
            f.write(f"3. Review the error message for specific issues to fix\n")
    
    # Calculate verification time
    verification_time = time.time() - verification_start
    
    # Update function times dictionary
    function_times = state.get("function_times", {}).copy()
    if func_name not in function_times:
        function_times[func_name] = {}
    function_times[func_name]["verification"] = verification_time
    
    return {
        "messages": [AIMessage(content=f"CBMC verification for function {func_name} v{version_num} complete in {verification_time:.2f}s. Status: {cbmc_results[func_name]['status']}. Results saved to {func_verification_dir}/v{version_num}_results.txt")],
        "cbmc_results": cbmc_results,
        "function_times": function_times,
        "cbmc_error_messages": cbmc_error_messages,
        "harness_syntax_errors": harness_syntax_errors,
        "parsing_issues": parsing_issues,
        "verification_failures": verification_failures,
        "next": "evaluator"  # Always proceed to evaluator
    }

def route_from_cbmc(state):
    """Routes from CBMC to harness evaluator."""
    return "evaluator"