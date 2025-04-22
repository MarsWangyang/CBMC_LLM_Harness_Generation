"""
CBMC output parsing utilities for the harness generator.
"""
import os
import re
import glob
import json
import logging
from typing import Dict, Any, Set, List, Tuple

logger = logging.getLogger("cbmc_parser")

def read_all_coverage_data(result_base_dir):
    """
    Read all stored coverage data files and combine into a DataFrame.
    
    Args:
        result_base_dir: Base directory for results
        
    Returns:
        DataFrame with all coverage data
    """
    import polars as pl
    
    coverage_dir = os.path.join(result_base_dir, "coverage", "data")
    if not os.path.exists(coverage_dir):
        return pl.DataFrame()
    
    # Use the CSV file if it exists
    csv_path = os.path.join(coverage_dir, "coverage_metrics.csv")
    if os.path.exists(csv_path):
        try:
            return pl.read_csv(csv_path)
        except Exception as e:
            logger.error(f"Error reading coverage CSV: {str(e)}")
    
    # Fallback to reading individual JSON files
    coverage_files = glob.glob(os.path.join(coverage_dir, "*.json"))
    if not coverage_files:
        return pl.DataFrame()
    
    # Read each JSON file
    coverage_data = []
    for file_path in coverage_files:
        try:
            with open(file_path, "r") as f:
                data = json.load(f)
                coverage_data.append(data)
        except Exception as e:
            logger.error(f"Error reading coverage file {file_path}: {str(e)}")
    
    if coverage_data:
        return pl.DataFrame(coverage_data)
    else:
        return pl.DataFrame()

def extract_coverage_metrics_from_json(json_data, target_function_name, version_num, verification_status=None):
    """
    Extract coverage metrics from CBMC JSON output using the enhanced JSON structure.
    
    Args:
        json_data: The JSON data from CBMC output
        target_function_name: Name of the function being analyzed
        
    Returns:
        Dictionary with coverage metrics
    """
    # Initialize metrics
    metrics = {
        "total_reachable_lines": 0,
        "total_covered_lines": 0,
        "total_coverage_pct": 0.0,
        "func_reachable_lines": 0,
        "func_covered_lines": 0,
        "func_coverage_pct": 0.0,
        "main_total_lines": 0,
        "main_reachable_lines": 0,
        "main_uncovered_lines": 0,
        "target_total_lines": 0,
        "target_reachable_lines": 0,
        "target_uncovered_lines": 0,
        "total_combined_lines": 0,
        "reachable_combined_lines": 0,
    }
    
    # Extract target function name without file prefix
    target_function = target_function_name
    if ":" in target_function_name:
        target_function = target_function_name.split(":")[-1]
    
    try:
        # Process goals data to extract coverage metrics
        goals_dict = None
        
        # Find the goals dictionary in the JSON data
        if isinstance(json_data, list):
            for item in json_data:
                if isinstance(item, dict) and "goals" in item:
                    goals_dict = item
                    break
        elif isinstance(json_data, dict) and "goals" in json_data:
            goals_dict = json_data
        
        if goals_dict and "goals" in goals_dict:
            goals = goals_dict["goals"]
            
            # Initialize sets to track lines
            reachable_lines_main = set()
            total_lines_main = set()
            
            reachable_lines_target_function = set()
            total_lines_target_function = set()
            
            # Define harness file name pattern
            harness_file_name = f"{target_function}_harness_v{version_num}.c"
            
            for goal in goals:
                # Check for basicBlockLines field
                basic_block_lines = goal.get("basicBlockLines", {})
                
                for file_path, function_lines in basic_block_lines.items():
                    for function_name, line_ranges in function_lines.items():
                        # Parse line ranges
                        parsed_lines = parse_line_ranges(line_ranges)
                        
                        # Track lines for main function in harness file
                        if function_name == "main" and harness_file_name in file_path:
                            total_lines_main.update(parsed_lines)
                            if goal.get("status") == "satisfied":
                                reachable_lines_main.update(parsed_lines)
                        
                        # Track lines for target function
                        if function_name == target_function:
                            total_lines_target_function.update(parsed_lines)
                            if goal.get("status") == "satisfied":
                                reachable_lines_target_function.update(parsed_lines)
            
            # Calculate Total Coverage
            total_reachable_lines = len(reachable_lines_main.union(reachable_lines_target_function))
            total_possible_lines = len(total_lines_main.union(total_lines_target_function))
            
            total_coverage = total_reachable_lines / total_possible_lines if total_possible_lines > 0 else 0
            
            # Calculate Target Function Coverage
            target_function_coverage = len(reachable_lines_target_function) / len(total_lines_target_function) if len(total_lines_target_function) > 0 else 0
            
            # Calculate uncovered lines
            uncovered_lines_main = total_lines_main - reachable_lines_main
            uncovered_lines_target_function = total_lines_target_function - reachable_lines_target_function
            
            # Update metrics dictionary
            metrics["main_total_lines"] = len(total_lines_main)
            metrics["main_reachable_lines"] = len(reachable_lines_main)
            metrics["main_uncovered_lines"] = len(uncovered_lines_main)
            
            metrics["target_total_lines"] = len(total_lines_target_function)
            metrics["target_reachable_lines"] = len(reachable_lines_target_function)
            metrics["target_uncovered_lines"] = len(uncovered_lines_target_function)
            
            metrics["total_combined_lines"] = total_possible_lines
            metrics["reachable_combined_lines"] = total_reachable_lines
            
            metrics["total_reachable_lines"] = total_reachable_lines
            metrics["total_covered_lines"] = total_reachable_lines
            metrics["total_coverage_pct"] = total_coverage * 100
            
            metrics["func_reachable_lines"] = len(reachable_lines_target_function)
            metrics["func_covered_lines"] = len(reachable_lines_target_function)
            metrics["func_coverage_pct"] = target_function_coverage * 100
            
            # Log the coverage metrics clearly
            logger.info(f"Coverage Metrics for {target_function_name}:")
            logger.info(f"  Main function: {len(reachable_lines_main)}/{len(total_lines_main)} lines covered ({metrics['main_uncovered_lines']} uncovered)")
            logger.info(f"  Target function: {len(reachable_lines_target_function)}/{len(total_lines_target_function)} lines covered ({metrics['target_uncovered_lines']} uncovered)")
            logger.info(f"  Total coverage: {metrics['total_coverage_pct']:.2f}%")
            logger.info(f"  Function coverage: {metrics['func_coverage_pct']:.2f}%")
        else:
            # If we couldn't find goals, try a simplified approach that looks at the raw JSON
            # Count blocks based on the presence of patterns in the string representation
            json_str = json.dumps(json_data)
            
            # Count total blocks
            total_blocks = json_str.count('"block"') + json_str.count('"coverage"')
            satisfied_blocks = json_str.count('"status":"satisfied"') + json_str.count('status="satisfied"')
            
            # Count function-specific blocks
            target_pattern = f'"{target_function}"'
            func_blocks = json_str.count(target_pattern)
            func_satisfied = 0
            
            # Estimate satisfaction rate for function blocks based on overall rate
            if total_blocks > 0 and func_blocks > 0:
                func_satisfied = int(func_blocks * (satisfied_blocks / total_blocks))
            
            # For main function, estimate
            main_blocks = json_str.count('"main"') + json_str.count('function="main"')
            main_satisfied = 0
            
            if total_blocks > 0 and main_blocks > 0:
                main_satisfied = int(main_blocks * (satisfied_blocks / total_blocks))
            
            # Update metrics with these estimates
            metrics["main_total_lines"] = max(main_blocks, 1)
            metrics["main_reachable_lines"] = main_satisfied
            metrics["main_uncovered_lines"] = max(main_blocks - main_satisfied, 0)
            
            metrics["target_total_lines"] = max(func_blocks, 1)
            metrics["target_reachable_lines"] = func_satisfied
            metrics["target_uncovered_lines"] = max(func_blocks - func_satisfied, 0)
            
            metrics["total_combined_lines"] = max(total_blocks, 1)
            metrics["reachable_combined_lines"] = satisfied_blocks
            
            metrics["total_reachable_lines"] = max(total_blocks, 1)
            metrics["total_covered_lines"] = satisfied_blocks
            metrics["total_coverage_pct"] = (satisfied_blocks / max(total_blocks, 1)) * 100
            
            metrics["func_reachable_lines"] = max(func_blocks, 1)
            metrics["func_covered_lines"] = func_satisfied
            metrics["func_coverage_pct"] = (func_satisfied / max(func_blocks, 1)) * 100
            
            # Log the estimated coverage metrics
            logger.info(f"Estimated Coverage Metrics for {target_function_name}:")
            logger.info(f"  Main function: {metrics['main_reachable_lines']}/{metrics['main_total_lines']} lines covered (estimate)")
            logger.info(f"  Target function: {metrics['target_reachable_lines']}/{metrics['target_total_lines']} lines covered (estimate)")
            logger.info(f"  Total coverage: {metrics['total_coverage_pct']:.2f}% (estimate)")
            logger.info(f"  Function coverage: {metrics['func_coverage_pct']:.2f}% (estimate)")
        
    except Exception as e:
        logger.error(f"Error extracting coverage metrics from JSON: {str(e)}")
    
    return metrics

def parse_line_ranges(line_ranges):
    """
    Parse a string of line ranges (e.g., '20-24,27') into a set of unique line numbers.
    :param line_ranges: A string representing line ranges.
    :return: A set of unique line numbers.
    """
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

def calculate_coverage(json_file_path, target_function_name):
    """
    Calculate total coverage and target function coverage.

    :param json_file_path: Path to the JSON file.
    :param target_function_name: Name of the target function.
    :return: A dictionary containing total coverage and target function coverage.
    """
    with open(json_file_path, 'r') as file:
        data = json.load(file)
    
    # Ensure data is a list
    if not isinstance(data, list):
        raise ValueError("Expected JSON root structure to be a list.")
    
    # Find the dictionary containing 'goals'
    goals_dict = None
    for item in data:
        if isinstance(item, dict) and "goals" in item:
            goals_dict = item
            break
    
    if not goals_dict:
        raise ValueError("No dictionary with 'goals' key found in the JSON file.")

    # Extract goals
    goals = goals_dict.get("goals", [])
    
    # Initialize sets to track lines
    reachable_lines_main = set()
    total_lines_main = set()
    
    reachable_lines_target_function = set()
    total_lines_target_function = set()
    
    # Define harness file name pattern
    harness_file_name = f"{target_function_name}_harness.c"
    
    for goal in goals:  # Iterate over each goal in the 'goals' list
        basic_block_lines = goal.get("basicBlockLines", {})
        
        for file_path, function_lines in basic_block_lines.items():
            for function_name, line_ranges in function_lines.items():
                parsed_lines = parse_line_ranges(line_ranges)
                
                # Track lines for main function in harness file
                if function_name == "main" and harness_file_name in file_path:
                    total_lines_main.update(parsed_lines)
                    if goal.get("status") == "satisfied":
                        reachable_lines_main.update(parsed_lines)
                
                # Track lines for target function
                if function_name == target_function_name:
                    total_lines_target_function.update(parsed_lines)
                    if goal.get("status") == "satisfied":
                        reachable_lines_target_function.update(parsed_lines)
    
    # Calculate Total Coverage
    total_reachable_lines = len(reachable_lines_main.union(reachable_lines_target_function))
    total_possible_lines = len(total_lines_main.union(total_lines_target_function))
    
    total_coverage = total_reachable_lines / total_possible_lines if total_possible_lines > 0 else 0
    
    # Calculate Target Function Coverage
    target_function_coverage = len(reachable_lines_target_function) / len(total_lines_target_function) if len(total_lines_target_function) > 0 else 0
    
    # Calculate uncovered lines
    uncovered_lines_main = total_lines_main - reachable_lines_main
    uncovered_lines_target_function = total_lines_target_function - reachable_lines_target_function
    
    # Print debug information about lines
    print(f"Total Lines (Main Function): {len(total_lines_main)}")
    print(f"Reachable Lines (Main Function): {len(reachable_lines_main)}")
    print(f"Uncovered Lines (Main Function): {len(uncovered_lines_main)}")
    
    print(f"Total Lines (Target Function): {len(total_lines_target_function)}")
    print(f"Reachable Lines (Target Function): {len(reachable_lines_target_function)}")
    print(f"Uncovered Lines (Target Function): {len(uncovered_lines_target_function)}")
    
    print(f"Total Lines (Harness + Target Function): {total_possible_lines}")
    print(f"Reachable Lines (Harness + Target Function): {total_reachable_lines}")
    
    # Print detailed sets of covered and uncovered lines
    print(f"Covered Lines (Main Function): {sorted(reachable_lines_main)}")
    print(f"Uncovered Lines (Main Function): {sorted(uncovered_lines_main)}")
    
    print(f"Covered Lines (Target Function): {sorted(reachable_lines_target_function)}")
    print(f"Uncovered Lines (Target Function): {sorted(uncovered_lines_target_function)}")
    
    return {
        "Total Coverage": round(total_coverage * 100, 2),
        "Target Function Coverage": round(target_function_coverage * 100, 2),
        # Add detailed metrics
        "main_total_lines": len(total_lines_main),
        "main_reachable_lines": len(reachable_lines_main),
        "main_uncovered_lines": len(uncovered_lines_main),
        "target_total_lines": len(total_lines_target_function),
        "target_reachable_lines": len(reachable_lines_target_function),
        "target_uncovered_lines": len(uncovered_lines_target_function),
        "total_combined_lines": total_possible_lines,
        "reachable_combined_lines": total_reachable_lines
    }

def process_cbmc_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """
    Process CBMC output and extract structured error information.
    Prioritizes STDERR over STDOUT for error identification and uses precise line number tracing.
    
    Args:
        stdout: The standard output from CBMC
        stderr: The standard error from CBMC
        
    Returns:
        A dictionary with structured information about the verification results
    """
    result = {
        "verification_status": "UNKNOWN",
        "message": "",
        "suggestions": "",
        "error_categories": [],
        "error_locations": {},
        "error_messages": [],
        "has_preprocessing_error": False,
        "has_parsing_error": False,
        "missing_functions": set(),
        "verification_failures": [],
        "reachable_lines": 0,
        "covered_lines": 0,
        "coverage_pct": 0.0,
        "func_reachable_lines": 0,  # Initialize function-specific metrics
        "func_covered_lines": 0,
        "func_coverage_pct": 0.0,
        "main_total_lines": 0,      # New enhanced metrics
        "main_reachable_lines": 0,
        "main_uncovered_lines": 0,
        "target_total_lines": 0,
        "target_reachable_lines": 0,
        "target_uncovered_lines": 0,
        "total_combined_lines": 0,
        "reachable_combined_lines": 0,
        "errors": 0,
        "failure_count": 0,         # Track number of FAILURE messages
        "error_count": 0,           # Track number of ERROR messages
        "has_redeclaration_error": False,  # Track redeclaration errors specifically
        "redeclared_symbols": []    # List of redeclared symbols
    }
    
    # IMPORTANT: Ensure stderr is preserved in the result for downstream processing
    result["stderr"] = stderr
    
    # First, check if we have any content in stderr (prioritize stderr)
    has_stderr_content = stderr.strip() != ""
    
    # Extract line-specific errors from stderr first
    stderr_error_locations = {}
    stderr_error_messages = []
    stderr_redeclaration_errors = []
    missing_constants = []  # Track missing constants (uppercase identifiers)
    
    if has_stderr_content:
        # Look for specific error patterns in stderr with line numbers
        for line in stderr.split('\n'):
            # Skip warning lines unless they contain critical information
            if 'warning:' in line.lower() and not any(critical in line.lower() 
                                                     for critical in ['pointer', 'memory', 'null', 'invalid', 'error']):
                continue
                
            # Check for redeclaration errors
            if 'redeclaration' in line.lower():
                result["has_redeclaration_error"] = True
                stderr_redeclaration_errors.append(line.strip())
                
                # Extract the redeclared symbol
                redecl_match = re.search(r"redeclaration of '([^']+)'", line)
                if redecl_match:
                    redecl_symbol = redecl_match.group(1)
                    if redecl_symbol not in result["redeclared_symbols"]:
                        result["redeclared_symbols"].append(redecl_symbol)
            
            # Check specifically for missing constants (all uppercase identifiers)
            missing_const_match = re.search(r"'([A-Z][A-Z0-9_]*)'.*(undeclared|undefined|not declared)", line)
            if missing_const_match:
                missing_constant = missing_const_match.group(1)
                if missing_constant not in missing_constants:
                    missing_constants.append(missing_constant)
                    
            # Look for error message patterns with line numbers
            if 'error:' in line or ('warning:' in line and any(critical in line.lower() 
                                                             for critical in ['pointer', 'memory', 'null', 'invalid'])):
                stderr_error_messages.append(line.strip())
                
                # Extract file and line information using improved regex pattern
                # This handles both "file.c:123:" and "file.c:123:12:" formats
                loc_match = re.search(r'([^:]+):(\d+)(?::\d+)?:', line)
                if loc_match:
                    file_name = loc_match.group(1)
                    line_num = int(loc_match.group(2))
                    
                    # Add to location tracking
                    if file_name not in stderr_error_locations:
                        stderr_error_locations[file_name] = []
                    if line_num not in stderr_error_locations[file_name]:
                        stderr_error_locations[file_name].append(line_num)
    
    # Check for preprocessing errors, parsing errors, or other critical errors in stderr
    if has_stderr_content and ("PARSING ERROR" in stderr or "preprocessing failed" in stderr.lower() 
                              or "error generated" in stderr.lower() or "error:" in stderr.lower() 
                              or "undefined reference" in stderr.lower()):
        result["verification_status"] = "FAILED"
        result["has_preprocessing_error"] = True
        result["message"] = "Preprocessing error detected"
        
        # Add missing constants to result
        if missing_constants:
            result["missing_constants"] = missing_constants
            result["has_missing_constants"] = True
        
        # Extract specific error messages from stderr
        if stderr_error_messages:  # Use the already extracted error messages
            error_description = "; ".join(stderr_error_messages[:3])
            result["message"] = f"PREPROCESSING ERROR: {error_description}"
            result["suggestions"] = "Fix syntax errors in the harness or source code"
            result["error_messages"] = stderr_error_messages
        else:
            # Add generic error message if no specific messages were found
            result["message"] = "PREPROCESSING ERROR: GCC preprocessing failed - check for syntax errors"
            result["suggestions"] = "Fix syntax errors and ensure all necessary includes are available"
        
        # Use the already extracted error locations
        if stderr_error_locations:
            result["error_locations"] = stderr_error_locations
        
        # Extract macro-related errors specifically
        macro_errors = []
        for line in stderr.split('\n'):
            if 'macro' in line.lower() and ('error' in line.lower() or 'defined' in line.lower()):
                macro_errors.append(line.strip())
                # Try to extract the macro name
                macro_match = re.search(r"macro '([^']+)'", line)
                if macro_match:
                    macro_name = macro_match.group(1)
                    macro_errors.append(f"Problematic macro: {macro_name}")
        
        # Add specific macro errors if found
        if macro_errors:
            error_description = "Macro definition error: " + "; ".join(macro_errors[:2])
            result["message"] = f"PREPROCESSING ERROR: {error_description}"
            result["suggestions"] = "Fix macro definitions and ensure they are properly defined"
        
        return result
    
    # Check for successful verification 
    if "VERIFICATION SUCCESSFUL" in stdout:
        result["verification_status"] = "SUCCESS"
        result["message"] = "Verification successful"
        return result
    
    # If we've gotten this far, it's a verification failure not a preprocessing error
    result["verification_status"] = "FAILED" 
    
    # Extract all failure information
    failure_lines = []
    failure_categories = set()
    failure_locations = {}
    failure_count = 0
    error_count = 0
    
    # First check if we have stderr_error_locations (from line-specific errors in stderr)
    # and use those as our primary error locations
    if stderr_error_locations:
        failure_locations = stderr_error_locations.copy()
    
    # Process each line of stdout for detailed failure information
    for line in stdout.split('\n'):
        # Count FAILURE occurrences
        if "FAILURE" in line:
            failure_count += 1
            
        # Count ERROR occurrences 
        if "ERROR" in line:
            error_count += 1
            
        if "FAILURE" in line or "FAILED" in line:
            # Skip unwinding assertions as they're often not relevant to core bugs
            if "unwinding assertion" in line:
                continue
                
            failure_lines.append(line.strip())
            
            # Parse and categorize failure type
            failure_category = "general"  # Default category
            
            if "[memory]" in line or "memory-leak" in line or "dynamic memory" in line:
                failure_category = "memory_leak"
                failure_categories.add("memory_leak")
            elif "[pointer]" in line or "dereference failure" in line or "NULL pointer" in line:
                failure_category = "null_pointer" 
                failure_categories.add("null_pointer")
            elif "[array]" in line or "array bounds" in line:
                failure_category = "array_bounds"
                failure_categories.add("array_bounds")
            elif "[arithmetic]" in line or "division by zero" in line:
                failure_category = "division_by_zero"
                failure_categories.add("division_by_zero")
            elif "[overflow]" in line or "overflow" in line:
                failure_category = "arithmetic_overflow"
                failure_categories.add("arithmetic_overflow")
            elif "[assertion]" in line or "__CPROVER_assert" in line:
                failure_category = "assertion"
                failure_categories.add("assertion")
            
            # Extract location information if available
            loc_match = re.search(r'file ([^:]+):(\d+)', line)
            if loc_match:
                file_name = loc_match.group(1)
                line_num = int(loc_match.group(2))
                
                # Add to location tracking
                if file_name not in failure_locations:
                    failure_locations[file_name] = []
                if line_num not in failure_locations[file_name]:
                    failure_locations[file_name].append(line_num)
    
    # Extract missing function bodies and constants
    missing_functions = set()
    for line in stdout.split('\n'):
        if "no body for callee" in line:
            match = re.search(r'no body for callee (\w+)', line)
            if match:
                func_name = match.group(1)
                missing_functions.add(func_name)
        
        # Check for missing constants in stdout too (sometimes they appear here)
        missing_const_match = re.search(r"'([A-Z][A-Z0-9_]*)'.*(undeclared|undefined|not declared)", line)
        if missing_const_match:
            missing_constant = missing_const_match.group(1)
            if missing_constant not in missing_constants:
                missing_constants.append(missing_constant)
    
    # Parse coverage information - extract lines for analysis
    # Extract lines of code information from coverage output
    line_info_pattern = r'line (\d+) function ([^,]+), file ([^,]+)'
    line_matches = re.finditer(line_info_pattern, stdout)
    
    # Initialize coverage tracking
    main_lines = set()
    main_covered = set()
    target_lines = set()
    target_covered = set()
    
    # Process all line matches
    for match in line_matches:
        line_num = int(match.group(1))
        func_name = match.group(2)
        file_name = match.group(3)
        
        # Check coverage status
        is_covered = False
        # Look at the preceding text for coverage status
        start_pos = max(0, match.start() - 100)
        preceding_text = stdout[start_pos:match.start()]
        if "SATISFIED" in preceding_text or "satisfied" in preceding_text.lower():
            is_covered = True
        
        # Categorize by function
        if func_name == "main":
            main_lines.add(line_num)
            if is_covered:
                main_covered.add(line_num)
        else:
            # Assume other functions are target functions
            target_lines.add(line_num)
            if is_covered:
                target_covered.add(line_num)
    
    # Update coverage metrics
    result["main_total_lines"] = len(main_lines)
    result["main_reachable_lines"] = len(main_covered)
    result["main_uncovered_lines"] = len(main_lines) - len(main_covered)
    
    result["target_total_lines"] = len(target_lines)
    result["target_reachable_lines"] = len(target_covered)
    result["target_uncovered_lines"] = len(target_lines) - len(target_covered)
    
    result["total_combined_lines"] = len(main_lines) + len(target_lines)
    result["reachable_combined_lines"] = len(main_covered) + len(target_covered)
    
    # Also set old metrics for backward compatibility
    result["reachable_lines"] = result["total_combined_lines"]
    result["covered_lines"] = result["reachable_combined_lines"]
    
    if result["total_combined_lines"] > 0:
        result["coverage_pct"] = (result["reachable_combined_lines"] / result["total_combined_lines"]) * 100
    
    result["func_reachable_lines"] = result["target_total_lines"]
    result["func_covered_lines"] = result["target_reachable_lines"]
    
    if result["target_total_lines"] > 0:
        result["func_coverage_pct"] = (result["target_reachable_lines"] / result["target_total_lines"]) * 100
    
    # Add the failure and error counts to the result
    result["failure_count"] = failure_count
    result["error_count"] = error_count
    
    # Add missing constants to result - do this before setting other categories
    if missing_constants:
        result["missing_constants"] = missing_constants
        result["has_missing_constants"] = True
        # Add to error categories
        if "missing_constants" not in failure_categories:
            failure_categories.add("missing_constants")

    # Count errors and set suggestions based on categories
    if failure_categories:
        result["error_categories"] = list(failure_categories)
        result["verification_failures"] = list(failure_categories)
        
        # Set message and suggestions based on primary failure category
        if "missing_constants" in failure_categories and len(failure_categories) == 1:
            # If the only issue is missing constants, make that the primary message
            result["message"] = f"VERIFICATION FAILED: Missing constants detected: {', '.join(missing_constants)}"
            result["suggestions"] = "Add mock definitions for these constants at the top of your harness"
        elif "memory_leak" in failure_categories:
            result["message"] = "VERIFICATION FAILED: Memory leak detected"
            result["suggestions"] = "Ensure all allocated memory is freed in all execution paths"
        elif "null_pointer" in failure_categories:
            result["message"] = "VERIFICATION FAILED: Null pointer dereference detected"
            result["suggestions"] = "Add null pointer checks before dereferencing pointers"
        elif "array_bounds" in failure_categories:
            result["message"] = "VERIFICATION FAILED: Array bounds violation detected"
            result["suggestions"] = "Add bounds checking for array accesses"
        elif "division_by_zero" in failure_categories:
            result["message"] = "VERIFICATION FAILED: Division by zero detected"
            result["suggestions"] = "Add checks to ensure divisors are non-zero"
        elif "arithmetic_overflow" in failure_categories:
            result["message"] = "VERIFICATION FAILED: Arithmetic overflow detected"
            result["suggestions"] = "Add checks to prevent integer overflow"
        elif "assertion" in failure_categories:
            result["message"] = "VERIFICATION FAILED: Assertion failure detected"
            result["suggestions"] = "Fix the conditions that cause the assertion to fail"
        else:
            result["message"] = "VERIFICATION FAILED: General verification error"
            result["suggestions"] = "Review the verification failures for more details"
    elif missing_functions:
        result["message"] = f"VERIFICATION FAILED: Missing function bodies for {len(missing_functions)} functions"
        result["suggestions"] = "Implement or stub the missing functions"
        result["missing_functions"] = missing_functions
    else:
        result["message"] = "VERIFICATION FAILED: Unspecified verification error"
        result["suggestions"] = "Review the full verification output for details"
    
    # Count total errors
    total_errors = sum(len(lines) for lines in failure_locations.values()) if failure_locations else len(failure_lines)
    result["errors"] = total_errors
    
    # Add error locations
    if failure_locations:
        result["error_locations"] = failure_locations
    
    return result

def extract_function_name_from_result(result: Dict[str, Any]) -> str:
    """
    Extract the function name from the result dictionary.
    
    Args:
        result: CBMC result dictionary
        
    Returns:
        Function name or empty string if not found
    """
    # Try to extract from function field
    if "function" in result:
        # Handle cases where function might be a full path
        func = result["function"]
        if ":" in func:
            return func.split(":")[-1]
        return func
    
    # Try to extract from error locations
    if "error_locations" in result:
        error_locs = result["error_locations"]
        for file_name in error_locs:
            # Try to extract function name from file name
            if "_" in file_name:
                parts = file_name.split("_")
                for part in parts:
                    # Look for likely function names (not common words)
                    if part and part not in ["file", "line", "error", "warning"]:
                        return part
    
    # Try other fields
    for field in ["message", "suggestions"]:
        if field in result:
            # Look for "function X" pattern
            match = re.search(r'function\s+(\w+)', result[field])
            if match:
                return match.group(1)
    
    return ""

def format_error_for_feedback(result: Dict[str, Any]) -> str:
    """
    Format the error information into a concise feedback string for the generator.
    
    Args:
        result: The processed CBMC output result
        
    Returns:
        A formatted string with error feedback
    """
    feedback = []
    
    # Add overall status and message - handle both key name variations
    status = result.get("verification_status", result.get("status", "UNKNOWN"))
    message = result.get("message", "No message provided")
    
    feedback.append(f"Status: {status}")
    feedback.append(f"Message: {message}")
    
    # Add specific feedback based on error type
    if result.get("has_preprocessing_error", False):
        feedback.append("\nPreprocessing Error Details:")
        for msg in result.get("error_messages", [])[:5]:  # Limit to first 5 for clarity
            feedback.append(f"- {msg}")
    
    # Add missing functions feedback
    missing_functions = result.get("missing_functions", [])
    if missing_functions:
        feedback.append("\nMissing Function Bodies:")
        for func in missing_functions:
            feedback.append(f"- {func}")
        
        feedback.append("\nSuggestions for missing functions:")
        feedback.append("1. Add the function implementations to your harness")
        feedback.append("2. Create minimal stub implementations that satisfy CBMC verification")
        feedback.append("3. Avoid calling these functions in your test if possible")
    
    # Add error categories feedback
    error_categories = result.get("error_categories", [])
    if error_categories:
        feedback.append("\nError Categories:")
        for category in error_categories:
            feedback.append(f"- {category}")
    
    # Add error locations if available
    error_locations = result.get("error_locations", {})
    if error_locations:
        feedback.append("\nError Locations:")
        for file, lines in error_locations.items():
            feedback.append(f"- {file}: lines {', '.join(str(l) for l in sorted(lines))}")
    
    # Add specific suggestions
    suggestions = result.get("suggestions", "")
    if suggestions:
        feedback.append(f"\nSuggestions: {suggestions}")
    
    # Add enhanced coverage metrics
    feedback.append("\nEnhanced Coverage Metrics:")
    
    # Main function metrics
    main_total = result.get("main_total_lines", 0)
    main_reached = result.get("main_reachable_lines", 0)
    main_uncovered = result.get("main_uncovered_lines", 0)
    
    feedback.append("\nMain Function Coverage:")
    feedback.append(f"- Total lines: {main_total}")
    feedback.append(f"- Reachable lines: {main_reached}")
    feedback.append(f"- Uncovered lines: {main_uncovered}")
    if main_total > 0:
        main_coverage = (main_reached / main_total) * 100
        feedback.append(f"- Coverage: {main_coverage:.2f}%")
    
    # Target function metrics
    target_total = result.get("target_total_lines", 0)
    target_reached = result.get("target_reachable_lines", 0)
    target_uncovered = result.get("target_uncovered_lines", 0)
    
    feedback.append("\nTarget Function Coverage:")
    feedback.append(f"- Total lines: {target_total}")
    feedback.append(f"- Reachable lines: {target_reached}")
    feedback.append(f"- Uncovered lines: {target_uncovered}")
    if target_total > 0:
        target_coverage = (target_reached / target_total) * 100
        feedback.append(f"- Coverage: {target_coverage:.2f}%")
    
    # Combined metrics
    combined_total = result.get("total_combined_lines", 0)
    combined_reached = result.get("reachable_combined_lines", 0)
    if combined_total > 0:
        combined_coverage = (combined_reached / combined_total) * 100
        feedback.append(f"\nCombined Coverage: {combined_coverage:.2f}%")
    
    return "\n".join(feedback)

def parse_line_specific_errors(cbmc_stderr: str, cbmc_stdout: str, harness_code: str) -> Dict[str, Any]:
    """
    Parse CBMC error messages to extract line-specific errors and suggest fixes.
    
    Args:
        cbmc_stderr: Standard error output from CBMC
        cbmc_stdout: Standard output from CBMC
        harness_code: The harness code being verified
        
    Returns:
        Dictionary with line-specific errors and suggested fixes
    """
    result = {
        "error_lines": {},  # Maps line numbers to error messages
        "suggested_fixes": {},  # Maps line numbers to suggested fixes
        "error_types": {},  # Maps line numbers to error types
        "code_snippets": {}  # Maps line numbers to relevant code snippets
    }
    
    # Initialize sets to track line numbers
    syntax_error_lines = set()
    null_pointer_lines = set()
    memory_leak_lines = set()
    array_bounds_lines = set()
    division_by_zero_lines = set()
    redeclaration_lines = set()
    
    # First process stderr for more detailed error messages
    if cbmc_stderr:
        for line in cbmc_stderr.split('\n'):
            # Look for lines with error or critical warnings
            if 'error:' in line or ('warning:' in line and any(critical in line.lower() 
                                                         for critical in ['pointer', 'memory', 'null', 'invalid'])):
                # Extract file and line information using improved regex
                loc_match = re.search(r'([^:]+):(\d+)(?::\d+)?:', line)
                if loc_match:
                    file_name = loc_match.group(1)
                    line_num = int(loc_match.group(2))
                    
                    # Extract the actual error message
                    error_msg = line.split(':', 3)[-1].strip() if len(line.split(':', 3)) >= 4 else line
                    
                    # Skip if not related to harness files
                    if "harness" not in file_name.lower() and "_harness_" not in file_name.lower():
                        continue
                    
                    # Store the error
                    if line_num not in result["error_lines"]:
                        result["error_lines"][line_num] = []
                    result["error_lines"][line_num].append(error_msg)
                    
                    # Categorize the error type
                    error_type = "syntax"  # Default type
                    
                    # Check for specific error types
                    if "redeclaration" in line.lower() or "redefinition" in line.lower():
                        error_type = "redeclaration"
                        redeclaration_lines.add(line_num)
                    elif "null" in line.lower() or "nullptr" in line.lower():
                        error_type = "null_pointer"
                        null_pointer_lines.add(line_num)
                    elif "memory" in line.lower() and ("leak" in line.lower() or "free" in line.lower()):
                        error_type = "memory_leak"
                        memory_leak_lines.add(line_num)
                    elif "bounds" in line.lower() or "index" in line.lower() or "buffer" in line.lower():
                        error_type = "array_bounds"
                        array_bounds_lines.add(line_num)
                    elif "division" in line.lower() and "zero" in line.lower():
                        error_type = "division_by_zero"
                        division_by_zero_lines.add(line_num)
                    
                    # Store the error type
                    result["error_types"][line_num] = error_type
                    
                    # Add suggested fix based on error type
                    fix = ""
                    if error_type == "redeclaration":
                        if "struct" in line.lower() or "redefinition of body" in line.lower() or "redefinition of" in line.lower():
                            fix = "NEVER redefine structs. Remove this struct definition entirely and use the one from the header."
                        else:
                            fix = "Remove this declaration or add 'extern' if it's a function declaration."
                    elif error_type == "null_pointer":
                        fix = "Add null check before using this pointer: if (ptr != NULL) { ... }"
                    elif error_type == "memory_leak":
                        fix = "Ensure all allocated memory is freed: free(ptr);"
                    elif error_type == "array_bounds":
                        fix = "Add bounds check: __CPROVER_assume(index < array_size);"
                    elif error_type == "division_by_zero":
                        fix = "Add zero check: __CPROVER_assume(divisor != 0);"
                    
                    # Store the suggested fix
                    result["suggested_fixes"][line_num] = fix
                    
                    # Get code snippet from the harness code
                    harness_lines = harness_code.strip().split('\n')
                    line_index = line_num - 1  # Convert to 0-based index
                    
                    if 0 <= line_index < len(harness_lines):
                        # Get context lines (2 before and 2 after)
                        start_ctx = max(0, line_index - 2)
                        end_ctx = min(len(harness_lines), line_index + 3)
                        
                        # Extract the context lines
                        context_lines = []
                        for ctx_idx in range(start_ctx, end_ctx):
                            prefix = "→ " if ctx_idx == line_index else "  "
                            context_lines.append(f"{prefix}Line {ctx_idx+1}: {harness_lines[ctx_idx].strip()}")
                        
                        # Store the code snippet
                        result["code_snippets"][line_num] = "\n".join(context_lines)
    
    # Now process stdout for additional errors
    if cbmc_stdout:
        for line in cbmc_stdout.split('\n'):
            if "FAILED" in line or "FAILURE" in line:
                # Extract file and line information
                loc_match = re.search(r'file ([^:]+):(\d+)', line)
                if loc_match:
                    file_name = loc_match.group(1)
                    line_num = int(loc_match.group(2))
                    
                    # Skip if not related to harness files
                    if "harness" not in file_name.lower() and "_harness_" not in file_name.lower():
                        continue
                    
                    # Skip if we already have this error from stderr (higher precedence)
                    if line_num in result["error_lines"]:
                        continue
                    
                    # Store the error
                    if line_num not in result["error_lines"]:
                        result["error_lines"][line_num] = []
                    result["error_lines"][line_num].append(line.strip())
                    
                    # Try to categorize the error type
                    error_type = "general"  # Default type
                    
                    # Check for specific error types
                    if "[memory]" in line or "memory-leak" in line:
                        error_type = "memory_leak"
                        memory_leak_lines.add(line_num)
                    elif "[pointer]" in line or "NULL pointer" in line:
                        error_type = "null_pointer"
                        null_pointer_lines.add(line_num)
                    elif "[array]" in line or "array bounds" in line:
                        error_type = "array_bounds"
                        array_bounds_lines.add(line_num)
                    elif "[arithmetic]" in line or "division by zero" in line:
                        error_type = "division_by_zero"
                        division_by_zero_lines.add(line_num)
                    
                    # Store the error type
                    result["error_types"][line_num] = error_type
                    
                    # Add suggested fix based on error type
                    fix = ""
                    if error_type == "memory_leak":
                        fix = "Ensure all allocated memory is freed: free(ptr);"
                    elif error_type == "null_pointer":
                        fix = "Add null check before using this pointer: if (ptr != NULL) { ... }"
                    elif error_type == "array_bounds":
                        fix = "Add bounds check: __CPROVER_assume(index < array_size);"
                    elif error_type == "division_by_zero":
                        fix = "Add zero check: __CPROVER_assume(divisor != 0);"
                    elif error_type == "general":
                        fix = "Review this line for potential errors."
                    
                    # Store the suggested fix
                    result["suggested_fixes"][line_num] = fix
                    
                    # Get code snippet from the harness code
                    harness_lines = harness_code.strip().split('\n')
                    line_index = line_num - 1  # Convert to 0-based index
                    
                    if 0 <= line_index < len(harness_lines):
                        # Get context lines (2 before and 2 after)
                        start_ctx = max(0, line_index - 2)
                        end_ctx = min(len(harness_lines), line_index + 3)
                        
                        # Extract the context lines
                        context_lines = []
                        for ctx_idx in range(start_ctx, end_ctx):
                            prefix = "→ " if ctx_idx == line_index else "  "
                            context_lines.append(f"{prefix}Line {ctx_idx+1}: {harness_lines[ctx_idx].strip()}")
                        
                        # Store the code snippet
                        result["code_snippets"][line_num] = "\n".join(context_lines)
    
    # Add code pattern suggestions for specific error types
    for line_num, error_type in result["error_types"].items():
        if error_type == "redeclaration" and ("struct" in result.get("error_lines", {}).get(line_num, [""])[0].lower() 
                                         or "redefinition of body" in result.get("error_lines", {}).get(line_num, [""])[0].lower()):
            pattern = """
// STRUCT REDEFINITION ERROR:
// NEVER redefine structs that are in headers. Instead:

// 1. Include the header that defines the struct
#include "your_header.h"

// 2. Use the struct directly WITHOUT redefining it
struct MyStruct* ptr;  // Just declare a pointer or variable

// WRONG - NEVER DO THIS:
// struct MyStruct {  // This causes a redefinition error
//     int field1;    // Even if identical to the header definition
//     char field2;
// };

// RIGHT - DO THIS:
// Simply use the struct that's already defined in the header
"""
            if "code_pattern" not in result:
                result["code_pattern"] = {}
            result["code_pattern"]["struct_redefinition"] = pattern
            
        elif error_type == "null_pointer":
            pattern = """
// NULL pointer check pattern:
if (ptr != NULL) {
    // Use ptr only inside this block
    result = ptr->field;  // Safe to dereference
} else {
    // Handle NULL case
    return ERROR_CODE;
}

// Alternatively, use CBMC assume:
__CPROVER_assume(ptr != NULL);
result = ptr->field;  // Now safe because CBMC knows ptr is not NULL
"""
            if "code_pattern" not in result:
                result["code_pattern"] = {}
            result["code_pattern"][error_type] = pattern
        
        elif error_type == "memory_leak":
            pattern = """
// Memory management pattern:
void* buffer = malloc(size);
__CPROVER_assume(buffer != NULL);
// ... use buffer ...
free(buffer);  // Always free allocated memory at the end

// OR use stack allocation instead:
char static_buffer[SIZE];  // No need for malloc/free
"""
            if "code_pattern" not in result:
                result["code_pattern"] = {}
            result["code_pattern"][error_type] = pattern
        
        elif error_type == "array_bounds":
            pattern = """
// Array bounds check pattern:
size_t index = nondet_size_t();
__CPROVER_assume(index < array_size);  // Ensure index is within bounds
array[index] = value;  // Safe array access
"""
            if "code_pattern" not in result:
                result["code_pattern"] = {}
            result["code_pattern"][error_type] = pattern
        
        elif error_type == "division_by_zero":
            pattern = """
// Division by zero check pattern:
int divisor = nondet_int();
__CPROVER_assume(divisor != 0);  // Ensure divisor is not zero
result = value / divisor;  // Safe division
"""
            if "code_pattern" not in result:
                result["code_pattern"] = {}
            result["code_pattern"][error_type] = pattern
    
    return result

def generate_improvement_recommendation(harness_code: str, func_code: str, cbmc_result: Dict[str, Any]) -> str:
    """
    Generate a targeted improvement recommendation based on CBMC results.
    Includes specialized guidance for timeout issues and other performance problems.
    
    Args:
        harness_code: The current harness code
        func_code: The original function code
        cbmc_result: The processed CBMC output result
        
    Returns:
        A detailed improvement recommendation
    """
    try:
        # Parse line-specific errors
        stderr = cbmc_result.get("stderr", "")
        stdout = cbmc_result.get("stdout", "")
        line_specific_errors = parse_line_specific_errors(stderr, stdout, harness_code)
        
        # Check for missing constants (uppercase identifiers) and add mock suggestions
        missing_constants = cbmc_result.get("missing_constants", [])
        has_missing_constants = cbmc_result.get("has_missing_constants", False)
        
        # Start with the error feedback
        recommendation = [format_error_for_feedback(cbmc_result)]
        
        # Add missing constants section if needed
        if has_missing_constants or missing_constants:
            recommendation.append(f"\n== MISSING CONSTANTS DETECTED ==")
            
            # List all identified missing constants
            if missing_constants:
                recommendation.append("The following constants/macros are undefined:")
                for constant in missing_constants:
                    recommendation.append(f"- '{constant}'")
                
            recommendation.append("\nTo fix these missing constants:")
            recommendation.append("1. These are likely project-specific constants that need to be defined")
            recommendation.append("2. You should add mock definitions for these constants in your harness")
            recommendation.append("3. Place all mock constants in a dedicated section at the top of your harness:")
            recommendation.append("```c")
            recommendation.append("/* BEGIN MOCK CONSTANTS */")
            
            # Add suggested mocks for common constant types
            for constant in missing_constants:
                if "MAX" in constant or "SIZE" in constant or "LENGTH" in constant or "LIMIT" in constant:
                    recommendation.append(f"#define {constant} 128  // Mock value for size/length constant")
                elif "MIN" in constant:
                    recommendation.append(f"#define {constant} 1    // Mock value for minimum constant")
                elif "TIMEOUT" in constant or "DELAY" in constant:
                    recommendation.append(f"#define {constant} 60   // Mock value for time constant in seconds")
                elif "ENABLED" in constant or "DISABLED" in constant:
                    recommendation.append(f"#define {constant} 1    // Mock value for feature flag (1=enabled, 0=disabled)")
                elif "FLAG" in constant or "OPTION" in constant:
                    recommendation.append(f"#define {constant} 1    // Mock value for flag/option")
                else:
                    recommendation.append(f"#define {constant} 42   // Mock value for general constant")
            
            recommendation.append("/* END MOCK CONSTANTS */")
            recommendation.append("```")
            recommendation.append("\nAdjust these values based on how they're used in the function.")
        
        # Add line-specific error information if available
        if line_specific_errors and line_specific_errors["error_lines"]:
            recommendation.append("\n\n== LINE-SPECIFIC ERROR ANALYSIS ==")
            recommendation.append("The following line numbers in your harness have specific errors that need to be fixed:")
            
            # Sort the errors by line number
            for line_num in sorted(line_specific_errors["error_lines"].keys()):
                error_msgs = line_specific_errors["error_lines"][line_num]
                error_type = line_specific_errors["error_types"].get(line_num, "unknown")
                fix = line_specific_errors["suggested_fixes"].get(line_num, "Review this line for errors.")
                code_snippet = line_specific_errors["code_snippets"].get(line_num, "")
                
                # Add the error information
                recommendation.append(f"\n🔴 Line {line_num} - {error_type.upper()} ERROR:")
                recommendation.append(f"  Error: {'; '.join(error_msgs)}")
                recommendation.append(f"  Suggested Fix: {fix}")
                
                # Add the code snippet
                if code_snippet:
                    recommendation.append("\n  Code Context:")
                    recommendation.append(f"{code_snippet}")
            
            # Add code patterns for common error types
            if "code_pattern" in line_specific_errors:
                recommendation.append("\n== CODE PATTERNS FOR FIXING ERRORS ==")
                
                for error_type, pattern in line_specific_errors["code_pattern"].items():
                    recommendation.append(f"\nPattern for {error_type.replace('_', ' ')} errors:")
                    recommendation.append("```c")
                    recommendation.append(pattern.strip())
                    recommendation.append("```")
                    
            # Add overall guidance
            recommendation.append("\n== HOW TO FIX THESE ERRORS ==")
            recommendation.append("1. Start with the highest priority errors (syntax errors, redeclarations)")
            recommendation.append("2. Fix each error by applying the suggested fix to the specific line")
            recommendation.append("3. Use the provided code patterns as templates for your fixes")
            recommendation.append("4. After fixing all line-specific errors, run verification again")
            recommendation.append("5. If you have memory leaks, make sure EVERY malloc has a corresponding free")
            recommendation.append("6. If you have null pointer errors, add checks before EVERY pointer dereference")
        
        # Check for persistent errors and add specific guidance when errors repeat
        persistent_errors = cbmc_result.get("persistent_errors", {})
        
        # Also look for any special persistence flags
        special_persistence_flags = {}
        for key in cbmc_result.keys():
            if key.startswith("persistence_"):
                error_type = key.replace("persistence_", "")
                special_persistence_flags[error_type] = cbmc_result[key]
        
        # Get overall persistence count
        max_persistence = 0
        for error_type, count in persistent_errors.items():
            max_persistence = max(max_persistence, count)
        for error_type, count in special_persistence_flags.items():
            max_persistence = max(max_persistence, count)
        
        # If we have persistent errors OR special persistence flags
        if persistent_errors or special_persistence_flags:
            recommendation.append("\n== PERSISTENT ERRORS DETECTED ==")
            recommendation.append("The following errors have persisted across multiple versions:")
            
            # List persistent errors from both sources
            if persistent_errors:
                for error, count in persistent_errors.items():
                    recommendation.append(f"- '{error}' has persisted for {count} version(s)")
            
            for error_type, count in special_persistence_flags.items():
                if count > 1 and error_type not in persistent_errors:
                    recommendation.append(f"- '{error_type}' has persisted for {count} version(s)")
            
            # Adjust the severity of the recommendation based on persistence count
            if max_persistence >= 4:
                recommendation.append("\n⚠️ CRITICAL PERSISTENT ERRORS! A COMPLETE REDESIGN IS MANDATORY! ⚠️")
            elif max_persistence >= 2:
                recommendation.append("\nSince these errors are persisting, try a COMPLETELY DIFFERENT APPROACH:")
            else:
                recommendation.append("\nThese errors have persisted, consider a different approach:")
            
            # Add specific recommendations based on persistent error types and their severity
            if "memory_leak" in persistent_errors or "memory_leak" in special_persistence_flags:
                leak_count = persistent_errors.get("memory_leak", special_persistence_flags.get("memory_leak", 0))
                recommendation.append(f"1. For persistent memory leaks (seen in {leak_count} versions):")
                if leak_count >= 3:
                    recommendation.append("   - 🔴 CRITICAL: COMPLETELY ELIMINATE ALL DYNAMIC MEMORY ALLOCATION")
                    recommendation.append("   - 🔴 Use fixed-size static arrays ONLY - NO malloc() calls at all")
                    recommendation.append("   - 🔴 Rewrite the entire harness with a different approach")
                else:
                    recommendation.append("   - Avoid allocating memory completely if possible")
                    recommendation.append("   - Use stack-allocated arrays or fixed-size buffers instead of malloc")
                    recommendation.append("   - Place all free() calls in a single location at the end of main()")
                    recommendation.append("   - Add __CPROVER_cleanup blocks to ensure memory is freed even in error paths")
            
            if "null_pointer" in persistent_errors or "null_pointer" in special_persistence_flags:
                null_count = persistent_errors.get("null_pointer", special_persistence_flags.get("null_pointer", 0))
                recommendation.append(f"2. For persistent null pointer issues (seen in {null_count} versions):")
                if null_count >= 3:
                    recommendation.append("   - 🔴 CRITICAL: COMPLETELY ELIMINATE ALL POINTER USAGE WHERE POSSIBLE")
                    recommendation.append("   - 🔴 Use direct stack variables instead of pointers")
                    recommendation.append("   - 🔴 Add explicit NULL checks before EVERY pointer dereference")
                    recommendation.append("   - 🔴 Rewrite the entire harness with a different approach")
                else:
                    recommendation.append("   - Add explicit NULL checks BEFORE every pointer use")
                    recommendation.append("   - Use __CPROVER_assume(ptr != NULL) immediately after each pointer definition")
                    recommendation.append("   - Consider using a simple fixed array instead of dynamic allocation")
            
            if "redeclaration" in persistent_errors or cbmc_result.get("has_redeclaration_error", False):
                recommendation.append("3. For persistent redeclaration issues:")
                recommendation.append("   - REMOVE ALL declarations and rely only on included headers")
                recommendation.append("   - Try a minimal set of includes (remove any that might cause conflicts)")
                recommendation.append("   - Use only fully qualified names for all types")
            
            # General guidance for any persistent errors, more forceful with higher persistence
            if max_persistence >= 3:
                recommendation.append("\n🔄 REQUIRED COMPLETE REDESIGN STRATEGY:")
                recommendation.append("1. THROW AWAY THE CURRENT HARNESS COMPLETELY")
                recommendation.append("2. START FROM SCRATCH with the most minimal possible approach")
                recommendation.append("3. FOCUS ONLY on calling the function with the MINIMUM required setup")
                recommendation.append("4. ELIMINATE ALL DYNAMIC ALLOCATION - use static buffers only")
                recommendation.append("5. ADD EXPLICIT NULL CHECKS before every pointer use")
            else:
                recommendation.append("\nGENERAL STRATEGY FOR PERSISTENT ERRORS:")
                recommendation.append("1. Use a simpler approach with fewer dependencies")
                recommendation.append("2. Focus on the MINIMAL code needed to call the function")
                recommendation.append("3. Reduce the complexity of inputs")
                recommendation.append("4. For memory issues, try using static or stack-allocated memory instead of dynamic allocation")
                recommendation.append("5. Try writing the harness from scratch rather than modifying the previous version")

        # Get redeclaration error information
        stderr = cbmc_result.get("stderr", "")
        stdout = cbmc_result.get("stdout", "")
        error_msg = cbmc_result.get("message", "")
        has_redeclaration_error = cbmc_result.get("has_redeclaration_error", False)
        redeclared_symbols = cbmc_result.get("redeclared_symbols", [])
        
        # If we don't have specific symbols but detect redeclaration in output, try to extract them
        if (not redeclared_symbols and 
            ("redeclaration" in stderr or "redeclaration" in stdout or "redeclaration" in error_msg)):
            has_redeclaration_error = True
            
            # Find all redeclaration mentions
            all_redecl_matches = re.findall(r"redeclaration of '([^']+)'", stderr + stdout)
            for redecl_match in all_redecl_matches:
                if redecl_match not in redeclared_symbols:
                    redeclared_symbols.append(redecl_match)
                    
            # If we still didn't find any, add a placeholder
            if not redeclared_symbols:
                redeclared_symbols = ["unknown symbol"]
        
        # Provide specific guidance for redeclaration errors
        if has_redeclaration_error or redeclared_symbols:
            recommendation.append(f"\n== REDECLARATION ERROR DETECTED ==")
            
            # List all identified symbols with redeclaration errors
            if redeclared_symbols:
                recommendation.append("The following symbols have redeclaration errors:")
                for symbol in redeclared_symbols:
                    recommendation.append(f"- '{symbol}'")
                
            recommendation.append("\nTo fix these redeclaration issues:")
            recommendation.append("1. REMOVE all declarations for symbols already defined in included headers")
            recommendation.append("2. Do NOT redeclare any function, type, enum, or struct from an included header")
            recommendation.append("3. NEVER redefine any macros from included headers")
            recommendation.append("4. Check each included header to see what symbols it already defines")
            recommendation.append("5. If you absolutely must declare something, use 'extern' and match signatures exactly")
            recommendation.append("6. Remove duplicate declarations in your harness code")
            recommendation.append("7. For 'redeclaration with no linkage' errors, use extern or remove the declaration completely\n")
            
            recommendation.append("RESOLUTION STRATEGY:")
            recommendation.append("1. First try REMOVING the declarations completely (preferred solution)")
            recommendation.append("2. Only if removal doesn't work, add 'extern' keyword")
            recommendation.append("3. Check your include order - some headers may need to be included before others")
            
            # Provide a correct declaration example
            recommendation.append("\nExample of proper external declaration (only if needed):")
            recommendation.append("extern ReturnType FunctionName(ParameterType paramName);")
            
            # For "no linkage" errors, add specific guidance
            if any("no linkage" in err for err in [stderr, stdout, error_msg]):
                recommendation.append("\nSPECIFIC GUIDANCE FOR 'NO LINKAGE' ERRORS:")
                recommendation.append("- These often involve enum values, struct types, or macros")
                recommendation.append("- Check if the symbol is defined as an enum value, macro, or typedef")
                recommendation.append("- For enums and structs: you cannot redeclare them at all")
                recommendation.append("- Solution: remove your declarations and use what's in the header")
        
        # Add line-specific error mapping with enhanced pinpointing
        error_locations = cbmc_result.get("error_locations", {})
        # Also check if we have stderr content for more line-specific error details
        stderr = cbmc_result.get("stderr", "")
        
        if error_locations:
            # Add specific section for line-based error mapping
            recommendation.append("\n== LINE-SPECIFIC ERROR TRACING ==")
            recommendation.append("The following line numbers in your harness have verification failures:")
            
            # First extract more detailed error information from CBMC stderr output to map lines to specific errors
            # This maps file+line to detailed error message
            detailed_line_errors = {}
            
            # Extract line-specific error messages from stderr first (more detail)
            if stderr:
                for line in stderr.split('\n'):
                    if 'error:' in line or (('warning:' in line) and any(critical in line.lower() 
                                                                 for critical in ['pointer', 'memory', 'null', 'invalid'])):
                        # Extract file and line information using improved regex
                        loc_match = re.search(r'([^:]+):(\d+)(?::\d+)?:', line)
                        if loc_match:
                            file_name = loc_match.group(1)
                            line_num = int(loc_match.group(2))
                            # Extract the actual error message
                            error_msg = line.split(':', 3)[-1].strip() if len(line.split(':', 3)) >= 4 else line
                            
                            # Create key for the detailed_line_errors dictionary
                            key = f"{file_name}:{line_num}"
                            if key not in detailed_line_errors:
                                detailed_line_errors[key] = []
                            # Add this specific error message
                            detailed_line_errors[key].append(error_msg)
            
            # Now extract error messages from stdout for lines that don't have stderr details
            for line in cbmc_result.get("stdout", "").split('\n'):
                if "FAILED" in line or "FAILURE" in line or "ERROR" in line:
                    loc_match = re.search(r'file ([^:]+):(\d+)', line)
                    if loc_match:
                        file_name = loc_match.group(1)
                        line_num = int(loc_match.group(2))
                        key = f"{file_name}:{line_num}"
                        
                        # Only add if we don't already have stderr details for this line
                        if key not in detailed_line_errors:
                            detailed_line_errors[key] = []
                            # Extract the error type and message if possible
                            error_type_match = re.search(r'\[(.*?)\]', line)
                            error_type = error_type_match.group(1) if error_type_match else "general"
                            detailed_line_errors[key].append(f"{error_type}: {line.strip()}")
            
            # Track by file
            for file_name, line_numbers in error_locations.items():
                # If this is the harness file (look for a pattern like "*_harness_*.c")
                if "_harness_" in file_name or "harness" in file_name:
                    recommendation.append(f"\nIn harness file '{file_name}':")
                    
                    # Get lines from harness code
                    harness_lines = harness_code.strip().split('\n')
                    
                    # For context, we'll show surrounding lines as well
                    context_lines = 2  # Number of lines before and after error line
                    
                    # Map each error line to actual code with context
                    for line_num in sorted(line_numbers):
                        # Adjust for 0-based indexing in our code representation
                        line_index = line_num - 1
                        
                        # Safety check to avoid index errors
                        if 0 <= line_index < len(harness_lines):
                            # Get the error line content
                            line_content = harness_lines[line_index].strip()
                            if line_content:
                                recommendation.append(f"\n🔴 Line {line_num}: {line_content}")
                                
                                # Add the detailed error message if available
                                key = f"{file_name}:{line_num}"
                                if key in detailed_line_errors and detailed_line_errors[key]:
                                    recommendation.append(f"  SPECIFIC ERROR: {'; '.join(detailed_line_errors[key])}")
                                
                                # Add specific improvement hint based on line content and error message
                                specific_error = detailed_line_errors.get(key, [])
                                specific_error_str = ' '.join(specific_error).lower()
                                
                                if "malloc" in line_content and not "free" in harness_code:
                                    recommendation.append(f"  ↪ FIX NEEDED: Add free() for memory allocated on this line")
                                elif "->" in line_content or "*" in line_content or "null" in specific_error_str or "nullptr" in specific_error_str:
                                    recommendation.append(f"  ↪ FIX NEEDED: Add NULL check before pointer dereference")
                                    recommendation.append(f"    Example: if (ptr != NULL) {{ ... }}")
                                elif "[" in line_content and "]" in line_content or "bounds" in specific_error_str or "index" in specific_error_str:
                                    recommendation.append(f"  ↪ FIX NEEDED: Add bounds check for array access")
                                    recommendation.append(f"    Example: __CPROVER_assume(index < array_size);")
                                elif "/" in line_content or "division" in specific_error_str:
                                    recommendation.append(f"  ↪ FIX NEEDED: Add check to prevent division by zero")
                                    recommendation.append(f"    Example: __CPROVER_assume(divisor != 0);")
                                elif "overflow" in specific_error_str:
                                    recommendation.append(f"  ↪ FIX NEEDED: Add checks to prevent arithmetic overflow")
                                    recommendation.append(f"    Example: __CPROVER_assume(x < INT_MAX/2);")
                                
                                # Show context before and after
                                recommendation.append("\n  Context:")
                                start_ctx = max(0, line_index - context_lines)
                                end_ctx = min(len(harness_lines), line_index + context_lines + 1)
                                
                                for ctx_idx in range(start_ctx, end_ctx):
                                    if ctx_idx == line_index:  # Skip the error line as it's already shown
                                        continue
                                    
                                    prefix = "  → " if ctx_idx < line_index else "  → "
                                    recommendation.append(f"{prefix}Line {ctx_idx+1}: {harness_lines[ctx_idx].strip()}")
                            
                        else:
                            recommendation.append(f"Line {line_num}: [Line number out of range]")
                else:
                    # This is a source file, not the harness
                    recommendation.append(f"\nIn source file '{file_name}':")
                    for line_num in sorted(line_numbers):
                        # Add the detailed error message if available
                        key = f"{file_name}:{line_num}"
                        error_detail = ""
                        if key in detailed_line_errors and detailed_line_errors[key]:
                            error_detail = f" - {'; '.join(detailed_line_errors[key])}"
                            
                        recommendation.append(f"Line {line_num}: Error originated in source code{error_detail}")
            
            # Add additional suggestions for common issues based on error patterns
            common_issues = []
            
            # Look at all detailed errors to identify patterns
            for key, errors in detailed_line_errors.items():
                error_str = ' '.join(errors).lower()
                
                if "null" in error_str or "nullptr" in error_str:
                    common_issues.append("🔍 NULL POINTER DEREFERENCE detected - Add checks before using pointers")
                if "memory" in error_str and ("leak" in error_str or "free" in error_str):
                    common_issues.append("🔍 MEMORY LEAK detected - Ensure all allocated memory is freed")
                if "bounds" in error_str or "index" in error_str:
                    common_issues.append("🔍 ARRAY BOUNDS issue detected - Add bounds checks before accessing arrays")
                if "division" in error_str and "zero" in error_str:
                    common_issues.append("🔍 DIVISION BY ZERO detected - Add checks to ensure divisors are non-zero")
            
            # Add common issues without duplication
            if common_issues:
                recommendation.append("\nCommon Issues Detected:")
                for issue in sorted(set(common_issues)):
                    recommendation.append(f"{issue}")
            
            # Add tracing guidance
            recommendation.append("\nRemember to trace each error to its root cause in your harness:")
            recommendation.append("- For memory leaks: Add free() for every malloc()/calloc()")
            recommendation.append("- For null pointer: Add NULL checks before dereferencing")
            recommendation.append("- For array bounds: Add boundary constraints with __CPROVER_assume()")
            recommendation.append("- For division by zero: Add checks with __CPROVER_assume(divisor != 0)")
            
            # Add suggested patterns for fixing the identified issues
            recommendation.append("\nSuggested Fix Patterns:")
            if any("null" in ' '.join(errors).lower() for errors in detailed_line_errors.values()):
                recommendation.append("""
// NULL pointer check pattern:
if (ptr != NULL) {
    // Use ptr only inside this block
    result = ptr->field;  // Safe to dereference
} else {
    // Handle NULL case
    return ERROR_CODE;
}

// Alternatively, use CBMC assume:
__CPROVER_assume(ptr != NULL);
result = ptr->field;  // Now safe because CBMC knows ptr is not NULL
""")
            
            if any("memory" in ' '.join(errors).lower() and "leak" in ' '.join(errors).lower() 
                  for errors in detailed_line_errors.values()):
                recommendation.append("""
// Memory management pattern:
void* buffer = malloc(size);
__CPROVER_assume(buffer != NULL);
// ... use buffer ...
free(buffer);  // Always free allocated memory at the end

// OR use stack allocation instead:
char static_buffer[SIZE];  // No need for malloc/free
""")
                
            if any("bounds" in ' '.join(errors).lower() or "index" in ' '.join(errors).lower() 
                  for errors in detailed_line_errors.values()):
                recommendation.append("""
// Array bounds check pattern:
size_t index = nondet_size_t();
__CPROVER_assume(index < array_size);  // Ensure index is within bounds
array[index] = value;  // Safe array access
""")
        
            # Find harness code snippets that may contain related problematic code
            if "null_pointer" in cbmc_result.get("error_categories", []):
                # Find pointer dereference patterns without null checks
                ptr_derefs = re.findall(r'(\w+)\s*->\s*\w+', harness_code)
                ptr_derefs += re.findall(r'\*\s*(\w+)', harness_code)  # Also catch *ptr dereferencing
                
                unchecked_ptrs = []
                for ptr in ptr_derefs:
                    if (f"if ({ptr} != NULL)" not in harness_code and 
                        f"__CPROVER_assume({ptr} != NULL)" not in harness_code and
                        f"if (NULL != {ptr})" not in harness_code):
                        unchecked_ptrs.append(ptr)
                
                if unchecked_ptrs:
                    recommendation.append("\nUnchecked pointer dereferences found:")
                    for ptr in sorted(set(unchecked_ptrs)):
                        recommendation.append(f"- '{ptr}' is used without NULL check")
                    recommendation.append("\nAdd null checks before using these pointers:")
                    recommendation.append(f"if ({unchecked_ptrs[0]} != NULL) {{ /* use {unchecked_ptrs[0]} */ }}")
                    recommendation.append(f"OR: __CPROVER_assume({unchecked_ptrs[0]} != NULL);")
            
            if "memory_leak" in cbmc_result.get("error_categories", []):
                # Find malloc without corresponding free
                malloc_vars = re.findall(r'(\w+)\s*=\s*(?:malloc|calloc)\([^;]+\)', harness_code)
                unfree_vars = []
                
                for var in malloc_vars:
                    if f"free({var})" not in harness_code:
                        unfree_vars.append(var)
                
                if unfree_vars:
                    recommendation.append("\nMemory leaks detected:")
                    for var in unfree_vars:
                        recommendation.append(f"- '{var}' is allocated but never freed")
                    recommendation.append("\nAdd these lines before the end of main():")
                    for var in unfree_vars:
                        recommendation.append(f"free({var});  // Free allocated memory")
            
            # Add tracing guidance
            recommendation.append("\nRemember to trace each error to its root cause in your harness:")
            recommendation.append("- For memory leaks: Add free() for every malloc()/calloc()")
            recommendation.append("- For null pointer: Add NULL checks before dereferencing")
            recommendation.append("- For array bounds: Add boundary constraints with __CPROVER_assume()")

            # Find harness code snippets that may contain related problematic code
            if "null_pointer" in cbmc_result.get("error_categories", []):
                # Find pointer dereference patterns without null checks
                ptr_derefs = re.findall(r'(\w+)\s*->\s*\w+', harness_code)
                for ptr in ptr_derefs:
                    if f"if ({ptr} != NULL)" not in harness_code and f"__CPROVER_assume({ptr} != NULL)" not in harness_code:
                        recommendation.append(f"\nUnchecked pointer dereference found: '{ptr}->'")
                        recommendation.append(f"Add this before using: if ({ptr} != NULL) {{ ... }}")
            
            if "memory_leak" in cbmc_result.get("error_categories", []):
                # Find malloc without corresponding free
                malloc_vars = re.findall(r'(\w+)\s*=\s*(?:malloc|calloc)\([^;]+\)', harness_code)
                for var in malloc_vars:
                    if f"free({var})" not in harness_code:
                        recommendation.append(f"\nMemory leak detected: '{var}' is allocated but never freed")
                        recommendation.append(f"Add this before end of function: free({var});")
        
        # Add specific recommendations for timeout issues
        if cbmc_result.get("verification_status") == "TIMEOUT" or "timeout" in cbmc_result.get("error_categories", []):
            recommendation.append("\n== TIMEOUT ISSUES DETECTED ==")
            recommendation.append("CBMC verification timed out, which often indicates excessive complexity in the harness.")
            recommendation.append("Here are specific recommendations to prevent timeouts:")
            
            # Check harness complexity
            complexity_issues = []
            if "while" in harness_code and "__CPROVER_assume" not in harness_code:
                complexity_issues.append("- Harness contains loops without CPROVER constraints")
            if harness_code.count("malloc(") > 3:
                complexity_issues.append("- Harness has excessive memory allocations (>3)")
            if len(harness_code.split('\n')) > 100:
                complexity_issues.append("- Harness is excessively long (>100 lines)")
            
            # Add found complexity issues or generic guidance
            if complexity_issues:
                recommendation.append("\nDetected complexity issues in harness:")
                recommendation.extend(complexity_issues)
            
            recommendation.append("\nTimeout resolution strategies:")
            recommendation.append("1. REDUCE COMPLEXITY: Create a significantly simpler harness")
            recommendation.append("   - Remove unnecessary loops or limit iterations with __CPROVER_assume(i < 3)")
            recommendation.append("   - Reduce the number of malloc() calls and the size of allocated memory")
            recommendation.append("   - Use smaller, fixed-size buffers instead of dynamic allocation")
            recommendation.append("   - Add specific constraints to limit input values")
            
            recommendation.append("\n2. AVOID UNBOUNDED LOOPS:")
            recommendation.append("   - Add bounds to all loops: for(int i=0; i < N; i++) where N is small (≤3)")
            recommendation.append("   - Add __CPROVER_assume(counter < MAX) before any while loop")
            recommendation.append("   - Replace while loops with equivalent fixed-iteration for loops when possible")
            
            recommendation.append("\n3. USE SPECIFIC BOUNDS ON INPUTS:")
            recommendation.append("   - Add constraints on all nondeterministic inputs")
            recommendation.append("   - Examples:")
            recommendation.append("     - __CPROVER_assume(size > 0 && size < 10);")
            recommendation.append("     - __CPROVER_assume(ptr != NULL && is_valid(ptr));")
            
            recommendation.append("\n4. SIMPLIFY MEMORY ALLOCATION:")
            recommendation.append("   - Use stack allocation instead of dynamic memory when possible:")
            recommendation.append("     char buffer[SIZE]; // Instead of malloc(SIZE)")
            recommendation.append("   - Limit allocated memory to small sizes:")
            recommendation.append("     malloc(size); where __CPROVER_assume(size < 10);")
            
            recommendation.append("\n5. USE THE --UNWIND FLAG:")
            recommendation.append("   - Add specific unwinding limits in the harness comment:")
            recommendation.append("     // --unwind 3")
            recommendation.append("   - This helps CBMC limit loop iterations")
            
            # Example of a minimal timeout-resistant harness
            recommendation.append("\nExample of a minimal timeout-resistant harness:")
            recommendation.append("```c")
            recommendation.append("// Minimal harness pattern to avoid timeouts")
            recommendation.append("#include <stdlib.h>")
            recommendation.append("")
            recommendation.append("void main() {")
            recommendation.append("    // Use constrained inputs")
            recommendation.append("    int size = nondet_int();")
            recommendation.append("    __CPROVER_assume(size > 0 && size < 10);  // Small, bounded size")
            recommendation.append("")
            recommendation.append("    // Prefer stack allocation when possible")
            recommendation.append("    char fixed_buffer[10];  // Fixed small size")
            recommendation.append("")
            recommendation.append("    // If malloc is necessary, use small sizes and null checks")
            recommendation.append("    char* dynamic_buffer = NULL;")
            recommendation.append("    if (size > 5) {  // Conditional allocation")
            recommendation.append("        dynamic_buffer = malloc(size);")
            recommendation.append("        __CPROVER_assume(dynamic_buffer != NULL);")
            recommendation.append("    }")
            recommendation.append("")
            recommendation.append("    // Call function with carefully constrained inputs")
            recommendation.append("    int result = target_function(fixed_buffer, size);")
            recommendation.append("")
            recommendation.append("    // Always free allocated memory")
            recommendation.append("    if (dynamic_buffer != NULL) {")
            recommendation.append("        free(dynamic_buffer);")
            recommendation.append("    }")
            recommendation.append("}")
            recommendation.append("```")
            
        # Add code patterns for specific error types
        patterns = []
        
        # Look for error categories and their persistence
        error_categories = cbmc_result.get("error_categories", [])
        persistent_errors = cbmc_result.get("persistent_errors", {})
        
        # Check for highly persistent null pointer errors to give more specific guidance
        null_persistence = persistent_errors.get("null_pointer", 0)
        if null_persistence >= 2:
            # For errors that have persisted 2+ versions, give more specific advice
            patterns.append(f"""
            // PERSISTENT ({null_persistence} versions) NULL POINTER ERROR - MAJOR REDESIGN NEEDED
            // Try using a completely different approach with these patterns:
            
            // APPROACH 1: Avoid pointers entirely when possible
            char static_buffer[BUFFER_SIZE]; // Use stack allocation instead of malloc
            size_t buffer_len = BUFFER_SIZE;
            
            // APPROACH 2: If you must use pointers, do extensive checking
            if (ptr != NULL) {{
                // Only use ptr inside this block
                // ...
            }}
            else {{
                // Handle null case explicitly
                return ERROR_CODE;
            }}
            """)
        
        # Check for highly persistent memory leaks
        memory_persistence = persistent_errors.get("memory_leak", 0)
        if memory_persistence >= 2:
            patterns.append(f"""
            // PERSISTENT ({memory_persistence} versions) MEMORY LEAK - MAJOR REDESIGN NEEDED
            // Try using a completely different approach with these patterns:
            
            // APPROACH 1: Avoid dynamic allocation entirely
            char static_buffer[BUFFER_SIZE]; // Use fixed size buffer on stack
            
            // APPROACH 2: Single allocation pattern with guaranteed cleanup
            void* ptr = malloc(size);
            DefenderStatus_t status = DefenderFailure;
            
            if (ptr != NULL) {{
                // Use ptr...
                status = process_with_ptr(ptr);
                // Always free at the end, regardless of logic paths
                free(ptr);
                return status;
            }}
            return DefenderFailure;
            """)
            
        # Standard pattern suggestions
        if "memory_leak" in error_categories:
            patterns.append("""
            // Memory management pattern
            void* buffer = malloc(size);
            __CPROVER_assume(buffer != NULL);  // Ensure allocation succeeded
            // ... use buffer ...
            free(buffer);  // Always free allocated memory
            """)
            
            # Special handling for memory leaks - check for unfree variables
            malloc_vars = re.findall(r'(\w+)\s*=\s*(?:malloc|calloc)\([^;]+\)', harness_code)
            unfree_vars = []
            
            for var in malloc_vars:
                if f"free({var})" not in harness_code:
                    unfree_vars.append(var)
            
            if unfree_vars:
                patterns.append(f"""
                // Memory leak fix - add these before end of main()
                {"".join([f"free({var});  // Free allocated memory\n" for var in unfree_vars])}
                """)
        
        if "null_pointer" in error_categories:
            patterns.append("""
            // Null pointer check pattern
            void* ptr = malloc(size);
            __CPROVER_assume(ptr != NULL);  // Ensure pointer is valid before use
            // ... use ptr ...
            """)
        
        if "array_bounds" in error_categories:
            patterns.append("""
            // Array bounds pattern
            size_t index = nondet_size_t();
            size_t size = 10;
            __CPROVER_assume(index < size);  // Ensure index is within bounds
            array[index] = value;  // Safe array access
            """)
        
        if "division_by_zero" in error_categories:
            patterns.append("""
            // Division safety pattern
            int divisor = nondet_int();
            __CPROVER_assume(divisor != 0);  // Prevent division by zero
            result = value / divisor;  // Safe division
            """)
        
        if "arithmetic_overflow" in error_categories:
            patterns.append("""
            // Arithmetic safety pattern
            int value = nondet_int();
            __CPROVER_assume(value > 0 && value < INT_MAX/2);  // Prevent overflow
            // ... use value ...
            """)
        
        # Add missing function patterns if needed
        missing_functions = cbmc_result.get("missing_functions", [])
        if missing_functions:
            example_func = next(iter(missing_functions))
            patterns.append(f"""
            // Option 1: Minimal stub for missing function
            // Replace return_type and parameters as needed
            return_type {example_func}(parameters) {{
                // Return a valid value without complex side effects
                return valid_value;
            }}
            
            // Option 2: Avoid calling function directly
            // Instead of: status = {example_func}(...);
            // Do: 
            status_type status = nondet_status_type();
            __CPROVER_assume(status == SUCCESS || status == ERROR);  // Constrain possible values
            """)
        
        # Add formatted patterns
        if patterns:
            recommendation.append("\nRecommended patterns for CBMC verification:")
            for i, pattern in enumerate(patterns):
                recommendation.append(f"\nPattern {i+1}:\n```c\n{pattern.strip()}\n```")
        
        # Add current harness and original function
        recommendation.append("\nCurrent harness:")
        recommendation.append("```c")
        recommendation.append(harness_code.strip())
        recommendation.append("```")
        
        recommendation.append("\nOriginal function:")
        recommendation.append("```c")
        recommendation.append(func_code.strip())
        recommendation.append("```")
        
        # Add critical instructions
        recommendation.append("""
        CRITICAL INSTRUCTIONS:
        1. Fix the specific issues identified in the line-by-line error feedback
        2. Target fixes to the exact line numbers indicated in error locations
        3. Ensure proper memory management (allocation and freeing)
        4. Add appropriate constraints using __CPROVER_assume()
        5. Implement any missing function bodies or avoid calling them
        6. Follow the recommended patterns for specific error types
        7. Focus on creating a minimal, focused harness that verifies the function
        """)
        
        return "\n".join(recommendation)
    except Exception as e:
        logger.error(f"Error generating improvement recommendation: {str(e)}")
        # Provide a basic recommendation in case of error
        return f"""
        Error generating detailed recommendation: {str(e)}
        
        Please check the CBMC output for verification failures and fix the issues.
        
        Current harness:
        ```c
        {harness_code}
        ```
        
        Original function:
        ```c
        {func_code}
        ```
        
        Make sure to fix any missing functions, memory leaks, or other issues detected by CBMC.
        """