"""
CBMC output parsing utilities for the harness generator.
"""
import re
import logging
from typing import Dict, Any, Set, List, Tuple

logger = logging.getLogger("cbmc_parser")

def process_cbmc_output(stdout: str, stderr: str) -> Dict[str, Any]:
    """
    Process CBMC output and extract structured error information.
    
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
        "errors": 0
    }
    
    # Check for successful verification first
    if "VERIFICATION SUCCESSFUL" in stdout:
        result["verification_status"] = "SUCCESS"
        result["message"] = "Verification successful"
        return result
    
    # Check for critical errors in stderr
    if "PARSING ERROR" in stderr or "preprocessing failed" in stderr.lower() or "error generated" in stderr.lower():
        result["verification_status"] = "FAILED"
        result["has_preprocessing_error"] = True
        result["message"] = "Preprocessing error detected"
        
        # Extract specific error messages
        error_messages = []
        error_locations = []
        
        for line in stderr.split('\n'):
            # Look for typical error message patterns
            if 'error:' in line or 'warning:' in line or 'note:' in line:
                error_messages.append(line.strip())
                
                # Extract specific location information
                loc_match = re.search(r'([^:]+):(\d+):', line)
                if loc_match:
                    file_name = loc_match.group(1)
                    line_num = loc_match.group(2)
                    location = f"{file_name}:{line_num}"
                    if location not in error_locations:
                        error_locations.append(location)
        
        # Look for macro-related errors specifically
        macro_errors = []
        for line in stderr.split('\n'):
            if 'macro' in line.lower() and ('error' in line.lower() or 'defined' in line.lower()):
                macro_errors.append(line.strip())
                # Try to extract the macro name
                macro_match = re.search(r"macro '([^']+)'", line)
                if macro_match:
                    macro_name = macro_match.group(1)
                    macro_errors.append(f"Problematic macro: {macro_name}")
        
        # Create a more detailed error description
        if macro_errors:
            error_description = "Macro definition error: " + "; ".join(macro_errors[:2])
            result["message"] = f"PREPROCESSING ERROR: {error_description}"
            result["suggestions"] = "Fix macro definitions and ensure they are properly defined"
        elif error_messages:
            error_description = "; ".join(error_messages[:3])
            result["message"] = f"PREPROCESSING ERROR: {error_description}"
            result["suggestions"] = "Fix syntax errors in the harness or source code"
        else:
            result["message"] = "PREPROCESSING ERROR: GCC preprocessing failed - check for syntax errors"
            result["suggestions"] = "Fix syntax errors and ensure all necessary includes are available"
        
        result["error_messages"] = error_messages
        if error_locations:
            result["error_locations"] = {"preprocessing_errors": error_locations}
        
        return result
    
    # Check for verification failures - we know it's failed if we got here
    result["verification_status"] = "FAILED" 
    
    # Extract all failure information
    failure_lines = []
    failure_categories = set()
    failure_locations = {}
    
    # Process each line of stdout for detailed failure information
    for line in stdout.split('\n'):
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
                location = f"{file_name}:{line_num}"
                
                # Add to location tracking
                if file_name not in failure_locations:
                    failure_locations[file_name] = []
                if line_num not in failure_locations[file_name]:
                    failure_locations[file_name].append(line_num)
    
    # Extract missing function bodies
    missing_functions = set()
    for line in stdout.split('\n'):
        if "no body for callee" in line:
            match = re.search(r'no body for callee (\w+)', line)
            if match:
                func_name = match.group(1)
                missing_functions.add(func_name)
    
    
    # Count errors and set suggestions based on categories
    if failure_categories:
        result["error_categories"] = list(failure_categories)
        result["verification_failures"] = list(failure_categories)
        
        # Set message and suggestions based on primary failure category
        if "memory_leak" in failure_categories:
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
    
    # Add function-specific metrics
    func_reachable = result.get("func_reachable_lines", 0)
    func_covered = result.get("func_covered_lines", 0)
    func_coverage = result.get("func_coverage_pct", 0.0)
    
    feedback.append("\nFunction Coverage Metrics:")
    feedback.append(f"- Function reachable lines: {func_reachable}")
    feedback.append(f"- Function covered lines: {func_covered}")
    feedback.append(f"- Function coverage: {func_coverage:.2f}%")
    
    return "\n".join(feedback)

def generate_improvement_recommendation(harness_code: str, func_code: str, cbmc_result: Dict[str, Any]) -> str:
    """
    Generate a targeted improvement recommendation based on CBMC results.
    
    Args:
        harness_code: The current harness code
        func_code: The original function code
        cbmc_result: The processed CBMC output result
        
    Returns:
        A detailed improvement recommendation
    """
    try:
        # Start with the error feedback
        recommendation = [format_error_for_feedback(cbmc_result)]
        
        # Add code patterns for specific error types
        patterns = []
        
        # Look for error categories in either location
        error_categories = cbmc_result.get("error_categories", [])
        
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
        1. Fix the specific issues identified in the error feedback
        2. Ensure proper memory management (allocation and freeing)
        3. Add appropriate constraints using __CPROVER_assume()
        4. Implement any missing function bodies or avoid calling them
        5. Follow the recommended patterns for specific error types
        6. Focus on creating a minimal, focused harness that verifies the function
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