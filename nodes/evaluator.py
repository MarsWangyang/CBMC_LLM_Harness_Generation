"""
Enhanced harness evaluator node with improved RAG integration and solution tracking.
"""
import time
import logging
import os
import json
import re
from langchain_core.messages import AIMessage
from utils.cbmc_parser import generate_improvement_recommendation
from utils.rag import get_unified_db

logger = logging.getLogger("evaluator")

def harness_evaluator_node(state):
    """
    Enhanced harness evaluation with sophisticated RAG-driven solution tracking.
    """
    evaluation_start = time.time()
    
    func_name = state.get("current_function", "")
    loop_counter = state.get("loop_counter", 0)
    
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
    
    logger.info(f"Evaluating harness for {func_name}")
    
    harnesses = state.get("harnesses", {})
    cbmc_results = state.get("cbmc_results", {})
    
    # Get result directories for RAG storage
    result_directories = state.get("result_directories", {})
    
    # Initialize unified RAG database
    rag_db = get_unified_db(os.path.join(result_directories.get("result_base_dir", "results"), "rag_data"))

    # Track function times
    function_times = state.get("function_times", {}).copy()
    if func_name not in function_times:
        function_times[func_name] = {}
    
    # Track refinement attempts
    state_refinement_attempts = state.get("refinement_attempts", {}).copy()
    if func_name not in state_refinement_attempts:
        state_refinement_attempts[func_name] = 0
    
    current_attempts = state_refinement_attempts.get(func_name, 0)
    max_refinements = 10  # Maximum number of refinement attempts
    
    # Processed functions tracking
    state_processed_functions = state.get("processed_functions", []).copy()
    
    # Force progression after max attempts
    if current_attempts >= max_refinements:
        if func_name not in state_processed_functions:
            state_processed_functions.append(func_name)
            logger.info(f"Max refinements reached for {func_name}, proceeding to next function")
        
        return {
            "messages": [AIMessage(content=f"Maximum refinement attempts ({max_refinements}) reached for {func_name}. Moving to next function.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "loop_counter": loop_counter,
            "next": "junction"
        }
    
    # Safety: Handle missing data
    harness_code = harnesses.get(func_name, "")
    cbmc_result = cbmc_results.get(func_name, {})
    
    if not harness_code or not cbmc_result:
        if func_name and func_name not in state_processed_functions:
            state_processed_functions.append(func_name)
            logger.info(f"Missing data for {func_name}, proceeding to next function")
        
        return {
            "messages": [AIMessage(content=f"Error: Missing harness or CBMC result for function {func_name}. Marking as processed.")],
            "processed_functions": state_processed_functions,
            "loop_counter": loop_counter,
            "next": "junction"
        }
    
    # Retrieve function code from RAG database
    function_data = rag_db.get_code_function(func_name)
    func_code = ""
    
    if function_data:
        func_code = function_data.get("code", "")
        logger.info(f"Retrieved function {func_name} from unified RAG database")
    else:
        # Fallback to code_collection if not in RAG database
        from core.embedding_db import code_collection
        function_result = code_collection.get(ids=[func_name], include=["documents"])
        
        if function_result["ids"]:
            func_code = function_result["documents"][0]
    
    # Make sure we're incrementing the refinement attempts - CRUCIAL FIX
    # This ensures versioning is consistent even for successful verifications
    state_refinement_attempts[func_name] = current_attempts + 1
    
    # Get harness version
    refinement_num = current_attempts
    version_num = refinement_num + 1
    
    # Save the harness and report regardless of verification outcome
    # Ensure the harness is saved to disk
    harnesses_dir = result_directories.get("harnesses_dir", "harnesses")
    func_harness_dir = os.path.join(harnesses_dir, func_name)
    os.makedirs(func_harness_dir, exist_ok=True)
    
    # Save harness to file
    harness_file = os.path.join(func_harness_dir, f"v{version_num}.c")
    if not os.path.exists(harness_file):
        with open(harness_file, "w") as f:
            f.write(harness_code)
            
    # Save to harness history - with defensive initialization
    harness_history = state.get("harness_history", {}).copy()
    if func_name not in harness_history:
        harness_history[func_name] = []
    elif not isinstance(harness_history[func_name], list):
        # Fix any corrupted state - ensure it's always a list
        logger.warning(f"Harness history for {func_name} was not a list. Reinitializing.")
        harness_history[func_name] = []
        
    if harness_code and harness_code not in harness_history[func_name]:
        harness_history[func_name].append(harness_code)
    
    # IMPORTANT: Store previous error categories in current result for tracking progress
    # This allows us to compare them in the next iteration
    curr_error_categories = cbmc_result.get("error_categories", [])
    prev_result = cbmc_results.get(func_name, {})
    if prev_result and "error_categories" in prev_result and version_num > 1:
        cbmc_result["previous_error_categories"] = prev_result.get("error_categories", [])
    
    # Check for critical STDERR issues that need to be prioritized
    stderr = cbmc_result.get("stderr", "")
    if stderr and ("error:" in stderr or "undefined reference" in stderr):
        logger.warning(f"Critical STDERR errors detected for {func_name}")
        
        # Add specialized error categories based on stderr content
        if "redeclaration" in stderr and "redeclaration" not in curr_error_categories:
            curr_error_categories.append("redeclaration")
            cbmc_result["error_categories"] = curr_error_categories
            logger.warning(f"Added 'redeclaration' to error categories based on STDERR")
            
        if "undefined reference" in stderr and "linking_error" not in curr_error_categories:
            curr_error_categories.append("linking_error")
            cbmc_result["error_categories"] = curr_error_categories
            logger.warning(f"Added 'linking_error' to error categories based on STDERR")
            
        # Check for common CBMC-specific issues in STDERR
        if "cannot open file" in stderr:
            curr_error_categories.append("missing_file")
            cbmc_result["error_categories"] = curr_error_categories
            logger.warning(f"Added 'missing_file' to error categories based on STDERR")
            
        # Ensure the stderr is properly processed in the evaluation output
        cbmc_result["has_stderr_errors"] = True
        
    # Check for timeout and performance issues
    is_timeout = cbmc_result.get("status") == "TIMEOUT" or cbmc_result.get("verification_status") == "TIMEOUT"
    is_slow = cbmc_result.get("is_slow_verification", False)
    
    # Add specialized handling for timeouts
    if is_timeout and "timeout" not in curr_error_categories:
        curr_error_categories.append("timeout")
        cbmc_result["error_categories"] = curr_error_categories
        logger.warning(f"Added 'timeout' to error categories for {func_name}")
        
        # Track timeout as a persistent issue
        state_persistent_errors = state.get("persistent_errors", {})
        if func_name not in state_persistent_errors:
            state_persistent_errors[func_name] = {}
            
        if "timeout" not in state_persistent_errors[func_name]:
            state_persistent_errors[func_name]["timeout"] = 1
        else:
            state_persistent_errors[func_name]["timeout"] += 1
            
        state["persistent_errors"] = state_persistent_errors
        cbmc_result["persistent_errors"] = state_persistent_errors[func_name]
        
    # Add specialized handling for slow verification (may lead to future timeouts)
    if is_slow and "performance_warning" not in curr_error_categories:
        curr_error_categories.append("performance_warning")
        cbmc_result["error_categories"] = curr_error_categories
        
        verification_time = cbmc_result.get("slow_verification_time", 0.0)
        logger.warning(f"Added 'performance_warning' to error categories for {func_name} - verification took {verification_time:.1f}s")
    
    # Enhanced check for repeated errors - consider both error categories and specific error messages
    error_categories = cbmc_result.get("error_categories", [])
    previous_error_categories = cbmc_result.get("previous_error_categories", [])
    
    # Track the failure count to monitor progress
    current_failure_count = cbmc_result.get("failure_count", 0)
    
    # Get the raw stderr content for detailed error comparison
    current_stderr = cbmc_result.get("stderr", "")
    
    # Store current failure count and error categories for the next iteration
    previous_cbmc_result = cbmc_results.get(func_name, {})
    if previous_cbmc_result and previous_cbmc_result.get("version", 0) < version_num:
        cbmc_result["previous_failure_count"] = previous_cbmc_result.get("failure_count", 0)
        cbmc_result["previous_stderr"] = previous_cbmc_result.get("stderr", "")
    
    # Extract specific error messages from stderr for more precise comparison
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
                    
                    # Special handling for conversion errors - capture more specific info
                    if ('invalid conversion' in error_msg.lower() or 
                        'incompatible type' in error_msg.lower() or 
                        'conversion from' in error_msg.lower() or
                        'type mismatch' in error_msg.lower() or
                        'cannot convert' in error_msg.lower()):
                        
                        # Mark as a conversion error explicitly to ensure proper categorization
                        error_sigs.append("CONVERSION ERROR DETECTED")
                        
                        # Try to extract source and target types for more specific guidance
                        from_type = ""
                        to_type = ""
                        
                        # Try several regex patterns for different error formats
                        from_match = re.search(r'from [\'"]?([^\'"\s]+)[\'"]?', error_msg)
                        to_match = re.search(r'to [\'"]?([^\'"\s]+)[\'"]?', error_msg)
                        
                        if from_match:
                            from_type = from_match.group(1)
                        if to_match:
                            to_type = to_match.group(1)
                        
                        # Add structured conversion error if we found the types
                        if from_type and to_type:
                            conversion_err = f"CONVERSION ERROR: from '{from_type}' to '{to_type}'"
                            error_sigs.append(conversion_err)
        return error_sigs
    
    # Get specific error messages from current and previous runs
    current_error_sigs = extract_error_signatures(current_stderr)
    previous_stderr = cbmc_result.get("previous_stderr", "")
    previous_error_sigs = extract_error_signatures(previous_stderr)
    
    # Check if the specific error messages are the same
    same_specific_errors = False
    if current_error_sigs and previous_error_sigs:
        # Convert to sets to compare unique errors without order
        same_specific_errors = set(current_error_sigs) == set(previous_error_sigs)
        
        # Log detailed error comparison
        logger.info(f"Current error signatures: {current_error_sigs}")
        logger.info(f"Previous error signatures: {previous_error_sigs}")
        logger.info(f"Same specific errors: {same_specific_errors}")
        
        # Store the specific error signatures in the result for the generator
        cbmc_result["error_signatures"] = current_error_sigs
        
    # Get previous failure count safely (accessing it correctly before we use it)
    previous_failure_count = cbmc_result.get("previous_failure_count", 0)
    if isinstance(previous_failure_count, str) and previous_failure_count.isdigit():
        previous_failure_count = int(previous_failure_count)
    elif not isinstance(previous_failure_count, (int, float)):
        previous_failure_count = 0
    
    # Sort error categories for consistent comparison and logging
    sorted_error_categories = sorted(error_categories) if error_categories else []
    sorted_previous_error_categories = sorted(previous_error_categories) if previous_error_categories else []
    
    # Log the actual counts for debugging with additional error information
    logger.info(f"Previous failure count for {func_name}: {previous_failure_count}")
    logger.info(f"Current failure count for {func_name}: {current_failure_count}")
    logger.info(f"Current error categories: {sorted_error_categories}")
    logger.info(f"Previous error categories: {sorted_previous_error_categories}")
    
    # Log coverage information alongside error data for better tracking
    coverage_percentage = cbmc_result.get("func_coverage_pct", 0.0)
    if isinstance(coverage_percentage, str) and coverage_percentage != "NA":
        try:
            coverage_percentage = float(coverage_percentage)
        except (ValueError, TypeError):
            coverage_percentage = 0.0
    
    # Get all error metrics to ensure we have a complete picture
    reported_errors = cbmc_result.get("reported_errors", 0)
    failure_count = cbmc_result.get("failure_count", 0)
    error_count = cbmc_result.get("error_count", 0)
    
    # Check stderr for errors as an additional verification
    stderr = cbmc_result.get("stderr", "")
    stderr_error_count = stderr.lower().count("error:") if stderr else 0
    
    # Make sure current_failure_count reflects the actual errors
    max_errors = max(reported_errors, failure_count, error_count, stderr_error_count, current_failure_count)
    
    # If we have errors in stderr but zero counts elsewhere, fix the error counts
    if stderr_error_count > 0 and max_errors == stderr_error_count and current_failure_count == 0:
        current_failure_count = stderr_error_count
        cbmc_result["failure_count"] = stderr_error_count
        cbmc_result["reported_errors"] = stderr_error_count
        cbmc_result["error_count"] = stderr_error_count
        logger.warning(f"Fixed zero error count using stderr errors: {stderr_error_count} errors found")
    
    logger.info(f"Function coverage: {coverage_percentage:.2f}% with {current_failure_count} errors")
    logger.info(f"All error counts: reported={reported_errors}, failures={failure_count}, errors={error_count}, stderr={stderr_error_count}")
    
    # First, retrieve any existing persistent_errors from the state
    state_persistent_errors = state.get("persistent_errors", {})
    if func_name not in state_persistent_errors:
        state_persistent_errors[func_name] = {}
    
    # Check for persistent errors using both categories AND specific error messages
    persistent_error_detected = False
    
    # Detailed check for persistence:
    # 1. Check if error categories are the same
    # 2. Check if specific error signatures are the same
    # 3. Ensure we're not making progress on failures
    
    # We already defined sorted_error_categories and sorted_previous_error_categories above
    # No need to redefine them here
    
    # Convert any string failure counts to integers for proper comparison
    if isinstance(current_failure_count, str) and current_failure_count.isdigit():
        current_failure_count = int(current_failure_count)
    elif not isinstance(current_failure_count, (int, float)):
        current_failure_count = 0
        
    # We already have previous_failure_count from earlier, so we don't need to redefine it here
    # The value was properly initialized and converted above
    
    if ((sorted_error_categories == sorted_previous_error_categories and sorted_error_categories) or 
        (same_specific_errors and current_error_sigs)) and current_failure_count > 0:
        
        # Check if we've made NO progress at all
        # We already converted previous_failure_count above, so use that value directly
        if current_failure_count >= previous_failure_count:
            persistent_error_detected = True
            logger.warning(f"Same errors persist between versions for {func_name} with no improvement in failures. This solution is ineffective.")
            
            # Update persistent errors counter in state AND in CBMC result
            # First, handle category-based errors
            for error in error_categories:
                if error not in state_persistent_errors[func_name]:
                    state_persistent_errors[func_name][error] = 1
                else:
                    state_persistent_errors[func_name][error] += 1
            
            # Then, handle specific error messages
            for error_sig in current_error_sigs:
                # Create a sanitized key for this specific error
                error_key = f"specific:{error_sig[:50]}"  # Truncate for safety
                if error_key not in state_persistent_errors[func_name]:
                    state_persistent_errors[func_name][error_key] = 1
                else:
                    state_persistent_errors[func_name][error_key] += 1
                    
            # Find the highest persistence count for any error
            max_persistence = max(state_persistent_errors[func_name].values()) if state_persistent_errors[func_name] else 0
            
            # Log this for debugging
            logger.warning(f"Maximum error persistence for {func_name}: {max_persistence} versions")
            
            # Set flags directly for generator to use
            state["has_persistent_errors"] = True
            state["persistent_error_count"] = max_persistence
            
            # Update the persistent errors in cbmc_result
            cbmc_result["persistent_errors"] = state_persistent_errors[func_name]
            
            # Also update error-specific persistence counts
            for err_cat in error_categories:
                persistence_key = f"persistence_{err_cat}"
                cbmc_result[persistence_key] = state_persistent_errors[func_name].get(err_cat, 1)
            
            # Add specific error signature persistence
            for error_sig in current_error_sigs:
                error_key = f"specific:{error_sig[:50]}"
                persistence_key = f"persistence_specific"
                if "persistence_specific" not in cbmc_result:
                    cbmc_result["persistence_specific"] = {}
                cbmc_result["persistence_specific"][error_key] = state_persistent_errors[func_name].get(error_key, 1)
            
            # Mark the solution as ineffective in the RAG database
            try:
                rag_db.mark_ineffective_solution(func_name, version_num-1)
            except Exception as e:
                logger.error(f"Failed to mark solution as ineffective: {str(e)}")
    
    # If we didn't detect persistent errors, check if we can reset some
    if not persistent_error_detected:
        # Reset persistent error counts for categories that have been fixed
        for error in previous_error_categories:
            if error not in error_categories and error in state_persistent_errors[func_name]:
                logger.info(f"Error '{error}' has been fixed for {func_name}")
                del state_persistent_errors[func_name][error]
        
        # Reset specific error signatures that have been fixed
        for error_sig in previous_error_sigs:
            error_key = f"specific:{error_sig[:50]}"
            if error_key in state_persistent_errors[func_name] and error_sig not in current_error_sigs:
                logger.info(f"Specific error '{error_sig[:50]}' has been fixed for {func_name}")
                del state_persistent_errors[func_name][error_key]
                
        # If we've fixed all previous errors, clear the persistent error flags
        if not state_persistent_errors[func_name]:
            state["has_persistent_errors"] = False
            state["persistent_error_count"] = 0
    
    # Update the state with the modified persistent errors dictionary
    state["persistent_errors"] = state_persistent_errors
    
    # Check coverage against target
    coverage_percentage = cbmc_result.get("func_coverage_pct", 0.0)
    target_coverage = 85.0  # Target is 85% coverage
    
    # Check if verification was successful
    if cbmc_result.get("status") == "SUCCESS":
        # Check coverage - if we have good coverage (>=80%), we can proceed to next function
        # Otherwise, we should keep refining if we have attempts left
        coverage_good_enough = coverage_percentage >= 80.0
        
        logger.info(f"CBMC verification successful for {func_name}, coverage: {coverage_percentage:.2f}%")
        
        # NEW: Check if only generic errors remain - if yes, ignore them for SUCCESS verification
        has_only_generic_errors = False
        if "error_categories" in cbmc_result:
            error_cats = cbmc_result["error_categories"]
            if len(error_cats) == 1 and "generic_error" in error_cats:
                has_only_generic_errors = True
                logger.info(f"Ignoring generic_error category for successful verification of {func_name}")
                
                # For successful verification, explicitly set error counts to 0
                cbmc_result["error_count"] = 0
                cbmc_result["reported_errors"] = 0
                cbmc_result["failure_count"] = 0
                # Clear the error categories completely for reporting
                cbmc_result["error_categories"] = []
                
        # For ANY successful verification, ensure error counts are 0
        if cbmc_result.get("status") == "SUCCESS":
            cbmc_result["error_count"] = 0
            cbmc_result["reported_errors"] = 0
            cbmc_result["failure_count"] = 0
        
        # Proceed to next function if coverage is good enough OR if we only have generic errors
        if coverage_good_enough or has_only_generic_errors:
            logger.info(f"Coverage is sufficient at {coverage_percentage:.2f}% (or generic errors only), storing solution and moving to next function")
            
            # Store solution in RAG database (error_id will be empty as there's no error)
            solution_id = rag_db.store_solution(
                "",  # No error ID for successful verification
                func_name, 
                harness_code, 
                cbmc_result,
                version_num
            )
            
            # Mark function as processed
            if func_name not in state_processed_functions:
                state_processed_functions.append(func_name)
            
            return {
                "messages": [AIMessage(content=f"CBMC verification successful for {func_name} with {coverage_percentage:.2f}% coverage. Solution stored in knowledge base. Moving to next function.")],
                "refinement_attempts": state_refinement_attempts,
                "processed_functions": state_processed_functions,
                "function_times": function_times,
                "loop_counter": loop_counter,
                "harness_history": harness_history,  # Make sure to return updated harness history
                "next": "junction"
            }
        else:
            # Success but low coverage - should we refine more if we have attempts left?
            if current_attempts < max_refinements - 1:
                logger.info(f"Verification successful but coverage is only {coverage_percentage:.2f}% (below 80% threshold). Attempting to improve coverage.")
                
                # Generate improvement recommendation focused on coverage for successful but low coverage harness
                improvement_recommendation = generate_coverage_improvement_recommendation(harness_code, func_code, cbmc_result, target_coverage)
                
                # Store the current solution even though we'll continue refining (it's a valid solution, just not optimal)
                rag_db.store_solution(
                    "",  # No error ID for successful verification
                    func_name, 
                    harness_code, 
                    cbmc_result,
                    version_num,
                    is_optimal=False  # Mark as non-optimal so we know there's a better version
                )
                
                return {
                    "messages": [AIMessage(content=f"CBMC verification successful for {func_name} but coverage is only {coverage_percentage:.2f}% (below 80% threshold). Attempting to improve coverage (attempt {version_num} of {max_refinements}).")],
                    "refinement_attempts": state_refinement_attempts,
                    "processed_functions": state_processed_functions,
                    "improvement_recommendation": improvement_recommendation,
                    "function_times": function_times,
                    "loop_counter": loop_counter,
                    "harness_history": harness_history,
                    "next": "generator"
                }
            else:
                # We've reached max refinements, accept the successful verification despite lower coverage
                logger.info(f"Max refinements reached. Accepting successful verification with {coverage_percentage:.2f}% coverage.")
                
                # Store solution in RAG database
                solution_id = rag_db.store_solution(
                    "",  # No error ID for successful verification
                    func_name, 
                    harness_code, 
                    cbmc_result,
                    version_num
                )
                
                # Mark function as processed
                if func_name not in state_processed_functions:
                    state_processed_functions.append(func_name)
                
                return {
                    "messages": [AIMessage(content=f"CBMC verification successful for {func_name} with {coverage_percentage:.2f}% coverage. Maximum refinements reached, accepting this solution. Moving to next function.")],
                    "refinement_attempts": state_refinement_attempts,
                    "processed_functions": state_processed_functions,
                    "function_times": function_times,
                    "loop_counter": loop_counter,
                    "harness_history": harness_history,
                    "next": "junction"
                }
    
    # NEW: If verification was successful AND coverage is good (>=80%), we already moved to the next function above
    # If coverage is below target but no errors, we should refine to improve coverage
    if cbmc_result.get("status") != "SUCCESS" and coverage_percentage < target_coverage and not error_categories:
        logger.info(f"Coverage for {func_name} is {coverage_percentage:.2f}%, which is below target of {target_coverage}%. Refinement needed.")
        
        # Store the error and generate coverage improvement recommendations
        error_id = rag_db.store_error(
            func_name,
            harness_code,
            cbmc_result,
            version_num
        )
        
        # Generate improvement recommendation focused on coverage, but prioritizing successful verification
        improvement_recommendation = generate_coverage_improvement_recommendation(harness_code, func_code, cbmc_result, target_coverage)
        
        # Determine whether to proceed with refinement or move to next function
        if current_attempts < max_refinements - 1:
            # Create update_state with all the necessary information
            update_state = {
                "messages": [AIMessage(content=f"Evaluated harness for {func_name}. Coverage is {coverage_percentage:.2f}%, which is below target of {target_coverage}%. Refinement needed (attempt {version_num} of {max_refinements}).")],
                "refinement_attempts": state_refinement_attempts,
                "processed_functions": state_processed_functions,
                "improvement_recommendation": improvement_recommendation,
                "function_times": function_times,
                "loop_counter": loop_counter,
                "harness_history": harness_history,
                "next": "generator"
            }
            
            # Make sure to pass all persistent error tracking in the state
            if "persistent_errors" in state:
                update_state["persistent_errors"] = state["persistent_errors"]
            if "has_persistent_errors" in state:
                update_state["has_persistent_errors"] = state["has_persistent_errors"]
            if "persistent_error_count" in state:
                update_state["persistent_error_count"] = state["persistent_error_count"]
                
            return update_state
    
    # If verification failed with errors, store the error and generate recommendations
    error_id = rag_db.store_error(
        func_name,
        harness_code,
        cbmc_result,
        version_num
    )
    
    # Parse line-specific errors
    from utils.cbmc_parser import parse_line_specific_errors
    
    stderr = cbmc_result.get("stderr", "")
    stdout = cbmc_result.get("stdout", "")
    line_specific_errors = parse_line_specific_errors(stderr, stdout, harness_code)
    
    # Add line-specific errors to the CBMC result
    cbmc_result["line_specific_errors"] = line_specific_errors
    
    # NEW: Check for coverage.json file for deeper error analysis
    # (Using os and json modules that are already imported at the top of the file)
    
    # Determine the path to the potential coverage.json file
    func_verification_dir = os.path.join(result_directories.get("verification_dir", "verification"), func_name)
    coverage_json_path = os.path.join(func_verification_dir, f"v{version_num}_coverage.json")
    
    # Check if the coverage file exists and attempt to extract detailed error information
    if os.path.exists(coverage_json_path):
        try:
            with open(coverage_json_path, 'r') as f:
                coverage_data = json.load(f)
            
            # Extract detailed error messages from coverage.json
            detailed_errors = []
            error_locations = {}
            
            # Define error categories for classification
            error_categories = {
                "syntax_error": ["syntax error", "expected", "invalid", "unexpected token"],
                "declaration_error": ["not declared", "undeclared", "declaration", "undefined reference"],
                "struct_error": ["member", "not found", "incomplete type", "has no member", "struct"],
                "type_error": ["incompatible type", "invalid conversion", "wrong type", "type mismatch", "no match for", 
                              "conversion from", "cannot convert", "CONVERSION ERROR", "CONVERSION ERROR DETECTED", 
                              "cannot cast", "cast from"],
                "memory_error": ["memory leak", "double free", "invalid free", "use after free", "buffer overflow"],
                "pointer_error": ["null pointer", "invalid pointer", "dereferencing", "dereference"],
                "compilation_error": ["cannot compile", "compilation failed", "error during compilation"],
                "verification_error": ["assert", "assertion", "property", "memory-safety"],
                "linker_error": ["linker", "undefined symbol", "undefined reference"]
            }
            
            # Add coverage.json-specific error types that might not be in stderr
            cbmc_specific_errors = set()
            
            for entry in coverage_data:
                # Process errors and warnings, plus special CBMC message types
                if entry.get("messageType") in ["ERROR", "WARNING", "FAILURE", "STATUS-MESSAGE"]:
                    message = entry.get("messageText", "")
                    
                    # Skip general warning messages
                    if "WARNING: Use --unwinding-assertions" in message or "WARNING: --partial-loops" in message:
                        continue
                        
                    # Get source location if available
                    location = entry.get("sourceLocation", {})
                    file_name = location.get("file", "").split("/")[-1] if location.get("file") else None
                    line_num = location.get("line")
                    func_name = location.get("function", "")
                    
                    # Store error message with context
                    error_info = {
                        "message": message, 
                        "type": entry.get("messageType"),
                        "function": func_name
                    }
                    
                    # Categorize the error message
                    error_category = "other"
                    for category, keywords in error_categories.items():
                        if any(keyword in message.lower() for keyword in keywords):
                            error_category = category
                            break
                    
                    error_info["category"] = error_category
                    
                    # Track specific CBMC error types for detailed analysis
                    if error_category != "other":
                        cbmc_specific_errors.add(error_category)
                    
                    # Add location information if available
                    if file_name and line_num:
                        error_info["file"] = file_name
                        error_info["line"] = line_num
                        
                        # Add to error locations for cross-referencing
                        if file_name not in error_locations:
                            error_locations[file_name] = []
                            
                        if line_num not in error_locations[file_name]:
                            error_locations[file_name].append(line_num)
                    
                    detailed_errors.append(error_info)
            
            # Store the detailed error information in the CBMC result
            if detailed_errors:
                cbmc_result["coverage_json_errors"] = detailed_errors
                logger.info(f"Found {len(detailed_errors)} detailed errors in coverage.json file")
                
                # Update error locations to supplement existing data
                if error_locations:
                    for file_name, lines in error_locations.items():
                        if file_name not in cbmc_result["error_locations"]:
                            cbmc_result["error_locations"][file_name] = []
                            
                        for line in lines:
                            if line not in cbmc_result["error_locations"][file_name]:
                                cbmc_result["error_locations"][file_name].append(line)
                
                # Extract structured error signatures for better error tracking
                if "error_signatures" not in cbmc_result:
                    cbmc_result["error_signatures"] = []
                
                for error in detailed_errors:
                    message = error.get("message", "")
                    category = error.get("category", "other")
                    
                    # Add all error messages to signatures for tracking
                    if message and message not in cbmc_result["error_signatures"]:
                        cbmc_result["error_signatures"].append(message)
                    
                    # Update error categories in the main result
                    if category != "other" and category not in cbmc_result["error_categories"]:
                        cbmc_result["error_categories"].append(category)
                
                # Add specific CBMC error categories to main result
                cbmc_result["cbmc_specific_errors"] = list(cbmc_specific_errors)
                            
        except Exception as e:
            logger.warning(f"Error processing coverage.json file: {str(e)}")
    
    # Generate improvement recommendation
    improvement_recommendation = generate_improvement_recommendation(harness_code, func_code, cbmc_result)
    
    # Add detailed insights from coverage.json errors if available
    if "coverage_json_errors" in cbmc_result and cbmc_result["coverage_json_errors"]:
        coverage_json_errors = cbmc_result["coverage_json_errors"]
        detailed_insights = "\n\n== DETAILED ERROR ANALYSIS FROM COVERAGE.JSON ==\n"
        
        # Use the categorized errors for structured analysis
        # Group errors by their assigned category for better organization
        categorized_errors = {}
        for error in coverage_json_errors:
            category = error.get("category", "other")
            if category not in categorized_errors:
                categorized_errors[category] = []
            
            error_msg = error.get("message", "")
            error_line = error.get("line", "unknown")
            error_file = error.get("file", "unknown")
            error_func = error.get("function", "")
            
            # Create a formatted error message
            location_info = f"Line {error_line}"
            if error_func:
                location_info += f" in {error_func}"
            
            error_info = f"{location_info}: {error_msg}"
            categorized_errors[category].append(error_info)
        
        # Add specific solutions and guidance for each error category
        
        # DECLARATION ERRORS
        if "declaration_error" in categorized_errors:
            declaration_errors = categorized_errors["declaration_error"]
            detailed_insights += "\n🔍 DECLARATION ERRORS - Functions not properly declared:\n"
            for error in declaration_errors:
                detailed_insights += f"- {error}\n"
            
            # Add customized guidance based on specific errors
            has_nondet_error = any("nondet_" in err for err in declaration_errors)
            
            if has_nondet_error:
                detailed_insights += """
💡 SOLUTION FOR NONDET FUNCTION DECLARATIONS:
```c
// Add these declarations at the top of your file
extern int nondet_int(void);
extern unsigned int nondet_uint(void);
extern size_t nondet_size_t(void);
extern char nondet_char(void);
extern char* nondet_string(void);
extern void* nondet_ptr(void);
```
"""
            else:
                detailed_insights += """
💡 SOLUTION FOR FUNCTION DECLARATIONS:
1. Look at the function names mentioned in the errors
2. Add proper 'extern' declarations for each function
3. Make sure the signature matches exactly (return type, params)
4. Place these declarations at the top of your file
5. DO NOT redefine any macros from included headers
"""
        
        # STRUCT ERRORS
        if "struct_error" in categorized_errors:
            struct_errors = categorized_errors["struct_error"]
            detailed_insights += "\n🔍 STRUCT MEMBER ERRORS - Invalid struct field access:\n"
            for error in struct_errors:
                detailed_insights += f"- {error}\n"
            
            # Extract struct names from errors for more specific guidance
            struct_names = set()
            for err in struct_errors:
                # Try to extract struct names like "HTTPRequestInfo_t" from errors
                struct_match = re.search(r'\'(\w+(?:_t)?)\' has no member', err)
                if struct_match:
                    struct_names.add(struct_match.group(1))
            
            # Add specific guidance for struct errors
            detailed_insights += """
💡 SOLUTION FOR STRUCT ERRORS:
1. Include the correct headers that define these structs
2. Use exact field names as defined in the headers
3. Don't invent new fields that don't exist in the struct definition
4. Check capitalization - struct field names are case-sensitive
"""
            
            if struct_names:
                detailed_insights += "\nSpecific structs with issues:\n"
                for struct_name in struct_names:
                    detailed_insights += f"- {struct_name}\n"
        
        # TYPE ERRORS
        if "type_error" in categorized_errors:
            type_errors = categorized_errors["type_error"]
            detailed_insights += "\n🔍 TYPE ERRORS - Incompatible types or conversions:\n"
            for error in type_errors:
                detailed_insights += f"- {error}\n"
                
            detailed_insights += """
💡 SOLUTION FOR TYPE ERRORS:
1. Check that variable types match function parameter types EXACTLY
2. Add explicit type casts using proper C syntax for the target type
3. Be careful with pointer types - make sure they match exactly 
4. Pay special attention to unsigned vs. signed types
5. For pointer type conversions, use (TargetType*)variable to cast properly
6. For integer conversions, use (int), (unsigned int), etc. as needed
7. For struct pointers, ensure you're using the correct struct type
8. Completely avoid implicit conversions between incompatible types
9. For string literals, make sure to cast to (char*) NOT (const char*)
10. For array types, remember arrays decay to pointers - use &array[0] if needed

SPECIFIC TYPE CONVERSION EXAMPLES:
```c
// Casting integer types
int a = 5;
unsigned int b = (unsigned int)a;  // Explicit cast to unsigned

// Casting pointers
void* generic_ptr = malloc(10);
char* char_ptr = (char*)generic_ptr;  // Explicit cast to char*

// Casting struct pointers
struct OriginalType* orig = &original;
struct TargetType* target = (struct TargetType*)orig;  // Explicit struct cast

// String literal handling
const char* str_literal = "test";
char* mutable_str = (char*)str_literal;  // Cast away const (be careful!)

// Array to pointer conversions
char buffer[100];
char* ptr = buffer;  // Arrays decay to pointers naturally
void* void_ptr = (void*)&buffer[0];  // Explicit cast with address
```
"""
        
        # MEMORY ERRORS
        if "memory_error" in categorized_errors:
            memory_errors = categorized_errors["memory_error"]
            detailed_insights += "\n🔍 MEMORY ERRORS - Memory management issues:\n"
            for error in memory_errors:
                detailed_insights += f"- {error}\n"
                
            detailed_insights += """
💡 SOLUTION FOR MEMORY ERRORS:
1. Every malloc() must have a corresponding free()
2. Free memory in the reverse order that you allocated it
3. Add null checks after memory allocation
4. Use stack variables instead of malloc when possible
5. Make sure you're not accessing memory after freeing it
"""
        
        # POINTER ERRORS
        if "pointer_error" in categorized_errors:
            pointer_errors = categorized_errors["pointer_error"]
            detailed_insights += "\n🔍 POINTER ERRORS - Invalid pointer operations:\n"
            for error in pointer_errors:
                detailed_insights += f"- {error}\n"
                
            detailed_insights += """
💡 SOLUTION FOR POINTER ERRORS:
1. Add null checks before dereferencing pointers
2. Initialize pointers to NULL or valid memory
3. Use __CPROVER_assume(ptr != NULL) for inputs
4. Be careful with pointer arithmetic
"""
        
        # COMPILATION ERRORS
        if "compilation_error" in categorized_errors:
            compilation_errors = categorized_errors["compilation_error"]
            detailed_insights += "\n🔍 COMPILATION ERRORS - Critical issues preventing compilation:\n"
            for error in compilation_errors:
                detailed_insights += f"- {error}\n"
                
            detailed_insights += """
💡 SOLUTION FOR COMPILATION ERRORS:
1. Fix the declaration and struct errors first
2. Check for syntax errors (missing semicolons, brackets)
3. Make sure all included headers exist
4. Review the error messages carefully for specific syntax issues
"""
        
        # LINKER ERRORS
        if "linker_error" in categorized_errors:
            linker_errors = categorized_errors["linker_error"]
            detailed_insights += "\n🔍 LINKER ERRORS - Problems with function linkage:\n"
            for error in linker_errors:
                detailed_insights += f"- {error}\n"
                
            detailed_insights += """
💡 SOLUTION FOR LINKER ERRORS:
1. Make sure all functions you call are either:
   - Declared with extern (if they're defined elsewhere)
   - Fully implemented in your harness
2. Check function name spelling exactly
3. Include the correct header files
"""
                
        # OTHER ERRORS
        if "other" in categorized_errors:
            other_errors = categorized_errors["other"]
            detailed_insights += "\n🔍 OTHER ISSUES - Additional warnings and errors:\n"
            for error in other_errors:
                detailed_insights += f"- {error}\n"
                
        # Add a summary of all error categories found
        all_categories = list(categorized_errors.keys())
        detailed_insights += f"\n🔔 SUMMARY: Found errors in {len(all_categories)} categories: {', '.join(all_categories)}\n"
                
        # Add the detailed insights to the recommendation
        improvement_recommendation += detailed_insights
    
    # Add HTTP-specific guidance for HTTP functions even if not at critical error level
    if "HTTPClient" in func_name and "error_signatures" in cbmc_result:
        # Check if any of the errors are about nondet functions or struct members
        error_sigs = cbmc_result.get("error_signatures", [])
        has_http_specific_errors = any("nondet_" in sig or "member" in sig or "not declared" in sig for sig in error_sigs)
        
        if has_http_specific_errors:
            http_specific_guidance = """
            HTTP CLIENT FUNCTION GUIDANCE:
            
            For HTTP Client functions, pay special attention to:
            
            1. STRUCTURE INITIALIZATION:
               - Make sure all HTTPRequestInfo_t and HTTPRequestHeaders_t fields are properly defined
               - Check struct member names against header definitions
            
            2. NONDET FUNCTIONS:
               - Declare all nondet functions at the top of your file:
                 extern int nondet_int(void);
                 extern unsigned int nondet_uint(void);
                 extern size_t nondet_size_t(void);
                 extern char nondet_char(void);
                 extern void* nondet_ptr(void);
            """
            improvement_recommendation += http_specific_guidance
    
    # If we have detected persistent errors, add more emphatic messaging
    if state.get("has_persistent_errors", False) and state.get("persistent_error_count", 0) >= 3:
        # For very persistent errors, add an extremely clear warning message
        improvement_recommendation = f"""
        ⚠️ CRITICAL WARNING: SAME ERRORS PERSISTING FOR {state.get('persistent_error_count', 0)} VERSIONS ⚠️ 
        You MUST take a completely different approach! Previous strategies have failed repeatedly.
        
        {improvement_recommendation}
        
        🚨 DO NOT CONTINUE THE SAME APPROACH - START FRESH! 🚨
        """
        
        # Add HTTP-specific guidance for HTTP functions
        if "HTTPClient" in func_name:
            http_specific_guidance = """
            SPECIALIZED HTTP CLIENT FUNCTION GUIDANCE:
            
            Your harness for this HTTP function is not working correctly. The most common issues are:
            
            1. STRUCT DEFINITIONS & INITIALIZATION:
               - Make sure you correctly declare HTTPRequestInfo_t and HTTPRequestHeaders_t structures
               - Initialize ALL fields in these structures with valid values
               - Don't reference fields that don't exist in the struct definition
            
            2. NONDET FUNCTION DECLARATIONS:
               - You MUST declare all nondet functions used in your harness:
               ```c
               extern int nondet_int(void);
               extern unsigned int nondet_uint(void);
               extern size_t nondet_size_t(void);
               extern char nondet_char(void);
               extern char* nondet_string(void);
               extern void* nondet_ptr(void);
               ```
            
            3. MEMORY MANAGEMENT:
               - Allocate sufficient memory for all buffers and arrays
               - HTTPHeaders should be initialized properly with host, path, etc.
               - Remember to free all allocated memory at the end
            
            EXAMPLE STRUCTURE SETUP:
            ```c
            // Example of properly initializing HTTP structures
            HTTPRequestInfo_t requestInfo;
            memset(&requestInfo, 0, sizeof(HTTPRequestInfo_t));
            requestInfo.method = HTTP_METHOD_GET;
            requestInfo.hostName = "example.com";
            requestInfo.hostNameLength = strlen(requestInfo.hostName);
            requestInfo.pPath = "/api/resource";
            requestInfo.pathLength = strlen(requestInfo.pPath);
            
            HTTPRequestHeaders_t requestHeaders;
            memset(&requestHeaders, 0, sizeof(HTTPRequestHeaders_t));
            ```
            
            Try a completely different approach with these guidelines in mind.
            """
            improvement_recommendation += http_specific_guidance
    
    # Get RAG recommendations
    rag_recommendations = rag_db.get_recommendations(
        func_name, 
        func_code, 
        cbmc_result,
        harness_code
    )
    
    # Modify improvement recommendation with RAG insights
    if rag_recommendations and (rag_recommendations.get('solutions') or rag_recommendations.get('matching_patterns')):
        # Add RAG-driven enhancements to improvement recommendation 
        improvement_recommendation += "\n\n== RAG KNOWLEDGE BASE INSIGHTS ==\n"
        
        # Add similar error insights
        if rag_recommendations.get('similar_errors'):
            improvement_recommendation += "Similar Error Patterns:\n"
            for error in rag_recommendations['similar_errors'][:2]:
                improvement_recommendation += f"- {error.get('error_message', 'Unspecified error')}\n"
        
        # Add solution recommendations
        if rag_recommendations.get('solutions'):
            improvement_recommendation += "\nPrevious Solution Patterns:\n"
            for solution in rag_recommendations['solutions'][:2]:
                effectiveness = solution.get('effectiveness_pct', 0)
                improvement_recommendation += f"- Effectiveness: {effectiveness:.2f}% - Consider similar approaches\n"
        
        # Add matching vulnerability patterns
        if rag_recommendations.get('matching_patterns'):
            improvement_recommendation += "\nMatching Vulnerability Patterns:\n"
            for name, pattern in rag_recommendations['matching_patterns'].items():
                improvement_recommendation += f"- {name}: {pattern.get('description', 'No description')}\n"
    
    # Add details about error counts
    failure_count = cbmc_result.get("failure_count", 0)
    error_count = cbmc_result.get("error_count", 0)
    
    if failure_count > 0 or error_count > 0:
        improvement_recommendation += f"\n\n== ERROR COUNTS ==\n"
        improvement_recommendation += f"FAILURE messages: {failure_count}\n"
        improvement_recommendation += f"Error messages: {error_count}\n"
    
    # Determine whether to proceed with refinement or move to next function
    if current_attempts < max_refinements - 1:
        # Create update_state with all the necessary information
        update_state = {
            "messages": [AIMessage(content=f"Evaluated harness for {func_name}. Needs improvement (attempt {version_num} of {max_refinements}). Using insights from unified knowledge base.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "improvement_recommendation": improvement_recommendation,
            "function_times": function_times,
            "loop_counter": loop_counter,
            "harness_history": harness_history,  # Make sure to return updated harness history
            "next": "generator"
        }
        
        # Make sure to pass all persistent error tracking in the state
        if "persistent_errors" in state:
            update_state["persistent_errors"] = state["persistent_errors"]
        if "has_persistent_errors" in state:
            update_state["has_persistent_errors"] = state["has_persistent_errors"]
        if "persistent_error_count" in state:
            update_state["persistent_error_count"] = state["persistent_error_count"]
        
        return update_state
    else:
        # Last attempt reached, mark as processed and move on
        if func_name not in state_processed_functions:
            state_processed_functions.append(func_name)
        
        return {
            "messages": [AIMessage(content=f"Final refinement attempt for {func_name} completed. Moving to next function.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "loop_counter": loop_counter,
            "harness_history": harness_history,  # Make sure to return updated harness history
            "next": "junction"
        }

def generate_coverage_improvement_recommendation(harness_code, func_code, cbmc_result, target_coverage):
    """
    Generate recommendations specifically focused on improving code coverage.
    
    Args:
        harness_code: The current harness code
        func_code: The original function code
        cbmc_result: The CBMC verification result
        target_coverage: The target coverage percentage
        
    Returns:
        A detailed improvement recommendation focused on coverage
    """
    # Get current coverage metrics
    current_coverage = cbmc_result.get("func_coverage_pct", 0.0)
    
    # Calculate uncovered lines
    uncovered_lines = cbmc_result.get("target_uncovered_lines", 0)
    total_lines = cbmc_result.get("target_total_lines", 0)
    
    # Start building the recommendation
    recommendation = [
        f"== COVERAGE IMPROVEMENT NEEDED ==",
        f"Current coverage: {current_coverage:.2f}%",
        f"Target coverage: {target_coverage:.2f}%",
        f"Uncovered lines: {uncovered_lines} of {total_lines}",
        "\nPRIORITY: Ensure verification succeeds first, then improve coverage.",
        "\nTo improve coverage while maintaining successful verification, consider these strategies:",
    ]
    
    # Analyze function for branch conditions
    if "if" in func_code or "switch" in func_code or "?" in func_code:
        recommendation.append(
            "1. Improve branch coverage by testing more conditional paths:\n"
            "   - Use additional test cases with different values\n"
            "   - Add __CPROVER_assume() statements to direct execution through specific branches\n"
            "   - Consider edge case values that might trigger different code paths"
        )
    
    # Check for loops
    if "for" in func_code or "while" in func_code:
        recommendation.append(
            "2. Improve loop coverage:\n"
            "   - Ensure loops execute at least once\n"
            "   - Consider unwinding loops to a specific depth with --unwind flag\n"
            "   - Test edge cases for loop boundaries"
        )
    
    # Check for error paths
    if "return" in func_code and ("NULL" in func_code or "0" in func_code or "-1" in func_code):
        recommendation.append(
            "3. Ensure error paths are covered:\n"
            "   - Create test cases that trigger error conditions\n"
            "   - Make sure both success and failure paths are exercised"
        )

    
    
    # Add generic recommendations
    recommendation.append(
        "4. General coverage improvements:\n"
        "   - Use nondet values with constraints to target specific execution paths\n"
        "   - Add assertions to verify critical properties along paths\n"
        "   - Structure inputs to exercise different code paths\n"
        "   - Consider adding symbolic values with __CPROVER_nondet functions\n"
        "   - Remember: Prefer a simple harness that passes verification over a complex one that fails"
    )
    
    # Add current harness
    recommendation.append("\nCurrent harness:")
    recommendation.append("```c")
    recommendation.append(harness_code.strip())
    recommendation.append("```")
    
    # Add original function
    recommendation.append("\nOriginal function:")
    recommendation.append("```c")
    recommendation.append(func_code.strip())
    recommendation.append("```")
    
    return "\n".join(recommendation)

def route_from_evaluator(state):
    """Routes from evaluator to either generator (for refinement) or junction (for next function)."""
    return state.get("next", "junction")