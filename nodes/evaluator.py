"""
Enhanced harness evaluator node with improved RAG integration and solution tracking.
"""
import time
import logging
import os
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
    
    # NEW: Check for repeated errors - if same errors in consecutive versions, consider the solution ineffective
    error_categories = cbmc_result.get("error_categories", [])
    previous_error_categories = cbmc_result.get("previous_error_categories", [])
    
    # Track the failure count to monitor progress
    current_failure_count = cbmc_result.get("failure_count", 0)
    
    # Store current failure count and error categories for the next iteration
    previous_cbmc_result = cbmc_results.get(func_name, {})
    if previous_cbmc_result and previous_cbmc_result.get("version", 0) < version_num:
        cbmc_result["previous_failure_count"] = previous_cbmc_result.get("failure_count", 0)
    
    # For this comparison, use both error categories and failure counts
    if error_categories and previous_error_categories:
        previous_failure_count = cbmc_result.get("previous_failure_count", 0)
        
        # Log the actual counts for debugging
        logger.info(f"Previous failure count for {func_name}: {previous_failure_count}")
        logger.info(f"Current failure count for {func_name}: {current_failure_count}")
        
        # First, retrieve any existing persistent_errors from the state
        state_persistent_errors = state.get("persistent_errors", {})
        if func_name not in state_persistent_errors:
            state_persistent_errors[func_name] = {}
        
        # Check for persistent errors across versions by comparing error categories
        if set(error_categories) == set(previous_error_categories) and current_failure_count >= previous_failure_count and current_failure_count > 0:
            logger.warning(f"Same errors persist between versions for {func_name} with no improvement in failures. This solution is ineffective.")
            
            # Update persistent errors counter in state AND in CBMC result
            for error in error_categories:
                if error not in state_persistent_errors[func_name]:
                    state_persistent_errors[func_name][error] = 1
                else:
                    state_persistent_errors[func_name][error] += 1
                
                # Find the highest persistence count for any error
                max_persistence = max(state_persistent_errors[func_name].values())
                
                # Log this for debugging
                logger.warning(f"Error '{error}' has persisted for {state_persistent_errors[func_name][error]} versions (max: {max_persistence})")
                
                # Set flags directly for generator to use
                state["has_persistent_errors"] = True
                state["persistent_error_count"] = max_persistence
            
            # Update the persistent errors in cbmc_result
            cbmc_result["persistent_errors"] = state_persistent_errors[func_name]
            
            # Also update error-specific persistence counts
            for err_cat in error_categories:
                persistence_key = f"persistence_{err_cat}"
                cbmc_result[persistence_key] = state_persistent_errors[func_name].get(err_cat, 1)
            
            # Mark the solution as ineffective in the RAG database
            rag_db.mark_ineffective_solution(func_name, version_num-1)
        else:
            # Reset persistent error counts for categories that have been fixed
            for error in previous_error_categories:
                if error not in error_categories and error in state_persistent_errors[func_name]:
                    logger.info(f"Error '{error}' has been fixed for {func_name}")
                    del state_persistent_errors[func_name][error]
                    
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
        logger.info(f"CBMC verification successful for {func_name}, storing solution in RAG database")
        
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
            "messages": [AIMessage(content=f"CBMC verification successful for {func_name}. Solution stored in knowledge base. Moving to next function.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "function_times": function_times,
            "loop_counter": loop_counter,
            "harness_history": harness_history,  # Make sure to return updated harness history
            "next": "junction"
        }
    
    # NEW: If coverage is below target but no errors, we should refine to improve coverage
    if cbmc_result.get("status") != "SUCCESS" and coverage_percentage < target_coverage and not error_categories:
        logger.info(f"Coverage for {func_name} is {coverage_percentage:.2f}%, which is below target of {target_coverage}%. Refinement needed.")
        
        # Store the error and generate coverage improvement recommendations
        error_id = rag_db.store_error(
            func_name,
            harness_code,
            cbmc_result,
            version_num
        )
        
        # Generate improvement recommendation focused on coverage
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
    
    # Generate improvement recommendation
    improvement_recommendation = generate_improvement_recommendation(harness_code, func_code, cbmc_result)
    
    # If we have detected persistent errors, add more emphatic messaging
    if state.get("has_persistent_errors", False) and state.get("persistent_error_count", 0) >= 3:
        # For very persistent errors, add an extremely clear warning message
        improvement_recommendation = f"""
        ⚠️ CRITICAL WARNING: SAME ERRORS PERSISTING FOR {state.get('persistent_error_count', 0)} VERSIONS ⚠️ 
        You MUST take a completely different approach! Previous strategies have failed repeatedly.
        
        {improvement_recommendation}
        
        🚨 DO NOT CONTINUE THE SAME APPROACH - START FRESH! 🚨
        """
    
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
        "\nTo improve coverage, consider the following strategies:",
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
        "   - Consider adding symbolic values with __CPROVER_nondet functions"
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