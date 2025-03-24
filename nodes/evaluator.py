"""
Harness evaluator node for CBMC harness generator workflow.
"""
import time
from langchain_core.messages import AIMessage
from core.embedding_db import code_collection

def harness_evaluator_node(state):
    """Evaluates the quality of generated harnesses based on CBMC output and suggests improvements."""
    evaluation_start = time.time()
    
    # SAFETY: Get and increment loop counter to prevent infinite recursion
    loop_counter = state.get("loop_counter", 0)
    print(f"DEBUG: Evaluator node - function: {state.get('current_function', '')}, loop: {loop_counter}")
    
    func_name = state.get("current_function", "")
    harnesses = state.get("harnesses", {})
    cbmc_results = state.get("cbmc_results", {})
    
    # Get error tracking dictionaries
    cbmc_error_messages = state.get("cbmc_error_messages", {})
    harness_syntax_errors = state.get("harness_syntax_errors", {})
    parsing_issues = state.get("parsing_issues", {})
    verification_failures = state.get("verification_failures", {})
    
    # SAFETY: Initialize refinement_attempts if not present for this function
    refinement_attempts = state.get("refinement_attempts", {}).copy()
    if func_name not in refinement_attempts:
        refinement_attempts[func_name] = 0
    
    # Get current attempts count
    current_attempts = refinement_attempts.get(func_name, 0)
    print(f"DEBUG: Current refinement attempts for {func_name}: {current_attempts}")
    
    # SAFETY: Force progression after max attempts regardless of other conditions
    max_refinements = 3
    if current_attempts >= max_refinements:
        processed_functions = state.get("processed_functions", []).copy()
        if func_name not in processed_functions:
            processed_functions.append(func_name)
            print(f"DEBUG: Max refinements reached, marking {func_name} as processed")
        
        return {
            "messages": [AIMessage(content=f"Maximum refinement attempts ({max_refinements}) reached for {func_name}. Moving to next function.")],
            "refinement_attempts": refinement_attempts,
            "processed_functions": processed_functions,
            "loop_counter": loop_counter,
            "next": "junction"
        }
    
    # SAFETY: Handle missing data
    harness_code = harnesses.get(func_name, "")
    cbmc_result = cbmc_results.get(func_name, {})
    
    if not harness_code or not cbmc_result:
        # Mark this function as processed even if there was an error
        processed_functions = state.get("processed_functions", []).copy()
        if func_name and func_name not in processed_functions:
            processed_functions.append(func_name)
            print(f"DEBUG: Missing harness/CBMC data, marking {func_name} as processed")
        
        return {
            "messages": [AIMessage(content=f"Error: Missing harness or CBMC result for function {func_name}. Marking as processed.")],
            "processed_functions": processed_functions,
            "loop_counter": loop_counter,
            "next": "junction"  # Move to next function
        }
    
    # Extract function details from code database
    function_result = code_collection.get(ids=[func_name], include=["documents", "metadatas"])
    if not function_result["ids"]:
        # Mark this function as processed even if there's an error
        processed_functions = state.get("processed_functions", []).copy()
        if func_name not in processed_functions:
            processed_functions.append(func_name)
            print(f"DEBUG: Function metadata not found, marking {func_name} as processed")
        
        return {
            "messages": [AIMessage(content=f"Error: Function {func_name} metadata not found. Marking as processed.")],
            "processed_functions": processed_functions,
            "loop_counter": loop_counter,
            "next": "junction"
        }
    
    func_code = function_result["documents"][0]
    func_metadata = function_result["metadatas"][0]
    
    # Get CBMC output
    cbmc_stdout = cbmc_result.get("stdout", "")
    cbmc_status = cbmc_result.get("status", "UNKNOWN")
    verification_message = cbmc_result.get("message", "")
    suggestions = cbmc_result.get("suggestions", "")
    
    # Check for syntax errors, parsing issues, and other error types from CBMC
    has_syntax_error = cbmc_result.get("has_syntax_error", False) or func_name in harness_syntax_errors
    has_parsing_issue = cbmc_result.get("has_parsing_issue", False) or func_name in parsing_issues
    verification_failure_types = cbmc_result.get("verification_failure_types", [])
    
    # Set evaluation criteria for harness quality
    evaluation_criteria = {
        "has_nondet_inputs": "__CPROVER_" in harness_code and "nondet" in harness_code,
        "has_assertions": "__CPROVER_assert" in harness_code,
        "has_assumptions": "__CPROVER_assume" in harness_code,
        "checks_memory_leaks": "memory leak" in harness_code.lower() or "free" in harness_code,
        "checks_bounds": "bounds" in harness_code.lower() or "index" in harness_code.lower(),
        "checks_arithmetic": any(op in harness_code for op in ["overflow", "division", "zero"]),
        "addresses_cbmc_errors": False,
        "verification_passed": cbmc_status == "SUCCESS",
        "syntactically_valid": not has_syntax_error and not has_parsing_issue
    }
    
    # Calculate overall quality score
    quality_score = sum(1 for criterion, value in evaluation_criteria.items() if value) / len(evaluation_criteria)
    quality_score = round(quality_score * 100)
    
    # Build the improvement recommendation based on CBMC results
    improvement_recommendation = ""
    needs_improvement = False
    
    # First handle syntax errors and parsing issues
    if has_syntax_error or has_parsing_issue:
        needs_improvement = True
        error_message = cbmc_error_messages.get(func_name, "Unknown error")
        syntax_error = harness_syntax_errors.get(func_name, "")
        
        improvement_recommendation = f"""
        Previous harness for {func_name} has syntax or parsing errors and needs to be fixed.
        
        CBMC error: {error_message}
        
        Syntax error details: {syntax_error}
        
        Current harness (with errors):
        ```c
        {harness_code}
        ```
        
        Original function:
        ```c
        {func_code}
        ```
        
        Please fix the syntax or parsing errors in the harness. Specifically:
        1. Make sure all variables are properly declared before use
        2. Check for balanced braces and proper function definitions
        3. Ensure all code is complete and not truncated
        4. Include all necessary header files
        
        Generate a complete, syntactically valid harness that can be properly compiled and analyzed by CBMC.
        """
    # Then handle verification failures
    elif cbmc_status != "SUCCESS" and verification_failure_types:
        needs_improvement = True
        
        # Analyze memory issues
        memory_issues = []
        if "memory_leak" in verification_failure_types:
            memory_issues.append("Memory leaks detected - ensure all allocated memory is freed")
        if "null_pointer" in verification_failure_types:
            memory_issues.append("Null pointer dereferences - add null pointer checks")
            
        # Analyze arithmetic issues
        arithmetic_issues = []
        if "division_by_zero" in verification_failure_types:
            arithmetic_issues.append("Division by zero - add checks to ensure divisors are non-zero")
        if "arithmetic_overflow" in verification_failure_types or "pointer_overflow" in verification_failure_types:
            arithmetic_issues.append("Arithmetic/pointer overflow - add bounds checking")
            
        # Analyze array bounds issues
        array_issues = []
        if "array_bounds" in verification_failure_types:
            array_issues.append("Array bounds violations - verify array indices are within bounds")
            
        # Analyze type conversion issues
        type_issues = []
        if "type_conversion" in verification_failure_types:
            type_issues.append("Type conversion problems - check for information loss in type conversions")
            
        improvement_recommendation = f"""
        Previous harness for {func_name} failed CBMC verification. Quality score: {quality_score}%.
        
        CBMC verification status: {cbmc_status}
        
        CBMC error message: {verification_message}
        
        Suggested fixes: {suggestions}
        
        CBMC output excerpt:
        {cbmc_stdout[:500] if len(cbmc_stdout) > 500 else cbmc_stdout}
        
        Current harness:
        ```c
        {harness_code}
        ```
        
        Original function:
        ```c
        {func_code}
        ```
        
        Please improve the harness to address the following issues:
        
        {', '.join(memory_issues) if memory_issues else ''}
        {', '.join(arithmetic_issues) if arithmetic_issues else ''}
        {', '.join(array_issues) if array_issues else ''}
        {', '.join(type_issues) if type_issues else ''}
        
        Generate a complete, working harness that properly tests the function and passes CBMC verification.
        
        Refinement attempt: {current_attempts + 1} of {max_refinements}
        """
    # Finally evaluate general harness quality
    else:
        # Determine if improvement is needed
        needs_improvement = (
            cbmc_status != "SUCCESS" or 
            quality_score < 70 or
            not evaluation_criteria["has_nondet_inputs"] or
            not evaluation_criteria["has_assertions"] or
            (func_metadata.get("has_malloc", False) and not evaluation_criteria["checks_memory_leaks"]) or
            not evaluation_criteria["syntactically_valid"]
        )
        
        if needs_improvement and not has_syntax_error and not has_parsing_issue:
            improvement_areas = []
            
            # Generate specific improvement suggestions
            if not evaluation_criteria["has_nondet_inputs"]:
                improvement_areas.append("Use CBMC's nondet functions for inputs")
            
            if not evaluation_criteria["has_assertions"]:
                improvement_areas.append("Add CPROVER assertions to verify behavior")
            
            if not evaluation_criteria["has_assumptions"]:
                improvement_areas.append("Use CPROVER assumptions to constrain input values")
            
            if func_metadata.get("has_malloc", False) and not evaluation_criteria["checks_memory_leaks"]:
                improvement_areas.append("Add memory leak verification")
            
            improvement_recommendation = f"""
            Previous harness for {func_name} needs improvement. Quality score: {quality_score}%.
            
            CBMC verification status: {cbmc_status}
            
            Current harness:
            ```c
            {harness_code}
            ```
            
            Original function:
            ```c
            {func_code}
            ```
            
            Identified issues:
            {', '.join(improvement_areas)}
            
            Please improve the harness to address these issues. Generate a complete, working harness that properly tests the function.
            
            Refinement attempt: {current_attempts + 1} of {max_refinements}
            """
    
    # Calculate evaluation time
    evaluation_time = time.time() - evaluation_start
    
    # Update function times dictionary
    function_times = state.get("function_times", {}).copy()
    if func_name not in function_times:
        function_times[func_name] = {}
    function_times[func_name]["evaluation"] = evaluation_time
    
    # CRITICAL: Update refinement attempts BEFORE returning
    # This ensures we don't get stuck in an infinite loop
    if needs_improvement:
        refinement_attempts[func_name] = current_attempts + 1
        print(f"DEBUG: Incremented refinement attempts for {func_name} to {refinement_attempts[func_name]}")
    
    # CRITICAL: Mark as processed if NOT going to refine
    # This ensures forward progress in the workflow
    processed_functions = state.get("processed_functions", []).copy()
    if not needs_improvement:
        if func_name not in processed_functions:
            processed_functions.append(func_name)
            print(f"DEBUG: No more improvements needed, marking {func_name} as processed")
    
    # CRITICAL: Return loop_counter to prevent recursive error
    return {
        "messages": [AIMessage(content=f"Evaluated harness for {func_name} in {evaluation_time:.2f}s. {cbmc_status}. {'Improvements needed.' if needs_improvement else 'No improvements needed.'}")],
        "refinement_attempts": refinement_attempts,
        "processed_functions": processed_functions,
        "improvement_recommendation": improvement_recommendation,
        "function_times": function_times,
        "loop_counter": loop_counter,  # Pass the loop counter to maintain recursion tracking
        "next": "generator" if needs_improvement else "junction"
    }

def route_from_evaluator(state):
    """Routes from evaluator to either generator (for refinement) or junction (for next function)."""
    return state.get("next", "junction")