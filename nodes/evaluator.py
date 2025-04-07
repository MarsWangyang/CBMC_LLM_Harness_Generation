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
    max_refinements = 9  # Maximum number of refinement attempts
    
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
    
    # Check if verification was successful
    if cbmc_result.get("status") == "SUCCESS":
        logger.info(f"CBMC verification successful for {func_name}, storing solution in RAG database")
        
        # Store solution in RAG database (error_id will be empty as there's no error)
        solution_id = rag_db.store_solution(
            "",  # No error ID for successful verification
            func_name, 
            harness_code, 
            cbmc_result,
            current_attempts + 1
        )
        
        # RESET: Clear existing error and solution data for this function
        try:
            # Delete existing errors for this function from error collection
            existing_errors = rag_db.error_collection.get(
                where={"func_name": func_name}
            )
            if existing_errors["ids"]:
                rag_db.error_collection.delete(ids=existing_errors["ids"])
            
            # Delete existing solutions for this function from solution collection
            existing_solutions = rag_db.solution_collection.get(
                where={"func_name": func_name}
            )
            if existing_solutions["ids"]:
                rag_db.solution_collection.delete(ids=existing_solutions["ids"])
            
            logger.info(f"Cleared existing error and solution data for {func_name}")
        except Exception as e:
            logger.warning(f"Error resetting RAG data for {func_name}: {str(e)}")
        
        # Mark function as processed
        if func_name not in state_processed_functions:
            state_processed_functions.append(func_name)
        
        return {
            "messages": [AIMessage(content=f"CBMC verification successful for {func_name}. Solution stored in knowledge base. Moving to next function.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "function_times": function_times,
            "loop_counter": loop_counter,
            "next": "junction"
        }
    
    # If verification failed, store the error and generate recommendations
    error_id = rag_db.store_error(
        func_name,
        harness_code,
        cbmc_result,
        current_attempts
    )
    
    # Generate improvement recommendation
    improvement_recommendation = generate_improvement_recommendation(harness_code, func_code, cbmc_result)
    
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
    
    # Determine whether to proceed with refinement or move to next function
    if current_attempts < max_refinements - 1:
        state_refinement_attempts[func_name] = current_attempts + 1

        
        return {
            "messages": [AIMessage(content=f"Evaluated harness for {func_name}. Needs improvement (attempt {current_attempts + 1} of {max_refinements}). Using insights from unified knowledge base.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "improvement_recommendation": improvement_recommendation,
            "function_times": function_times,
            "loop_counter": loop_counter,
            "next": "generator"
        }
    else:
        # Last attempt reached, mark as processed and move on
        if func_name not in state_processed_functions:
            state_processed_functions.append(func_name)
        state_refinement_attempts[func_name] = max_refinements
        
        # RESET: Clear existing error and solution data when max refinements reached
        try:
            # Delete existing errors for this function from error collection
            existing_errors = rag_db.error_collection.get(
                where={"func_name": func_name}
            )
            if existing_errors["ids"]:
                rag_db.error_collection.delete(ids=existing_errors["ids"])
            
            # Delete existing solutions for this function from solution collection
            existing_solutions = rag_db.solution_collection.get(
                where={"func_name": func_name}
            )
            if existing_solutions["ids"]:
                rag_db.solution_collection.delete(ids=existing_solutions["ids"])
            
            logger.info(f"Cleared RAG data for {func_name} after reaching max refinement attempts")
        except Exception as e:
            logger.warning(f"Error resetting RAG data for {func_name} after max refinements: {str(e)}")
        
        return {
            "messages": [AIMessage(content=f"Final refinement attempt for {func_name} completed. Moving to next function.")],
            "refinement_attempts": state_refinement_attempts,
            "processed_functions": state_processed_functions,
            "loop_counter": loop_counter,
            "next": "junction"
        }

def route_from_evaluator(state):
    """Routes from evaluator to either generator (for refinement) or junction (for next function)."""
    return state.get("next", "junction")