"""
Junction node for CBMC harness generator workflow.
"""
from langchain_core.messages import AIMessage

def junction_node(state):
    """Processes vulnerable functions one at a time in sequential order."""
    # Get the list of vulnerable functions and processed functions
    vulnerable_functions = state.get("vulnerable_functions", [])
    processed_functions = state.get("processed_functions", [])
    
    # Safety counter to prevent infinite recursion
    loop_counter = state.get("loop_counter", 0) + 1
    
    # Force termination if loop counter gets too high
    if loop_counter > 50:
        return {
            "messages": [AIMessage(content=f"WARNING: Loop counter exceeded maximum value. Forcing termination to avoid recursion error.")],
            "loop_counter": 0,  # Reset counter
            "next": "output"
        }
    
    # Track the progress
    total_functions = len(vulnerable_functions)
    completed_functions = len(processed_functions)
    
    # Check if we've processed all functions
    if completed_functions >= total_functions:
        return {
            "messages": [AIMessage(content=f"All {total_functions} functions have been processed. Moving to final output.")],
            "loop_counter": 0,  # Reset counter
            "next": "output"
        }
    
    # Get current function being processed
    current_function = state.get("current_function", "")
    
    # Important fix: If current function is in processed_functions, clear it
    if current_function and current_function in processed_functions:
        # This should never happen, but if it does, reset the current function
        current_function = ""
    
    # If we have a valid current function that's not processed, continue with it
    if current_function and current_function in vulnerable_functions and current_function not in processed_functions:
        return {
            "messages": [AIMessage(content=f"Continuing processing of function: {current_function}")],
            "current_function": current_function,
            "loop_counter": loop_counter,
            "next": "generator"
        }
    
    # Find the next unprocessed function
    for func in vulnerable_functions:
        if func not in processed_functions:
            # Select this function as the next to process
            return {
                "messages": [AIMessage(content=f"Processing function {completed_functions + 1} of {total_functions}: {func}")],
                "current_function": func,
                "loop_counter": loop_counter,
                "next": "generator"
            }
    
    # Fallback (should not reach here if logic is correct)
    return {
        "messages": [AIMessage(content="All functions appear to be processed. Moving to output.")],
        "loop_counter": 0,  # Reset counter
        "next": "output"
    }

def route_from_junction(state):
    """Routes from junction to either generator or output."""
    return state.get("next", "generator")