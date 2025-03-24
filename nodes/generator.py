"""
Generator node for CBMC harness generator workflow.
"""
import time
import os
import re
import json
from langchain_core.messages import AIMessage, HumanMessage
from core.embedding_db import code_collection, query_pattern_db
from utils.llm_utils import setup_llm

# Initialize the LLM
llm = setup_llm()

def generator_node(state):
    """Generates or refines CBMC-compatible harness for the current function with timing."""
    import time
    import os
    generation_start = time.time()
    
    func_name = state.get("current_function", "")
    
    # Check if this is a refinement call
    improvement_recommendation = state.get("improvement_recommendation", "")
    is_refinement = bool(improvement_recommendation)
    
    # Track harness history in the state if not already present
    harness_history = state.get("harness_history", {})
    if func_name not in harness_history:
        harness_history[func_name] = []
    
    # Get the previous harness if this is a refinement
    previous_harness = ""
    if is_refinement and func_name in state.get("harnesses", {}):
        previous_harness = state.get("harnesses", {})[func_name]
        # Add to history if not already there
        if previous_harness not in harness_history[func_name]:
            harness_history[func_name].append(previous_harness)
    
    # Get function code from CodeDB if not refining
    if not is_refinement:
        function_result = code_collection.get(ids=[func_name], include=["documents", "metadatas"])
        
        if not function_result["ids"]:
            return {
                "messages": [AIMessage(content=f"Error: Function {func_name} not found in database.")],
                "next": "junction"  # Return to junction to process next function
            }
        
        func_code = function_result["documents"][0]
        func_metadata = function_result["metadatas"][0]
        
        # Get pattern information from PatternDB
        patterns_result = query_pattern_db(func_code)
        
        # Analyze function to determine which checks are actually needed
        has_malloc = "malloc(" in func_code
        has_free = "free(" in func_code
        has_array_access = "[" in func_code and "]" in func_code
        has_pointer_arithmetic = "*" in func_code or "->" in func_code
        has_division = "/" in func_code or "%" in func_code
        has_type_conversion = "(" in func_code and ")" in func_code and any(type_name in func_code for type_name in ["int", "char", "float", "double", "size_t", "unsigned", "long"])
        
        # Produce targeted verification guide based on actual function contents
        verification_checks = []
        if has_malloc or has_free:
            verification_checks.append("--memory-leak-check: Verify memory is properly allocated and freed")
        if has_array_access:
            verification_checks.append("--bounds-check: Verify array accesses are within bounds")
        if has_pointer_arithmetic:
            verification_checks.append("--pointer-overflow-check: Verify pointer arithmetic is safe")
        if has_division:
            verification_checks.append("--div-by-zero-check: Verify divisors are non-zero")
        if has_type_conversion:
            verification_checks.append("--conversion-check: Verify type conversions are safe")
        
        # Construct the verification guide
        if verification_checks:
            verification_guide = "Relevant CBMC Verification Checks for this function:\n" + "\n".join(verification_checks)
        else:
            verification_guide = "This function doesn't appear to need special CBMC verification checks beyond basic assertions."
        
        # Clear guidance about avoiding unnecessary mocks
        cbmc_verification_info = f"""
        {verification_guide}
        
        IMPORTANT GUIDELINES:
        
        1. Do NOT create mock implementations that aren't necessary for verification.
        2. Focus ONLY on testing the actual function behavior, not on artificial scenarios.
        3. Only implement verification checks that are relevant to this specific function.
        4. Avoid creating test cases for verification types that don't apply to this function.
        5. Keep the harness minimal and focused on real potential issues.
        
        The harness should:
        - Use __CPROVER_assert() only for properties that could actually fail in this function
        - Use __CPROVER_assume() to specify realistic input constraints
        - Use nondet functions like nondet_int() for inputs that need to be nondeterministic
        """
        
        # Build generator prompt with focused verification
        generator_prompt = f"""
        You are a specialized harness generator for CBMC verification.
        Create a MINIMAL, FOCUSED harness for the following function WITHOUT unnecessary mocks:
        
        ```c
        {func_code}
        ```
        
        Function metadata:
        - Return type: {func_metadata.get("return_type", "void")}
        - Parameters: {func_metadata.get("params", "")}
        - Contains malloc: {has_malloc}
        - Contains free: {has_free}
        
        Matching vulnerability patterns:
        {json.dumps(patterns_result.get('matching_patterns', {}), indent=2)}
        
        {cbmc_verification_info}
        
        CRITICAL INSTRUCTIONS:
        1. DO NOT create mock implementations of functions that aren't directly related to verification
        2. DO NOT implement stubs or test code just to satisfy CBMC checklist items
        3. ONLY verify properties that are relevant to this specific function
        4. DO NOT add checks for issues that cannot occur in this function
        5. Keep the harness SMALL and FOCUSED - don't add anything that isn't necessary
        6. If function dependencies are unavailable, minimize assumptions rather than creating elaborate mocks
        7. Follow CBMC's harness structure with a void main() function
        
        Provide only the minimal, focused harness code without explanation.
        """
    else:
        # For refinement, use targeted improvement guidance
        generator_prompt = f"""
        You are a specialized harness generator for CBMC verification.
        You need to REFINE an existing harness based on evaluation feedback, focusing on ELIMINATING UNNECESSARY MOCKS.
        
        {improvement_recommendation}
        
        Previous harness code that you should improve:
        ```c
        {previous_harness}
        ```
        
        Create an improved version of the harness that addresses the identified issues while REMOVING UNNECESSARY CODE.
        
        CRITICAL INSTRUCTIONS:
        1. REMOVE any mock implementations that aren't directly necessary for verification
        2. ELIMINATE any test code that's just there to satisfy CBMC checklist items
        3. FOCUS only on testing real properties of the function that matter
        4. SIMPLIFY the harness - remove anything that isn't directly testing the function
        5. KEEP only the minimal verification needed to properly test the function
        6. AVOID adding checks for issues that cannot occur in this function
        
        The harness must use CBMC's special functions:
        - __CPROVER_assert() for verification of properties that actually matter
        - __CPROVER_assume() for realistic constraints
        - nondet functions for inputs
        
        Make sure your harness is complete and properly formatted.
        
        Provide only the improved, minimal harness code without explanation.
        """
    
    # Generate the harness
    try:
        # Setup messages for the LLM
        response = llm.invoke([
            HumanMessage(content=generator_prompt)
        ])
        
        # Extract the harness code
        harness_code = response.content
        match = re.search(r'```(?:c)?\n(.+?)\n```', harness_code, re.DOTALL)
        if match:
            harness_code = match.group(1)
        
        # Validate harness completeness
        has_main = "void main(" in harness_code or "int main(" in harness_code
        balanced_braces = harness_code.count("{") <= harness_code.count("}")
        
        if not has_main or not balanced_braces:
            print(f"Warning: Harness for {func_name} may be incomplete. Adding necessary closing elements.")
            
            # Try to fix incomplete harnesses
            if not balanced_braces:
                missing_braces = harness_code.count("{") - harness_code.count("}")
                if missing_braces > 0:
                    harness_code += "\n" + ("}" * missing_braces)
            
            # Make sure there's a main function
            if not has_main:
                if "int main" not in harness_code and "void main" not in harness_code:
                    harness_code += "\n\nvoid main() {\n    // Auto-generated main function\n}"
        
        # Save the new harness to history
        if harness_code not in harness_history[func_name]:
            harness_history[func_name].append(harness_code)
        
        # Update the harnesses dictionary
        harnesses = state.get("harnesses", {}).copy()
        harnesses[func_name] = harness_code
        
        # Determine iteration number for filename
        refinement_num = state.get("refinement_attempts", {}).get(func_name, 0)
        version_num = refinement_num + 1
        
        # Create organized directory structure for harnesses
        harness_base_dir = "harnesses"
        os.makedirs(harness_base_dir, exist_ok=True)
        
        # Create function-specific directory
        func_harness_dir = os.path.join(harness_base_dir, func_name)
        os.makedirs(func_harness_dir, exist_ok=True)
        
        # Save harness file
        filename = os.path.join(func_harness_dir, f"v{version_num}.c")
        
        # Save harness to file with explicit buffer flushing
        with open(filename, "w") as f:
            f.write(harness_code)
            f.flush()
            os.fsync(f.fileno())  # Force flush to disk
        
        # Calculate time spent on generation
        generation_time = time.time() - generation_start
        
        # Update function times dictionary
        function_times = state.get("function_times", {}).copy()
        if func_name not in function_times:
            function_times[func_name] = {}
        function_times[func_name]["generation"] = generation_time
        
        # Clear improvement recommendation after processing
        return {
            "messages": [AIMessage(content=f"{'Refined' if is_refinement else 'Generated'} minimal, focused harness for function {func_name} in {generation_time:.2f}s (without unnecessary mocks)")],
            "harnesses": harnesses,
            "harness_history": harness_history,
            "improvement_recommendation": "",
            "function_times": function_times,
            "next": "cbmc"  # Proceed to CBMC verification
        }
        
    except Exception as e:
        # Handle API errors
        error_msg = str(e)
        
        # Calculate time even for errors
        generation_time = time.time() - generation_start
        
        # Update function times dictionary
        function_times = state.get("function_times", {}).copy()
        if func_name not in function_times:
            function_times[func_name] = {}
        function_times[func_name]["generation_error"] = generation_time
        
        return {
            "messages": [AIMessage(content=f"Error {'refining' if is_refinement else 'generating'} harness for function {func_name} in {generation_time:.2f}s: {error_msg}")],
            "improvement_recommendation": "",
            "function_times": function_times,
            "next": "junction"  # Return to junction to process next function
        }

def route_from_generator(state):
    """Routes from generator to either cbmc or junction."""
    return state.get("next", "cbmc")