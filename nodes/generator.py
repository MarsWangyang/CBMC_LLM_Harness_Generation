"""
Generator node for CBMC harness generator workflow with unified RAG enhancement.
"""
import time
import os
import re
import json
import logging
from langchain_core.messages import AIMessage, HumanMessage, SystemMessage
from core.embedding_db import code_collection
from utils.rag import get_unified_db

# Set up logging
logger = logging.getLogger("generator")

# Add to generator.py - Enhanced header analysis and macro extraction

def extract_project_functions(rag_db):
    """
    Extract all function declarations and macros from headers and source files in the RAG database.
    
    Args:
        rag_db: The unified RAG database
        
    Returns:
        Dictionary mapping header names to lists of function declarations and macros
    """
    project_functions = {}
    project_macros = {}
    
    try:
        # Use the rag_db collections directly
        code_coll = rag_db.code_collection
        
        # First gather all available headers
        available_headers = []
        
        # Query all documents that are headers
        try:
            header_results = code_coll.get(
                include=["documents", "metadatas"],
                where={"type": "header"}
            )
            
            # Process each header
            if header_results["ids"]:
                for i, header_id in enumerate(header_results["ids"]):
                    if "header:" in header_id:
                        header_name = header_id.replace("header:", "")
                        available_headers.append(header_name)
                        # Initialize the entry in project_functions
                        project_functions[header_name] = []
                        project_macros[header_name] = []
                        
                        # Extract declarations from header content if available
                        if "documents" in header_results and i < len(header_results["documents"]):
                            header_content = header_results["documents"][i]
                            
                            # Extract function declarations
                            func_decl_pattern = r'([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)\s*;'
                            for match in re.finditer(func_decl_pattern, header_content, re.MULTILINE):
                                return_type = match.group(1).strip()
                                func_name = match.group(2).strip()
                                params = match.group(3).strip()
                                
                                # Add to function declarations
                                project_functions[header_name].append({
                                    "name": func_name,
                                    "return_type": return_type,
                                    "params": params,
                                    "declaration": match.group(0)
                                })
                            
                            # Extract macro definitions
                            macro_pattern = r'#define\s+(\w+)(?:\(([^)]*)\))?\s+(.+?)(?:\n|$)'
                            for match in re.finditer(macro_pattern, header_content, re.MULTILINE):
                                macro_name = match.group(1)
                                macro_params = match.group(2)
                                macro_value = match.group(3).strip()
                                
                                # Add to macro definitions
                                project_macros[header_name].append({
                                    "name": macro_name,
                                    "params": macro_params,
                                    "value": macro_value,
                                    "definition": match.group(0).strip()
                                })
            
            logger.info(f"Found {len(available_headers)} header files")
        except Exception as e:
            logger.error(f"Error processing headers: {str(e)}")
        
        # Now get all function declarations
        try:
            decl_results = code_coll.get(
                include=["documents", "metadatas"],
                where={"type": "function_declaration"}
            )
            
            # Process each declaration
            if decl_results["ids"]:
                for i, decl_id in enumerate(decl_results["ids"]):
                    if i < len(decl_results["metadatas"]):
                        metadata = decl_results["metadatas"][i]
                        
                        # Get header name
                        header_name = metadata.get("header", "unknown")
                        
                        # Skip if it's a pattern match
                        if "pattern:" in decl_id or metadata.get("is_keyword", False):
                            continue
                        
                        # Initialize header entry if not exists
                        if header_name not in project_functions:
                            project_functions[header_name] = []
                        
                        # Create function declaration entry
                        func_name = metadata.get("name", "")
                        return_type = metadata.get("return_type", "void")
                        params = metadata.get("params", "")
                        
                        if func_name and i < len(decl_results["documents"]):
                            declaration = decl_results["documents"][i]
                            
                            # Add to function declarations if not already there
                            existing_names = [f["name"] for f in project_functions[header_name]]
                            if func_name not in existing_names:
                                project_functions[header_name].append({
                                    "name": func_name,
                                    "return_type": return_type,
                                    "params": params,
                                    "declaration": declaration
                                })
            
            # Count total function declarations
            total_decls = sum(len(funcs) for funcs in project_functions.values())
            logger.info(f"Found {total_decls} function declarations across {len(project_functions)} headers")
            
            # Count total macros
            total_macros = sum(len(macros) for macros in project_macros.values())
            logger.info(f"Found {total_macros} macro definitions across {len(project_macros)} headers")
        except Exception as e:
            logger.error(f"Error processing function declarations: {str(e)}")
        
        # Combine macros with functions in the result
        combined_result = {}
        for header in set(list(project_functions.keys()) + list(project_macros.keys())):
            combined_result[header] = {
                "functions": project_functions.get(header, []),
                "macros": project_macros.get(header, [])
            }
        
        return combined_result
    
    except Exception as e:
        logger.error(f"Error extracting project functions and macros: {str(e)}")
        return {}
    
def extract_cbmc_flags_for_function(func_name):
    """Extract CBMC flags from Makefiles for the given function."""
    # Default flags from Makefile.common
    flags = [
        "--memory-leak-check",
        "--bounds-check",
        "--conversion-check",
        "--div-by-zero-check",
        "--float-overflow-check",
        "--nan-check",
        "--pointer-overflow-check",
        "--undefined-shift-check",
        "--unsigned-overflow-check",
        "--unwinding-assertions",
    ]
    
    # Look for function-specific flags
    function_proof_dir = None
    
    # Parse original function name if needed
    original_func_name = func_name
    if ":" in func_name:
        _, original_func_name = func_name.split(":", 1)
    
    # Try to find specific proof directory for this function
    proof_root = os.environ.get("PROOF_ROOT", "test/cbmc/proofs")
    if os.path.exists(proof_root):
        for dir_name in os.listdir(proof_root):
            if dir_name.lower() == func_name.lower() or dir_name.lower() == original_func_name.lower():
                function_proof_dir = dir_name
                break
    
    if function_proof_dir:
        makefile_path = os.path.join(proof_root, function_proof_dir, "Makefile")
        if os.path.exists(makefile_path):
            with open(makefile_path, 'r') as f:
                makefile_content = f.read()
                
                # Extract UNWINDSET
                unwind_matches = re.findall(r'UNWINDSET\s*\+=\s*([^=\n]+)', makefile_content)
                if unwind_matches:
                    for match in unwind_matches:
                        unwind_parts = match.strip().split(':')
                        if len(unwind_parts) == 2:
                            flags.append(f"--unwind {unwind_parts[1].strip()}")
                
                # Extract other CBMC flags
                cbmc_flag_matches = re.findall(r'CBMC_FLAG_(\w+)\s*=\s*([^\n]+)', makefile_content)
                for flag_name, flag_value in cbmc_flag_matches:
                    flag_value = flag_value.strip()
                    if flag_value and not flag_value.startswith('#'):
                        flags.append(flag_value)
    
    return "\n".join(flags)

# Add to generator.py - Improved memory leak handling
def generator_node(state):
    """Generates or refines CBMC-compatible harness for the current function using unified RAG."""
    # Get the global LLM instance
    from utils.llm_utils import setup_llm
    llm = setup_llm()

    # Start timing
    generation_start = time.time()
    
    func_name = state.get("current_function", "")
    logger.info(f"Generating harness for function: {func_name}")
    
    # Get result directories from state
    result_directories = state.get("result_directories", {})
    harnesses_dir = result_directories.get("harnesses_dir", "harnesses")
    
    # Get the unified RAG database
    rag_db = get_unified_db(os.path.join(result_directories.get("result_base_dir", "results"), "rag_data"))
    
    # Check if this is a refinement
    improvement_recommendation = state.get("improvement_recommendation", "")
    is_refinement = bool(improvement_recommendation)
    
    # Track harness history - defensive initialization
    harness_history = state.get("harness_history", {}).copy()  # Ensure we have a copy
    if func_name not in harness_history:
        harness_history[func_name] = []
    elif not isinstance(harness_history[func_name], list):
        # Fix any corrupted state - ensure it's always a list
        logger.warning(f"Harness history for {func_name} was not a list. Reinitializing.")
        harness_history[func_name] = []
    
    # Get previous harness if refining
    previous_harness = ""
    cbmc_result = {}
    if is_refinement and func_name in state.get("harnesses", {}):
        previous_harness = state.get("harnesses", {})[func_name]
        # Add to history if not already there
        if previous_harness not in harness_history[func_name]:
            harness_history[func_name].append(previous_harness)
        # Get the CBMC results for analysis
        cbmc_result = state.get("cbmc_results", {}).get(func_name, {})
    
    # Check if we should do a radical harness transformation due to persistent errors
    reset_approach = False
    persistent_errors = state.get("persistent_errors", {}).get(func_name, {})
    highest_persistence = 0
    most_persistent_error = ""
    
    for error_type, count in persistent_errors.items():
        if count > highest_persistence:
            highest_persistence = count
            most_persistent_error = error_type
    
    # If errors are extremely persistent (4+ versions), take drastic action
    if highest_persistence >= 4:
        logger.warning(f"TAKING DRASTIC ACTION: Errors persisted for {highest_persistence} versions for {func_name}")
        logger.warning(f"Most persistent error type: {most_persistent_error}") 
        reset_approach = True
        
        # Check if we're seeing the same error in consecutive versions - remove from RAG if so
        refinement_attempts = state.get("refinement_attempts", {}).get(func_name, 0)
        if refinement_attempts > 1:
            prev_version = refinement_attempts - 1
            current_version = refinement_attempts
            
            # Compare error categories and failure counts between versions
            if cbmc_result.get("error_categories") and cbmc_result.get("previous_error_categories"):
                current_errors = set(cbmc_result.get("error_categories", []))
                previous_errors = set(cbmc_result.get("previous_error_categories", []))
                
                current_failure_count = cbmc_result.get("failure_count", 0)
                previous_failure_count = cbmc_result.get("previous_failure_count", 0)
                
                # Log the actual failure counts for debugging
                logger.info(f"Previous failure count for {func_name}: {previous_failure_count}")
                logger.info(f"Current failure count for {func_name}: {current_failure_count}")
                
                # If same errors persist and failure count didn't decrease, remove the previous solution from RAG
                if current_errors == previous_errors and current_errors and current_failure_count >= previous_failure_count and current_failure_count > 0:
                    logger.warning(f"Same errors persist for {func_name} after refinement with no decrease in failures. Removing from RAG database.")
                    rag_db.remove_ineffective_solution(func_name, prev_version)
                    
                    # Check for persistent errors in the CBMC result
                    persistent_errors = cbmc_result.get("persistent_errors", {})
                    if persistent_errors:
                        # Find the most persistent error (highest count)
                        longest_persisting_error = max(persistent_errors.values(), default=0)
                        logger.warning(f"Detected persistent errors for {func_name} with most persistent error continuing for {longest_persisting_error} versions")
                        
                        # Store this information in state to influence the system prompt
                        state["has_persistent_errors"] = True
                        state["persistent_error_count"] = longest_persisting_error
    
    # Try to get function from unified database first
    function_data = rag_db.get_code_function(func_name)
    
    if function_data:
        func_code = function_data["code"]
        func_metadata = function_data["metadata"]
        logger.info(f"Found function {func_name} in unified RAG database")
    else:
        # Fall back to direct lookup from code_collection
        function_result = code_collection.get(ids=[func_name], include=["documents", "metadatas"])
        
        if function_result["ids"]:
            func_code = function_result["documents"][0]
            func_metadata = function_result["metadatas"][0]
            logger.info(f"Found function {func_name} via direct ID lookup")
            
            # Store in unified database for future use
            rag_db.add_code_function(func_name, func_code, func_metadata)
        else:
            logger.error(f"Function {func_name} not found in database")
            return {
                "messages": [AIMessage(content=f"Error: Function {func_name} not found in database.")],
                "next": "junction"
            }

    # Extract CBMC flags from Makefiles
    cbmc_flags = extract_cbmc_flags_for_function(func_name)
    
    # Extract original function name
    if ":" in func_name:
        _, original_func_name = func_name.split(":", 1)
    else:
        original_func_name = func_name
    
    # Check previous coverage if this is a refinement
    target_coverage = 85.0  # Target coverage percentage
    current_coverage = cbmc_result.get("func_coverage_pct", 0.0)
    
    # Find implementations for dependencies
    dependency_implementations = {}
    
    # Extract function calls or dependencies
    function_calls = func_metadata.get("function_calls", [])
    if isinstance(function_calls, str):
        try:
            function_calls = json.loads(function_calls)
        except json.JSONDecodeError:
            # Fallback to splitting if JSON parsing fails
            function_calls = [call.strip() for call in function_calls.split(',')]
    
    # Find implementations for dependencies
    for called_func in function_calls:
        # Skip control flow functions, standard library functions are allowed now
        if called_func in ["if", "for", "while", "switch", "return"]:
            continue
        
        # Try to find the dependency in the unified database first
        function_data = rag_db.get_code_function(called_func)
        if function_data:
            dependency_implementations[called_func] = {
                "code": function_data["code"],
                "metadata": function_data["metadata"]
            }
            logger.info(f"Found dependency {called_func} in unified RAG database")
            continue
        
        # Fallback search in code collection
        dep_result = code_collection.get(ids=[called_func], include=["documents", "metadatas"])
        if dep_result["ids"]:
            dependency_implementations[called_func] = {
                "code": dep_result["documents"][0],
                "metadata": dep_result["metadatas"][0]
            }
            logger.info(f"Found dependency {called_func} via direct lookup")
    
    # Extract all project functions and macros from headers
    project_data = extract_project_functions(rag_db)
    
    # Collect available header files from the project
    available_headers = list(project_data.keys())
    logger.info(f"Found {len(available_headers)} available headers")
    
    # Count total functions and macros
    total_functions = sum(len(data.get("functions", [])) for data in project_data.values())
    total_macros = sum(len(data.get("macros", [])) for data in project_data.values())
    logger.info(f"Found {total_functions} function declarations and {total_macros} macro definitions")
    
    # Create a detailed project function library description for the LLM
    function_library = ""
    macro_library = ""
    
    for header_name, data in project_data.items():
        functions = data.get("functions", [])
        macros = data.get("macros", [])
        
        # Add functions section
        if functions:
            function_library += f"\n// Header: {header_name} - Functions\n"
            for func in functions:
                function_library += f"{func['declaration']}\n"
        
        # Add macros section
        if macros:
            macro_library += f"\n// Header: {header_name} - Macros\n"
            for macro in macros:
                if macro.get('params'):
                    macro_library += f"#define {macro['name']}({macro['params']}) {macro['value']}\n"
                else:
                    macro_library += f"#define {macro['name']} {macro['value']}\n"
    
    # RAG Enhancement: Get recommendations from unified database for similar errors/solutions
    rag_recommendations = None
    
    if is_refinement and cbmc_result:
        logger.info(f"Querying unified RAG database for function {func_name}")
        
        # Get recommendations from unified database
        rag_recommendations = rag_db.get_recommendations(
            func_name, 
            func_code, 
            cbmc_result,
            previous_harness
        )
        
        # Log RAG findings
        if rag_recommendations:
            if rag_recommendations.get("has_similar_errors", False):
                logger.info(f"Found {len(rag_recommendations.get('similar_errors', []))} similar errors in RAG database")
            if rag_recommendations.get("has_solutions", False):
                logger.info(f"Found {len(rag_recommendations.get('solutions', []))} potential solutions in RAG database")
            if rag_recommendations.get("has_matching_patterns", False):
                logger.info(f"Found {len(rag_recommendations.get('matching_patterns', {}))} matching patterns in RAG database")
    
    # Check if errors are persistent across multiple refinements, to determine if standard library should be allowed
    allow_stdlib = False
    persistent_errors = False
    if is_refinement and cbmc_result:
        refinement_attempts = state.get("refinement_attempts", {}).get(func_name, 0)
        if refinement_attempts >= 2:  # At least 2 previous attempts
            # Check if same errors persist
            error_categories = cbmc_result.get("error_categories", [])
            previous_error_categories = cbmc_result.get("previous_error_categories", [])
            if set(error_categories) == set(previous_error_categories) and error_categories:
                persistent_errors = True
                allow_stdlib = True
                logger.warning(f"Persistent errors detected for {func_name}. Allowing standard library as fallback.")
    
    # Build generator prompt with comprehensive project-specific context
    if not is_refinement:
        # For initial generation, create a minimal harness focusing on function declaration and dependencies
        generator_prompt = f"""
        You are a specialized harness generator for CBMC verification.
        Create a MINIMAL verification harness for testing the function:

        Function Signature:
        ```c
        {func_metadata.get('return_type', 'void')} {original_func_name}({func_metadata.get('params', 'void')});
        ```

        Function Code:
        ```c
        {func_code}
        ```

        CRITICAL INSTRUCTIONS:
        1. DO NOT include the full function implementation
        2. Always use the EXACT parameter names from the original function
        3. ALWAYS use "extern" keyword for function declarations to avoid redefinition conflicts
        4. NEVER redefine the function being tested
        5. NEVER redefine any struct, even if you define it exactly the same as the header
        6. Create a main() function that calls the target function
        7. Use __CPROVER_assume() for input constraints
        8. Use nondet_* functions (like nondet_int(), nondet_char()) for nondeterministic inputs
        9. You are ENCOURAGED to use both project-specific resources AND standard library headers/functions
        10. Standard library usage is fully allowed and encouraged where appropriate
        11. Ensure all declarations are complete and syntactically correct
        12. ALWAYS FREE ALL ALLOCATED MEMORY - Any malloc() must have a corresponding free()
        13. DO NOT CREATE STUBS for existing function dependencies
        14. Properly use project macros that are provided in the PROJECT MACRO LIBRARY section
        15. Your goal is to achieve coverage of at least {target_coverage}% for the target function
        16. IMPORTANT: If you can't find certain constants (like SHADOW_THINGNAME_MAX_LENGTH), create mock values:
            /* BEGIN MOCK CONSTANTS */
            #define MISSING_CONSTANT 128  // Mock value for missing constant
            /* END MOCK CONSTANTS */
        17. STRUCT HANDLING - IMPORTANT:
            - NEVER redefine structs from headers
            - NEVER declare anonymous structs
            - Just use the structs directly from their headers

        CBMC Verification Flags that will be used:
        {cbmc_flags}
        
        Available Project Headers (FEEL FREE TO USE THESE ALONG WITH STANDARD LIBRARY HEADERS):
        """
        
        # Add available headers
        if available_headers:
            for header in available_headers:
                generator_prompt += f"#include \"{header}\"\n"
        else:
            generator_prompt += "// No project headers found, use CBMC built-in functions only\n"
        
        # Add the project function library
        generator_prompt += "\n\n// PROJECT FUNCTION LIBRARY - PRIORITIZE THESE OVER STANDARD LIBRARY FUNCTIONS\n"
        generator_prompt += function_library
        
        # Add the project macro library
        generator_prompt += "\n\n// PROJECT MACRO LIBRARY - USE THESE MACROS IN YOUR HARNESS\n"
        generator_prompt += macro_library
        
        # Add dependency declarations
        if dependency_implementations:
            generator_prompt += "\n// Function Dependencies to Declare\n"
            for dep_name, dep_info in dependency_implementations.items():
                # Extract function signature from metadata or existing implementations
                return_type = dep_info.get('metadata', {}).get('return_type', 'void')
                params = dep_info.get('metadata', {}).get('params', 'void')
                # Use extern and PRESERVE EXACT parameter names
                generator_prompt += f"extern {return_type} {dep_name}({params});\n"
        
        # Add main function template with explicit memory management
        generator_prompt += f"""
        // CREATE A MAIN FUNCTION THAT USES PROJECT FUNCTIONS AND CBMC BUILTINS
        void main() {{
            // Nondeterministic input preparation using nondet_* functions
            // Example: int x = nondet_int();
            // Use __CPROVER_assume() to constrain inputs
            // Example: __CPROVER_assume(x > 0);
            
            // Use appropriate project functions to prepare inputs if needed
            // Use project macros where appropriate
            
            // MEMORY MANAGEMENT: CRUCIAL FOR VERIFICATION
            // For any dynamic memory allocation:
            // void* ptr = malloc(size);
            // __CPROVER_assume(ptr != NULL);
            // ... use ptr ...
            // free(ptr);  // ALWAYS FREE ALLOCATED MEMORY
            
            // Call the function under test with explicit parameter names
            {func_metadata.get('return_type', 'void')} result = {original_func_name}({
                ', '.join([f'nondet_{p.split()[-1]}()' if p.strip() != 'void' else '' 
                           for p in func_metadata.get('params', 'void').split(',')])
            });
            
            // Add verification assertions as needed
            // Example: __CPROVER_assert(result != NULL, "Result should not be NULL");
            
            // Use appropriate project functions to verify outputs if needed
            
            // MAKE SURE TO FREE ALL ALLOCATED MEMORY BEFORE FUNCTION EXIT
        }}
        """
        
        # Add clear instructions
        generator_prompt += """
        KEY VERIFICATION PRINCIPLES:
        - Feel free to use BOTH project-specific resources AND standard library headers/functions
        - Standard library usage is fully allowed and encouraged where appropriate
        - Place project-specific #includes BEFORE standard library includes
        - Use project-specific macros when relevant to the verification task
        - Use __CPROVER_assume() to set realistic input constraints
        - Add __CPROVER_assert() to check critical properties
        - Minimize the harness complexity
        - Focus on key function behaviors
        - ALWAYS use extern for function declarations
        - NEVER redeclare the function with different parameter names
        - ALWAYS FREE ALL ALLOCATED MEMORY before the function exits
        - NEVER create stubs for existing function dependencies
        """
    
    else:
        # For refinement, focus on specific CBMC verification issues and improving coverage
        
        # Detect specific issues from CBMC results that need focused handling
        has_stderr_errors = cbmc_result.get("has_stderr_errors", False)
        has_redeclaration_error = cbmc_result.get("has_redeclaration_error", False) or "redeclaration" in cbmc_result.get("error_categories", [])
        has_linking_error = "linking_error" in cbmc_result.get("error_categories", [])
        has_missing_file_error = "missing_file" in cbmc_result.get("error_categories", [])
        
        # Extract specific information from STDERR if available
        stderr_info = ""
        if "stderr" in cbmc_result and cbmc_result["stderr"]:
            stderr_lines = cbmc_result["stderr"].split('\n')
            # Only include the first 10 stderr lines to keep prompt focused
            stderr_info = "\nCRITICAL STDERR INFORMATION:\n"
            stderr_info += "\n".join(stderr_lines[:10])
            if len(stderr_lines) > 10:
                stderr_info += f"\n...and {len(stderr_lines) - 10} more lines (truncated)"
        
        # Create focused prompt for refinement with critical STDERR issues highlighted
        generator_prompt = f"""
        You are a specialized harness generator for CBMC verification.
        You need to REFINE a harness based on SPECIFIC CBMC verification failures.
        
        Previous Harness:
        ```c
        {previous_harness}
        ```
        
        CBMC Verification Results:
        {improvement_recommendation}
        
        Function Code:
        ```c
        {func_code}
        ```
        
        Current Coverage: {current_coverage:.2f}%
        Target Coverage: {target_coverage:.2f}%
        """
        
        # Add specialized guidance for critical STDERR issues
        if has_stderr_errors:
            generator_prompt += f"""
            {stderr_info}
            
            🔴 CRITICAL STDERR ERRORS DETECTED! These errors must be fixed first before any other issues.
            """
            
            # Add specialized instructions based on error type
            if has_redeclaration_error:
                generator_prompt += """
                REDECLARATION ERROR INSTRUCTIONS:
                1. REMOVE ALL declarations for symbols already defined in included headers
                2. Add "extern" to ALL function declarations
                3. Check for and remove duplicate declarations
                4. NEVER redeclare types, enums, or structs defined in headers
                5. Fix the redeclaration issues FIRST, before addressing any other errors
                """
                
            if has_linking_error:
                generator_prompt += """
                LINKING ERROR INSTRUCTIONS:
                1. Check for "undefined reference" errors in the STDERR output
                2. Make sure all functions called are either:
                   - Declared with proper "extern" keyword
                   - Fully implemented in the harness if not available elsewhere
                3. Do not call any functions that are not available in the project
                4. If you need a function that doesn't exist, implement a minimal stub version
                """
                
            if has_missing_file_error:
                generator_prompt += """
                MISSING FILE ERROR INSTRUCTIONS:
                1. Check for "cannot open file" errors in the STDERR output
                2. Make sure all #include directives use EXACTLY the filenames provided
                3. Use double quotes for project headers (#include "project_header.h")
                4. Use angle brackets only for standard library headers (#include <stdlib.h>)
                5. Remove any includes for files that don't exist
                """
        
        # Add specialized guidance for timeout and performance issues
        is_timeout = cbmc_result.get("status") == "TIMEOUT" or "timeout" in cbmc_result.get("error_categories", [])
        is_slow = cbmc_result.get("is_slow_verification", False) or "performance_warning" in cbmc_result.get("error_categories", [])
        
        if is_timeout or is_slow:
            verification_time = cbmc_result.get("slow_verification_time", 60.0)  # Default to 60s if not specified
            
            performance_warning = "⏱️ TIMEOUT DETECTED!" if is_timeout else f"⚠️ SLOW VERIFICATION DETECTED ({verification_time:.1f}s)"
            
            generator_prompt += f"""
            {performance_warning} The verification process is too complex or contains unbounded operations.
            
            PERFORMANCE OPTIMIZATION INSTRUCTIONS:
            1. SIGNIFICANTLY SIMPLIFY the harness - it's currently too complex for CBMC to verify efficiently
            2. REMOVE or LIMIT all loops by adding bounds (__CPROVER_assume(i < 3))
            3. REDUCE the number of memory allocations (use stack-based fixed arrays when possible)
            4. REDUCE the size of allocated memory (use smaller buffer sizes)
            5. ADD specific constraints to all inputs to limit state space
            6. Use SMALL CONSTANTS throughout the harness (use values < 10)
            7. REMOVE any unnecessary function calls or complex operations
            
            EXAMPLES OF PERFORMANCE OPTIMIZATIONS:
            - Replace: while(condition) {{ ... }}
              With:    for(int i=0; i<3; i++) {{ ... }}
            
            - Replace: char* buffer = malloc(size);
              With:    char buffer[10]; // Fixed small size
            
            - Add constraints: __CPROVER_assume(value > 0 && value < 10);
            """
        
        generator_prompt += """
        CRITICAL INSTRUCTIONS:
        1. DO NOT include the full function implementation
        2. Always use the EXACT parameter names from the original function
        3. ALWAYS use "extern" keyword for function declarations
        4. NEVER redefine the function being tested
        5. Modify the main() function to address specific CBMC failures
        6. Use __CPROVER_assume() to constrain inputs
        7. Use __CPROVER_assert() to validate key properties
        8. PRIORITIZE PROJECT RESOURCES - use project headers and functions FIRST
        9. You MAY use standard library headers and functions when project resources are insufficient
        10. Use project-specific macros when relevant to the verification task
        11. Make sure to use the EXACT header include names as provided
        12. FOCUS on the verification requirements and achieving 85% coverage
        13. ALWAYS FREE ALL ALLOCATED MEMORY - Any malloc() must have a corresponding free()
        14. Follow any specific memory leak resolution instructions in the verification results
        15. DO NOT CREATE STUBS for existing function dependencies - only add stubs for truly missing functions
        """
        
        # Standard libraries are now allowed, but we still prioritize project-specific resources
        generator_prompt += """
        16. IMPORTANT: You are ENCOURAGED to use standard library functions and headers as needed.
            Standard library usage is fully allowed and encouraged where appropriate.
            When using standard libraries, prefer memory-safe functions and add proper error checking.
            """
        
        generator_prompt += f"""
        CBMC Verification Flags that will be used:
        {cbmc_flags}
        
        Available Project Headers (FEEL FREE TO USE THESE ALONG WITH STANDARD LIBRARY HEADERS):
        """
        
        # Add available headers
        if available_headers:
            for header in available_headers:
                generator_prompt += f"#include \"{header}\"\n"
        else:
            generator_prompt += "// No project headers found, use CBMC built-in functions only\n"
        
        # Add the project function library
        generator_prompt += "\n\n// PROJECT FUNCTION LIBRARY - PRIORITIZE THESE OVER STANDARD LIBRARY FUNCTIONS\n"
        generator_prompt += function_library
        
        # Add the project macro library
        generator_prompt += "\n\n// PROJECT MACRO LIBRARY - USE THESE MACROS IN YOUR HARNESS\n"
        generator_prompt += macro_library
        
        # Add dependency declarations
        if dependency_implementations:
            generator_prompt += "\n// Function Dependencies to Declare\n"
            for dep_name, dep_info in dependency_implementations.items():
                # Extract function signature from metadata or existing implementations
                return_type = dep_info.get('metadata', {}).get('return_type', 'void')
                params = dep_info.get('metadata', {}).get('params', 'void')
                generator_prompt += f"extern {return_type} {dep_name}({params});\n"
        
        # Add memory leak detection
        malloc_calls = re.findall(r'(\w+)\s*=\s*(?:malloc|calloc)\([^;]+\)', previous_harness)
        has_malloc = bool(malloc_calls)
        missing_free = []
        
        for var in malloc_calls:
            if f"free({var})" not in previous_harness:
                missing_free.append(var)
        
        if missing_free:
            generator_prompt += "\n// MEMORY LEAK DETECTION:\n"
            generator_prompt += "// The following allocated variables are not being freed:\n"
            for var in missing_free:
                generator_prompt += f"// - {var} \n"
            generator_prompt += "// These must be explicitly freed before the function exits.\n"
        
        # Add refinement guidance
        generator_prompt += """
        // REFINE THE HARNESS TO ADDRESS THE CBMC VERIFICATION FAILURES
        // Use nondet_* functions for inputs (nondet_int, nondet_char, etc.)
        // Use __CPROVER_assume() for constraints
        // Use __CPROVER_assert() for verification
        // Use project functions for any other functionality
        // Use project macros where appropriate
        
        // MEMORY MANAGEMENT PATTERN:
        // void* ptr = malloc(size);
        // __CPROVER_assume(ptr != NULL);
        // ... use ptr ...
        // free(ptr);  // ALWAYS FREE ALL ALLOCATED MEMORY
        """

        # Check for redeclaration errors and provide specific guidance
        if cbmc_result.get("has_redeclaration_error", False) or "redeclaration" in cbmc_result.get("stderr", "") or "redeclaration" in cbmc_result.get("message", ""):
            redeclared_symbols = cbmc_result.get("redeclared_symbols", [])
            
            generator_prompt += """
            // REDECLARATION ERROR DETECTED
            // This error occurs when a function is declared multiple times without proper linkage.
            """
            
            # Add specific guidance for each redeclared symbol
            if redeclared_symbols:
                generator_prompt += "// SPECIFIC REDECLARATION ERRORS FOUND:\n"
                for symbol in redeclared_symbols:
                    generator_prompt += f"// - Symbol '{symbol}' was redeclared improperly\n"
                    
                generator_prompt += "// For EACH of these symbols, you MUST:\n"
            
            generator_prompt += """
            // To fix these redeclaration issues:
            // 1. REMOVE ALL DECLARATIONS for these symbols that are already defined in headers
            // 2. If you MUST declare them, use 'extern' keyword and EXACT matching signatures
            // 3. NEVER redeclare or redefine any symbol, struct, type, or enum already defined in a header
            // 4. Check for and remove ALL duplicate declarations in your harness
            // 5. For each header you include, DO NOT redeclare ANY symbol from that header
            // 6. If you see "redeclaration with no linkage", use extern or completely remove the declaration
            
            // RESOLUTION STRATEGY:
            // 1. First try REMOVING the declaration completely (preferred solution)
            // 2. Only if removal doesn't work, add 'extern' to declaration
            // 3. If still failing, ensure your include order is correct
            """

        # Add line-specific error information if available
        if "line_specific_errors" in cbmc_result and cbmc_result["line_specific_errors"]["error_lines"]:
            line_specific_errors = cbmc_result["line_specific_errors"]
            
            generator_prompt += """
            // LINE-SPECIFIC ERRORS DETECTED
            // The following specific line errors were found in the previous harness:
            """
            
            # Sort errors by line number
            for line_num in sorted(line_specific_errors["error_lines"].keys()):
                error_msgs = line_specific_errors["error_lines"][line_num]
                error_type = line_specific_errors["error_types"].get(line_num, "unknown")
                fix = line_specific_errors["suggested_fixes"].get(line_num, "")
                
                generator_prompt += f"// Line {line_num} - {error_type.upper()} ERROR:\n"
                generator_prompt += f"// - Error: {'; '.join(error_msgs)}\n"
                generator_prompt += f"// - Fix: {fix}\n"
            
            generator_prompt += """
            // IMPORTANT: Focus first on fixing these specific line errors
            // Apply the suggested fixes exactly as recommended
            """
        
        # Add RAG-based recommendations if available
        if rag_recommendations and (rag_recommendations.get("has_similar_errors", False) or 
                                   rag_recommendations.get("has_solutions", False) or 
                                   rag_recommendations.get("has_matching_patterns", False)):
            generator_prompt += "\n\n// RECOMMENDATIONS FROM KNOWLEDGE BASE:\n"
            
            if rag_recommendations.get("has_similar_errors", False):
                generator_prompt += "// Similar Errors Insights:\n"
                for error in rag_recommendations.get("similar_errors", [])[:2]:
                    generator_prompt += f"// - {error.get('error_message', 'Unspecified error')}\n"
            
            if rag_recommendations.get("has_solutions", False):
                generator_prompt += "// Successful Solution Patterns:\n"
                for solution in rag_recommendations.get("solutions", [])[:2]:
                    generator_prompt += "// Verification strategy hints:\n"
                    # Add specific hints about solution patterns
                    if solution.get('patterns_found', 0) > 0:
                        generator_prompt += "// Consider adding targeted assertions\n"
            
            if rag_recommendations.get("has_matching_patterns", False):
                generator_prompt += "// Matching Vulnerability Patterns:\n"
                for name, pattern in rag_recommendations.get("matching_patterns", {}).items():
                    generator_prompt += f"// - {pattern.get('description', 'Unspecified pattern')}\n"
        
        generator_prompt += """
        VERIFICATION REFINEMENT PRINCIPLES:
        - Feel free to use BOTH project-specific resources AND standard library headers/functions
        - Standard library usage is fully allowed and encouraged where appropriate
        - Place project-specific #includes BEFORE standard library includes
        - Use CBMC built-in nondet_* functions for inputs
        - Use project-specific macros when they help with verification
        - Precisely address the specific CBMC verification failures
        - Use more restrictive input constraints with __CPROVER_assume()
        - Add targeted assertions with __CPROVER_assert()
        - Minimize harness complexity
        - ALWAYS use extern for function declarations
        - NEVER redeclare the function with different parameter names
        - ALWAYS FREE ALL ALLOCATED MEMORY before the function exits
        - DO NOT CREATE STUBS for existing function dependencies - only add stubs for truly missing functions
        """
    
    # Generate the harness
    try:
        logger.info(f"Sending API request to generate harness for {func_name}")
        
        # Check for the LLM model type to handle system prompt correctly
        model_name = str(llm).lower()
        
        # Create appropriate system prompt based on whether it's initial generation or refinement
        if not is_refinement:
            # Initial generation system prompt - more focused on basics
            system_prompt = """
            You are a specialized harness generator for CBMC verification. Generate complete, correct, minimal code.
    
            IMPORTANT RULES:
            1. ALWAYS create a function named 'void main()' as the ONLY entry point
            2. DO NOT create functions named 'harness()', 'test_harness()', or any other entry point
            3. Feel free to use BOTH project-specific resources AND standard library headers/functions
            4. Standard library usage is fully allowed and encouraged where appropriate
            5. When using both project resources and standard libraries, always put project #includes FIRST
            6. CREATE A HARNESS USING BOTH PROJECT RESOURCES AND STANDARD LIBRARIES AS NEEDED
            7. ALWAYS use the EXACT parameter names from the original function
            8. NEVER redefine the function being tested
            9. FUNCTION DECLARATION BEST PRACTICES:
               - Only declare functions that are not already declared in included headers
               - Always use extern keyword for ALL function declarations
               - Check for duplicate declarations in your own code
            10. ALWAYS use nondet_* functions for inputs (nondet_int(), nondet_char(), etc.)
            11. Constrain inputs with __CPROVER_assume() when needed
            12. ONLY INCLUDE HEADERS FROM THE PROVIDED LIST - DO NOT MAKE UP HEADER NAMES
            13. ALWAYS FREE ALL ALLOCATED MEMORY - Every malloc() must have a matching free()
            14. DO NOT CREATE STUBS for existing function dependencies
            15. USE PROJECT MACROS when appropriate for the verification task
            """
        else:
            # Check if we have persistent errors that require more dramatic changes
            has_persistent_errors = state.get("has_persistent_errors", False)
            persistent_error_count = state.get("persistent_error_count", 0)
            
            # Also check for specific persistent error types
            state_persistent_errors = state.get("persistent_errors", {})
            func_persistent_errors = state_persistent_errors.get(func_name, {})
            
            # Extract specific error types
            has_persistent_null_pointer = "null_pointer" in func_persistent_errors
            has_persistent_memory_leak = "memory_leak" in func_persistent_errors
            has_persistent_redeclaration = "redeclaration" in func_persistent_errors
            
            # Get the counts for persistent errors
            null_pointer_count = func_persistent_errors.get("null_pointer", 0)
            memory_leak_count = func_persistent_errors.get("memory_leak", 0)
            redeclaration_count = func_persistent_errors.get("redeclaration", 0)
            
            # Add some extra logging to help debug
            logger.info(f"Persistent error check for {func_name}:")
            logger.info(f"- Has persistent errors: {has_persistent_errors}")
            logger.info(f"- Persistent error count: {persistent_error_count}")
            logger.info(f"- Null pointer errors: {null_pointer_count}")
            logger.info(f"- Memory leak errors: {memory_leak_count}")
            logger.info(f"- Redeclaration errors: {redeclaration_count}")
            
            if reset_approach and highest_persistence >= 3:
                # For extremely persistent errors (4+ versions), provide a pre-built template
                # as a starting point rather than asking the LLM to create from scratch again
                
                # Create a template based on error type
                template_harness = ""
                
                if most_persistent_error == "null_pointer":
                    # Template for null pointer errors
                    template_harness = f"""
                    // RADICAL REDESIGN TEMPLATE - AVOIDING NULL POINTERS
                    
                    #include "defender.h"  // Only include essential headers
                    
                    void main() {{
                        // STATIC DATA ONLY - NO DYNAMIC ALLOCATION
                        char static_buffer[1024] = {{0}};  // Static buffer with known size
                        
                        // Static structures for all parameters
                        DefenderTopic_t static_api = DefenderJsonReportPublish;  // Static value
                        char static_thing_name[256] = "test_thing";  // Static thing name
                        uint16_t static_length = 10;  // Static length
                        
                        // Use pointers to stack-allocated data (GUARANTEED NON-NULL)
                        const char *p_thing_name = static_thing_name;
                        DefenderTopic_t *p_api = &static_api;
                        const char **pp_thing_name = &p_thing_name;
                        uint16_t *p_length = &static_length;
                        
                        // Verify explicitly ALL pointers are valid (redundant but safe)
                        if (p_api == NULL || pp_thing_name == NULL || *pp_thing_name == NULL || p_length == NULL) {{
                            return;  // Exit early if any pointer is NULL (should never happen)
                        }}
                        
                        // Call function with guaranteed valid data
                        DefenderStatus_t result = {original_func_name}(static_buffer, 1024, p_api, pp_thing_name, p_length);
                        
                        // Verify expected result
                        __CPROVER_assert(result == DefenderSuccess || result == DefenderBadParameter, 
                                        "Result should be a valid DefenderStatus_t value");
                    }}
                    """
                elif most_persistent_error == "memory_leak":
                    # Template for memory leak errors
                    template_harness = f"""
                    // RADICAL REDESIGN TEMPLATE - AVOIDING MEMORY LEAKS
                    
                    #include "defender.h"  // Only include essential headers
                    
                    void main() {{
                        // STATIC DATA ONLY - NO DYNAMIC ALLOCATION OR MALLOC/FREE
                        char static_buffer[1024] = {{0}};  // Static buffer with known size
                        
                        // Create all inputs as static data - NO MALLOC
                        const char static_topic[] = "test/topic";
                        
                        // Call the function using only stack variables
                        {original_func_name}(
                            static_buffer,  // Buffer is static array
                            sizeof(static_buffer),  // Buffer size is known
                            // Add other parameters as needed
                        );
                        
                        // NO FREE NEEDED - All memory is stack allocated and automatically freed
                    }}
                    """
                else:
                    # Default template for any persistent error
                    template_harness = f"""
                    // RADICAL REDESIGN TEMPLATE - MINIMAL APPROACH
                    
                    #include "defender.h"  // Only include essential headers
                    
                    void main() {{
                        // Use STATIC data wherever possible
                        char static_buffer[1024] = {{0}};
                        
                        // Create minimal static test data
                        const char static_str[] = "test";
                        uint16_t static_val = 10;
                        
                        // Add clear constraints
                        __CPROVER_assume(static_val > 0 && static_val < 100);
                        
                        // Call function with minimal inputs
                        {original_func_name}(static_buffer, sizeof(static_buffer), /* other params as needed */);
                    }}
                    """
                
                system_prompt = f"""
                You are a specialized harness generator for CBMC verification. Generate complete, correct, minimal code.
                
                🚨 EMERGENCY INTERVENTION: The same errors have persisted for {highest_persistence} VERSIONS!
                ⚠️ ALL PREVIOUS APPROACHES HAVE FAILED REPEATEDLY ⚠️
                
                THE SYSTEM HAS PROVIDED A RADICAL REDESIGN TEMPLATE BELOW. WORK WITH THIS TEMPLATE.
                
                ```c
                {template_harness}
                ```
                
                YOUR TASK:
                1. COMPLETE the template above with proper parameter types and values based on the function signature
                2. DO NOT START FROM SCRATCH - BUILD ON THIS TEMPLATE
                3. FOLLOW THE TEMPLATE'S APPROACH - it's designed to avoid the persistent errors
                4. MAKE ONLY NECESSARY CHANGES to adapt it to the function being tested
                
                ABSOLUTELY REQUIRED:
                1. NO DYNAMIC MEMORY ALLOCATION - Use static arrays only
                2. NO COMPLEX POINTER CHAINS - Use static data with direct pointers
                3. ADD EXPLICIT NULL CHECKS before every pointer dereference
                4. INCLUDE ONLY ESSENTIAL HEADERS - Minimal dependencies
                5. FOLLOW THE EXACT PATTERN in the template - It is designed to avoid the {most_persistent_error} error
                
                Function Signature:
                ```c
                {func_metadata.get('return_type', 'void')} {original_func_name}({func_metadata.get('params', 'void')});
                ```
                
                YOU MUST FOLLOW THIS TEMPLATE - NO EXCEPTIONS!
                """
                
            elif has_persistent_errors and persistent_error_count >= 3:
                # Standard approach for moderately persistent errors
                specific_advice = ""
                
                # Add more specific guidance based on error types
                if has_persistent_null_pointer and null_pointer_count >= 3:
                    specific_advice += f"""
                    NULL POINTER ERROR has persisted for {null_pointer_count} versions!
                    For this specific error:
                    1. DO NOT USE ANY POINTERS in your harness if possible 
                    2. If pointers are necessary, do thorough NULL checks with IF statements
                    3. If using malloc/calloc, use __CPROVER_assume(ptr != NULL) immediately after allocation
                    4. Consider using stack-allocated arrays instead of dynamic memory
                    """
                
                if has_persistent_memory_leak and memory_leak_count >= 3:
                    specific_advice += f"""
                    MEMORY LEAK ERROR has persisted for {memory_leak_count} versions!
                    For this specific error:
                    1. ELIMINATE ALL DYNAMIC MEMORY ALLOCATIONS - use static arrays
                    2. If malloc/calloc is absolutely necessary, use a single free() section at the end of main()
                    3. Put all free() calls together in a single block right before main() exits
                    4. Track every allocation carefully to ensure it's freed
                    """
                
                # Special system prompt for persistent errors - with drastic changes suggested
                system_prompt = f"""
                You are a specialized harness generator for CBMC verification. Generate complete, correct, minimal code.
                
                🚨 CRITICAL SITUATION: Same errors persisting across {persistent_error_count} versions of the harness!
                YOUR TASK: Create a COMPLETELY DIFFERENT approach than previous versions.
                
                {specific_advice}
        
                DRASTIC CHANGES REQUIRED:
                1. AVOID ALL TECHNIQUES from previous versions that failed
                2. Take a MINIMALIST approach - ONLY include what's absolutely necessary
                3. MINIMIZE or ELIMINATE DYNAMIC MEMORY ALLOCATION - use stack variables when possible
                4. If memory allocation is necessary, FREE ALL MEMORY in a single location at the end of main()
                5. REMOVE ALL function declarations except the target function - rely on included headers
                6. Use SIMPLER INPUT VALUES - static arrays or literal values where possible
                7. Add STRICT constraints with __CPROVER_assume() for ALL inputs
                8. ADD EXPLICIT NULL CHECKS before using ANY pointer
                9. If previous versions used malloc(), try using static arrays instead
                10. If previous versions used complex inputs, try using simpler fixed values
                11. If previous versions used multiple headers, try using only the essential ones
                12. FOCUS ON THE MOST BASIC HARNESS POSSIBLE that still tests the function
        
                CORE RULES:
                1. Create a FRESH implementation - DO NOT copy patterns from previous versions
                2. ALWAYS create a function named 'void main()' as the ONLY entry point
                3. ALWAYS use the EXACT parameter names from the original function
                4. NEVER redefine the function being tested
                5. ONLY use headers from the PROVIDED LIST - do not make up header names
                6. Feel free to use BOTH project-specific resources AND standard library headers/functions
                7. USE COMPLETELY DIFFERENT PATTERNS than previous versions
                8. FOCUS ON EXTREMELY BASIC VERIFICATION - just enough to exercise the function's core behavior
                """
            else:
                # Standard refinement system prompt - focused on errors
                system_prompt = """
                You are a specialized harness generator for CBMC verification. Generate complete, correct, minimal code.
        
                IMPORTANT RULES:
                1. ALWAYS create a function named 'void main()' as the ONLY entry point
                2. DO NOT create functions named 'harness()', 'test_harness()', or any other entry point
                3. Feel free to use BOTH project-specific resources AND standard library headers/functions
                4. Standard library usage is fully allowed and encouraged where appropriate
                5. When using both project resources and standard libraries, always put project #includes FIRST
                6. CREATE A HARNESS USING BOTH PROJECT RESOURCES AND STANDARD LIBRARIES AS NEEDED
                7. HANDLING FUNCTION DECLARATIONS - PREVENT REDECLARATION ERRORS:
                   - NEVER redeclare ANY symbol (function, enum, struct, typedef) that's defined in an included header
                   - First try to REMOVE declarations of symbols from included headers
                   - If you absolutely must declare something, use "extern" and match signatures exactly
                   - For redeclaration errors with "no linkage", REMOVE the declaration completely
                8. ALWAYS use the EXACT parameter names from the original function
                9. NEVER redefine the function being tested
                10. FOLLOW PROPER C CODE STRUCTURE:
                   - Project-specific include directives first (if any)
                   - Type definitions next (if needed)
                   - Function declarations next (with extern keyword)
                   - Main function last
                11. FUNCTION DECLARATION BEST PRACTICES:
                   - Only declare functions that are not already declared in included headers
                   - Never redeclare functions already available through headers
                   - If you must declare an already available function, ensure EXACT matching signatures
                   - Always use extern keyword for ALL function declarations
                   - Check for duplicate declarations in your own code
                12. ALWAYS use nondet_* functions for inputs (nondet_int(), nondet_char(), etc.)
                13. Constrain inputs with __CPROVER_assume() when needed
                14. ONLY INCLUDE HEADERS FROM THE PROVIDED LIST - DO NOT MAKE UP HEADER NAMES
                15. ALWAYS FREE ALL ALLOCATED MEMORY - Every malloc() must have a matching free()
                16. DO NOT CREATE STUBS for existing function dependencies - only implement stubs for truly missing functions
                17. USE PROJECT MACROS when appropriate for the verification task
                18. FOCUS ON FIXING THE SPECIFIC FAILURES indicated in the verification results
                """
        
        # Setup messages for the LLM based on the model type
        if "gemini" in model_name:
            # For Gemini, include the system prompt in the human message
            response = llm.invoke([
                HumanMessage(content=f"{system_prompt}\n\n{generator_prompt}")
            ])
        else:
            # For Claude and OpenAI models, use separate system and human messages
            response = llm.invoke([
                SystemMessage(content=system_prompt),
                HumanMessage(content=generator_prompt)
            ])
            
        logger.info(f"Received API response for {func_name}")
        
        # Extract the harness code
        harness_code = response.content
        
        # Remove markdown code block syntax
        # First try to extract code between triple backticks
        code_block_pattern = r'```(?:c|cpp)?\s*([\s\S]*?)```'
        code_blocks = re.findall(code_block_pattern, harness_code, re.MULTILINE)
        
        if code_blocks:
            # Use the largest code block found
            harness_code = max(code_blocks, key=len)
        else:
            # If no code blocks found with triple backticks, remove any triple backticks that might be present
            harness_code = re.sub(r'```(?:c|cpp)?', '', harness_code)
            harness_code = re.sub(r'```', '', harness_code)
        
        # Final cleanup - remove any leftover backtick markers and trim whitespace
        harness_code = harness_code.strip()
        
        # Add version comment for both initial and refinement versions
        # Determine version number for changelog
        refinement_attempts = state.get("refinement_attempts", {}).get(func_name, 0)
        version_num = refinement_attempts + 1
        previous_version = refinement_attempts
            
        # No comment blocks will be added at the start of the harness
        # The harness code will be used as is from the LLM response
        # Just continue with processing the harness code
        
        # Validate harness completeness
        has_main = "void main(" in harness_code or "int main(" in harness_code
        balanced_braces = harness_code.count("{") <= harness_code.count("}")

        if not has_main or not balanced_braces:
            logger.warning(f"Incomplete harness for {func_name}, attempting to fix")
            
            # Fix incomplete harnesses
            if not balanced_braces:
                missing_braces = harness_code.count("{") - harness_code.count("}")
                if missing_braces > 0:
                    harness_code += "\n" + ("}" * missing_braces)
            
            # Make sure there's a main function
            if not has_main:
                harness_code += "\n\nvoid main() {\n    // Auto-generated main function\n}"
        
        # Remove any comments restricting standard library usage as standard libraries are now fully allowed
        # If needed, add a comment indicating standard libraries are fully allowed
        std_lib_pattern = r'(#include\s+<[^>]+>)'
        harness_code = re.sub(std_lib_pattern, r'\1  // Standard library', harness_code)
        
        # Ensure all project headers start with double quotes (not angle brackets)
        for header in available_headers:
            if f"#include <{header}>" in harness_code:
                harness_code = harness_code.replace(f"#include <{header}>", f'#include "{header}"')                    

        # Save the new harness to history - ensure func_name exists in harness_history
        if func_name not in harness_history:
            harness_history[func_name] = []
            
        if harness_code not in harness_history[func_name]:
            harness_history[func_name].append(harness_code)
        
        # Update the harnesses dictionary
        harnesses = state.get("harnesses", {}).copy()
        harnesses[func_name] = harness_code
        
        # Determine version number for filename
        refinement_num = state.get("refinement_attempts", {}).get(func_name, 0)
        version_num = refinement_num + 1
        
        # Create function-specific directory in harnesses dir
        func_harness_dir = os.path.join(harnesses_dir, func_name)
        os.makedirs(func_harness_dir, exist_ok=True)
        
        # Save harness to file
        filename = os.path.join(func_harness_dir, f"v{version_num}.c")
        with open(filename, "w") as f:
            f.write(harness_code)
            f.flush()
            os.fsync(f.fileno())  # Force flush to disk
        
        # Calculate time
        generation_time = time.time() - generation_start
        generation_time_ms = int(generation_time * 1000)
        
        # Update function times
        function_times = state.get("function_times", {}).copy()
        if func_name not in function_times:
            function_times[func_name] = {}
        function_times[func_name]["generation"] = generation_time
        
        # Count macro usage in the harness
        macro_usage = 0
        for header_name, data in project_data.items():
            macros = data.get("macros", [])
            for macro in macros:
                macro_name = macro.get("name", "")
                if macro_name and macro_name in harness_code:
                    macro_usage += 1
        
        logger.info(f"Successfully {'refined' if is_refinement else 'generated'} harness for {func_name} in {generation_time:.2f}s with {macro_usage} project macros")
        
        # Create message with RAG information if used
        message_content = f"{'Refined' if is_refinement else 'Generated'} minimal, focused harness for function {func_name} in {generation_time:.2f}s using project-specific functions"
        if macro_usage > 0:
            message_content += f" and {macro_usage} project macros"
        
        if allow_stdlib:
            message_content += " (with standard library fallback allowed due to persistent errors)"
            
        if is_refinement and rag_recommendations:
            # Add info about RAG contributions
            if rag_recommendations.get("has_similar_errors", False):
                message_content += f"\nLeveraged {len(rag_recommendations.get('similar_errors', []))} similar past errors from unified database"
            if rag_recommendations.get("has_solutions", False):
                message_content += f"\nApplied patterns from {len(rag_recommendations.get('solutions', []))} successful solutions"
            if rag_recommendations.get("has_matching_patterns", False):
                message_content += f"\nIdentified {len(rag_recommendations.get('matching_patterns', {}))} relevant vulnerability patterns"
        
        return {
            "messages": [AIMessage(content=message_content)],
            "harnesses": harnesses,
            "harness_history": harness_history,
            "improvement_recommendation": "",
            "function_times": function_times,
            "next": "cbmc"  # Proceed to CBMC verification
        }
        
    except Exception as e:
        # Error handling
        error_msg = str(e)
        error_type = type(e).__name__
        logger.error(f"Error ({error_type}) generating harness for {func_name}: {error_msg}")
        logger.error("Full traceback:", exc_info=True)
        print(f"\nERROR: API call failed when processing function {func_name}")
        print(f"Error type: {error_type}")
        print(f"Error message: {error_msg}")
        
        # Mark this function as failed to prevent repeated attempts
        failed_functions = state.get("failed_functions", [])
        if func_name not in failed_functions:
            failed_functions.append(func_name)
        
        # Get refinement attempt number
        refinement_num = state.get("refinement_attempts", {}).get(func_name, 0)
        version_num = refinement_num + 1
        generation_time_ms = int((time.time() - generation_start) * 1000)
        
        # Return to junction to try next function
        return {
            "messages": [AIMessage(content=f"Error generating harness for {func_name}: {error_msg}. Skipping to next function.")],
            "failed_functions": failed_functions,
            "next": "junction"
        }

def route_from_generator(state):
    """Routes from generator to either cbmc or junction."""
    return state.get("next", "cbmc")