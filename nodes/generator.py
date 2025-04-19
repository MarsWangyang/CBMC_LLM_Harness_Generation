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
    
    # Track harness history
    harness_history = state.get("harness_history", {})
    if func_name not in harness_history:
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
    
    # Extract original function name
    if ":" in func_name:
        _, original_func_name = func_name.split(":", 1)
    else:
        original_func_name = func_name
    
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
        # Skip standard library and control flow functions
        if called_func in ["if", "for", "while", "switch", "return", "malloc", "free",
                          "memset", "memcpy", "printf", "fprintf", "sprintf"]:
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
            if rag_recommendations["has_similar_errors"]:
                logger.info(f"Found {len(rag_recommendations['similar_errors'])} similar errors in RAG database")
            if rag_recommendations["has_solutions"]:
                logger.info(f"Found {len(rag_recommendations['solutions'])} potential solutions in RAG database")
            if rag_recommendations["has_matching_patterns"]:
                logger.info(f"Found {len(rag_recommendations['matching_patterns'])} matching patterns in RAG database")
    
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
        5. Create a main() function that calls the target function
        6. Use __CPROVER_assume() for input constraints
        7. Use nondet_* functions (like nondet_int(), nondet_char()) for nondeterministic inputs
        8. AVOID STANDARD LIBRARY HEADERS AND FUNCTIONS - only use project-specific headers and functions
        9. ONLY use one or more of the available project headers from the list below
        10. Ensure all declarations are complete and syntactically correct
        11. FOCUS on creating a verifiable function call scenario using only project resources
        12. ALWAYS FREE ALL ALLOCATED MEMORY - Any malloc() must have a corresponding free()
        13. DO NOT CREATE STUBS for existing function dependencies
        14. Properly use project macros that are provided in the PROJECT MACRO LIBRARY section

        15. Make a null check before dereferncing any pointer
        16: Chceck for bounds before accessing a location out of bounds
        

        Available Project Headers (USE ONLY THESE, DO NOT USE STANDARD LIBRARY HEADERS):
        """
        
        # Add available headers
        if available_headers:
            for header in available_headers:
                generator_prompt += f"#include \"{header}\"\n"
        else:
            generator_prompt += "// No project headers found, use CBMC built-in functions only\n"
        
        # Add the project function library
        generator_prompt += "\n\n// PROJECT FUNCTION LIBRARY - USE THESE FUNCTIONS INSTEAD OF STANDARD LIBRARY\n"
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
        - DO NOT use any standard library functions (printf, malloc, free, etc.) or headers (stdio.h, stdlib.h, etc.)
        - Only use one or more of the project-specific headers provided above
        - Only use project-specific functions and CBMC built-in nondet_* functions
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
        # For refinement, focus on specific CBMC verification issues
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
        
        CRITICAL INSTRUCTIONS:
        1. DO NOT include the full function implementation
        2. Always use the EXACT parameter names from the original function
        3. ALWAYS use "extern" keyword for function declarations
        4. NEVER redefine the function being tested
        5. Modify the main() function to address specific CBMC failures
        6. Use __CPROVER_assume() to constrain inputs
        7. Use __CPROVER_assert() to validate key properties
        8. AVOID ALL STANDARD LIBRARY HEADERS AND FUNCTIONS
        9. ONLY use one or more of the available project headers from the list below
        10. Only use project-specific functions from the provided library and CBMC built-ins
        11. Use project-specific macros when relevant to the verification task
        12. Make sure to use the EXACT header include names as provided
        13. FOCUS on the verification requirements
        14. ALWAYS FREE ALL ALLOCATED MEMORY - Any malloc() must have a corresponding free()
        15. Follow any specific memory leak resolution instructions in the verification results
        16. DO NOT CREATE STUBS for existing function dependencies - only add stubs for truly missing functions

        Available Project Headers (USE ONLY THESE, DO NOT USE STANDARD LIBRARY HEADERS):
        """
        
        # Add available headers
        if available_headers:
            for header in available_headers:
                generator_prompt += f"#include \"{header}\"\n"
        else:
            generator_prompt += "// No project headers found, use CBMC built-in functions only\n"
        
        # Add the project function library
        generator_prompt += "\n\n// PROJECT FUNCTION LIBRARY - USE THESE FUNCTIONS INSTEAD OF STANDARD LIBRARY\n"
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
        
        # Add RAG-based recommendations if available
        if rag_recommendations and (rag_recommendations["has_similar_errors"] or 
                                   rag_recommendations["has_solutions"] or 
                                   rag_recommendations["has_matching_patterns"]):
            generator_prompt += "\n\n// RECOMMENDATIONS FROM KNOWLEDGE BASE:\n"
            
            if rag_recommendations["has_similar_errors"]:
                generator_prompt += "// Similar Errors Insights:\n"
                for error in rag_recommendations["similar_errors"][:2]:
                    generator_prompt += f"// - {error.get('error_message', 'Unspecified error')}\n"
            
            if rag_recommendations["has_solutions"]:
                generator_prompt += "// Successful Solution Patterns:\n"
                for solution in rag_recommendations["solutions"][:2]:
                    generator_prompt += "// Verification strategy hints:\n"
                    # Add specific hints about solution patterns
                    if solution.get('patterns_found', 0) > 0:
                        generator_prompt += "// Consider adding targeted assertions\n"
            
            if rag_recommendations["has_matching_patterns"]:
                generator_prompt += "// Matching Vulnerability Patterns:\n"
                for name, pattern in rag_recommendations["matching_patterns"].items():
                    generator_prompt += f"// - {pattern.get('description', 'Unspecified pattern')}\n"
        
        generator_prompt += """
        VERIFICATION REFINEMENT PRINCIPLES:
        - DO NOT use any standard library headers or functions
        - Only use project-specific headers and functions listed above
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
        
        # Enhanced system prompt to strongly enforce project-specific functions and memory management
        system_prompt = """
        You are a specialized harness generator for CBMC verification. Generate complete, correct, minimal code.

        IMPORTANT RULES:
        1. ALWAYS create a function named 'void main()' as the ONLY entry point
        2. DO NOT create functions named 'harness()', 'test_harness()', or any other entry point
        3. NEVER use standard library headers (stdio.h, stdlib.h, string.h, etc.)
        4. NEVER use standard library functions (printf, malloc, free, etc.)
        5. ONLY use project-specific functions that were provided AND CBMC built-in functions
        6. ONLY include project-specific headers that were explicitly provided
        7. CREATE A HARNESS USING ONLY PROJECT RESOURCES AND CBMC BUILT-INS
        8. ALWAYS use "extern" for function declarations to avoid redefinition conflicts
        9. ALWAYS use the EXACT parameter names from the original function
        10. NEVER redefine the function being tested
        11. FOLLOW PROPER C CODE STRUCTURE:
           - Project-specific include directives first (if any)
           - Type definitions next (if needed)
           - Function declarations next
           - Main function last
        12. ALWAYS use nondet_* functions for inputs (nondet_int(), nondet_char(), etc.)
        13. Constrain inputs with __CPROVER_assume() when needed
        14. ONLY INCLUDE HEADERS FROM THE PROVIDED LIST - DO NOT MAKE UP HEADER NAMES
        15. ALWAYS FREE ALL ALLOCATED MEMORY - Every malloc() must have a matching free()
        16. DO NOT CREATE STUBS for existing function dependencies - only implement stubs for truly missing functions
        17. USE PROJECT MACROS when appropriate for the verification task
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
        match = re.search(r'```(?:c)?\n(.+?)\n```', harness_code, re.DOTALL)
        if match:
            harness_code = match.group(1)
        
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
        
        # Check for standard library includes and remove them
        harness_code = re.sub(r'#include\s+<[^>]+>', '// REMOVED STANDARD LIBRARY INCLUDE', harness_code)
        
        # Ensure all project headers start with double quotes (not angle brackets)
        for header in available_headers:
            if f"#include <{header}>" in harness_code:
                harness_code = harness_code.replace(f"#include <{header}>", f'#include "{header}"')
        
        # ENHANCEMENT: Check for memory leaks by finding malloc calls without corresponding free
        malloc_vars = re.findall(r'(\w+)\s*=\s*(?:malloc|calloc)\([^;]+\)', harness_code)
        missing_free = []
        
        for var in malloc_vars:
            if f"free({var})" not in harness_code:
                missing_free.append(var)
        
        if missing_free:
            logger.warning(f"Found {len(missing_free)} allocated variables without free in harness")
            
            # Add free operations before the end of main function
            main_end_match = re.search(r'}(\s*)$', harness_code)
            if main_end_match:
                # Insert free operations before the closing brace of main
                free_block = "\n    // Free allocated memory to prevent leaks\n"
                for var in missing_free:
                    free_block += f"    free({var});\n"
                
                # Replace the closing brace with our free block plus closing brace
                harness_code = harness_code[:main_end_match.start()] + free_block + "}" + harness_code[main_end_match.end():]
                logger.info(f"Added free operations for {len(missing_free)} variables to prevent memory leaks")
        
        # Save the new harness to history
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
            
        if is_refinement and rag_recommendations:
            # Add info about RAG contributions
            if rag_recommendations["has_similar_errors"]:
                message_content += f"\nLeveraged {len(rag_recommendations['similar_errors'])} similar past errors from unified database"
            if rag_recommendations["has_solutions"]:
                message_content += f"\nApplied patterns from {len(rag_recommendations['solutions'])} successful solutions"
            if rag_recommendations["has_matching_patterns"]:
                message_content += f"\nIdentified {len(rag_recommendations['matching_patterns'])} relevant vulnerability patterns"
        
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