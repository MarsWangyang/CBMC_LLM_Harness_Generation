#!/usr/bin/env python3
"""
Main entry point for the CBMC harness generator.
"""
import os
import glob
import argparse
import logging
import sys
from langchain_core.messages import HumanMessage
import polars as pl

# Improved logging setup:
logging.basicConfig(level=logging.INFO, 
                   format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
                   handlers=[logging.FileHandler("cbmc_main.log"), logging.StreamHandler()])
logger = logging.getLogger("main")

# Reduce verbosity of other loggers
logging.getLogger("urllib3").setLevel(logging.WARNING)
logging.getLogger("chromadb").setLevel(logging.WARNING)

# Import local modules
from utils.file_utils import process_directory, calculate_recursion_limit, setup_verification_directories
from utils.llm_utils import setup_llm
from utils.solver_utils import setup_sat_solver

def initialize_rag_system(result_base_dir):
    """
    Initialize the RAG system after all modules are loaded.
    This avoids circular imports by initializing the RAG system
    only after all core modules are already loaded.
    """
    logger.info("Initializing unified RAG system")
    
    # Create the directory for RAG storage
    rag_dir = os.path.join(result_base_dir, "rag_data")
    os.makedirs(rag_dir, exist_ok=True)
    
    try:
        # Import the unified RAG database module
        from utils.rag import get_unified_db
        import core.embedding_db as embedding_db
        
        # Initialize the unified database
        db = get_unified_db(rag_dir)
        logger.info(f"Initialized RAG database at {rag_dir}")
        
        # Update embedding_db to use the unified database
        embedding_db.code_collection = db.code_collection
        embedding_db.pattern_collection = db.pattern_collection
        
        # Update the query function to use the unified database
        def updated_query_pattern_db(query: str):
            return db.query_pattern_db(query)
        
        embedding_db.query_pattern_db = updated_query_pattern_db
        
        # Recognize global error patterns from previous runs
        global_error_patterns = db.recognize_global_error_patterns()
        
        # Log global error patterns with detailed insights
        if global_error_patterns:
            logger.info("Global Error Pattern Analysis:")
            for pattern in global_error_patterns:
                logger.info(f"Category: {pattern['category']}")
                logger.info(f"  Total Occurrences: {pattern['total_occurrences']}")
                logger.info(f"  Challenge Ratio: {pattern['challenge_ratio']:.2%}")
                logger.info(f"  Recommended Strategy: {pattern['recommended_strategy']}")
                
                if pattern.get('mitigation_suggestions'):
                    logger.info("  Mitigation Suggestions:")
                    for suggestion in pattern['mitigation_suggestions']:
                        logger.info(f"    - {suggestion}")
        
        logger.info("Successfully connected embedding_db to unified RAG database")
        
        return {
            "db": db,
            "global_error_patterns": global_error_patterns
        }
    except Exception as e:
        logger.error(f"Error initializing RAG system: {str(e)}")
        logger.warning("Continuing with default embedding_db implementation")
        return {
            "db": None,
            "global_error_patterns": None
        }

def main():
    """
    Main function for the CBMC harness generator.
    Parses command line arguments and runs the workflow.
    """
    # Set the TOKENIZERS_PARALLELISM environment variable
    os.environ["TOKENIZERS_PARALLELISM"] = "false"
    
    # Set up command line argument parser
    parser = argparse.ArgumentParser(description='CBMC Harness Generator')
    parser.add_argument('-d', '--directory', type=str, help='Directory containing C source files to analyze')
    parser.add_argument('-f', '--file', type=str, help='Single C source file to analyze')
    parser.add_argument('-l', '--llm', type=str, choices=['claude', 'openai', 'gemini'], default='claude',
                        help='LLM to use for code analysis and harness generation (default: claude)')
    parser.add_argument('-t', '--timeout', type=int, default=3600,
                        help='Timeout in seconds for the entire workflow (default: 3600)')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Enable verbose logging')
    parser.add_argument('-e', '--export', type=str, default='metrics.xlsx',
                        help='Export metrics to specified Excel file (default: metrics.xlsx)')
    parser.add_argument('--no-rag', action='store_true',
                        help='Disable the RAG system and use standard embedding database')
    parser.add_argument('-s', '--sat_solver', type=str, choices=['minisat', 'kissat', 'cadical'], default = 'minisat',
                        help='SAT solver used by CBMC' )
    args = parser.parse_args()


    # Set logging level based on verbose flag
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
        logger.debug("Verbose logging enabled")
    
    try:
        # Initialize the global LLM based on user choice
        logger.info(f"Initializing LLM: {args.llm}")
        setup_llm(model_choice=args.llm)

        logger.info(f"Initilizing SAT solver: {args.sat_solver}")
        setup_sat_solver(args.sat_solver)
        
        # Set up verification directories with LLM model name
        directories = setup_verification_directories(llm_used=args.llm)
        
        # Initialize the RAG system if not disabled
        rag_result = {"db": None, "global_error_patterns": None}
        if not args.no_rag:
            rag_result = initialize_rag_system(directories["result_base"])
        
        # Add directories to state for access by nodes
        result_directories = {
            "harnesses_dir": directories["harnesses"],
            "verification_dir": directories["verification"],
            "reports_dir": directories["reports"],
            "result_base_dir": directories["result_base"]
        }
        
        # Only import workflow after initializing the RAG system
        # This prevents circular imports
        from core.workflow import create_workflow
        
        # Set up workflow
        app = create_workflow()
        
        if args.directory:
            # Directory mode
            logger.info(f"Processing directory: {args.directory}")
            initial_message = HumanMessage(content=f"""
            I need to analyze all C source files in the directory: {args.directory}
            Please identify any potential memory leaks and generate CBMC harnesses for verification.
            """)
            
            # Count C source files in the directory for estimation
            source_files_count = 0
            source_subdir = os.path.join(args.directory, "source")
            if not os.path.isdir(source_subdir):
                source_subdir = args.directory
                
            for pattern in ['*.c', '*.cpp']:
                source_files_count += len(glob.glob(os.path.join(source_subdir, "**", pattern), recursive=True))
            
            logger.info(f"Found {source_files_count} source files in {source_subdir}")
            
            # Calculate recursion limit based on file count
            recursion_limit = calculate_recursion_limit(source_files_count)
            
            # Prepare initial state with potential global error patterns
            initial_state = {
                "messages": [initial_message],
                "source_code": "",
                "embeddings": {},
                "vulnerable_functions": [],
                "harnesses": {},
                "cbmc_results": {},
                "processed_functions": [],
                "result_directories": result_directories,
                "llm_used": args.llm,
                "rag_enabled": bool(rag_result["db"]),
                "sat_solver": args.sat_solver,
                "global_error_patterns": rag_result.get("global_error_patterns", [])
            }
            
            # Run workflow with calculated limit and timeout
            try:
                logger.info(f"Starting workflow with recursion limit {recursion_limit} and timeout {args.timeout}s")
                result = app.invoke(
                    initial_state,
                    {"recursion_limit": recursion_limit, "timeout": args.timeout}
                )
                logger.info("Workflow completed successfully")
            except TimeoutError:
                logger.error(f"Workflow timed out after {args.timeout} seconds")
                print(f"ERROR: Workflow timed out after {args.timeout} seconds. Try increasing the timeout with --timeout option.")
                return 1
            except Exception as e:
                logger.error(f"Error during workflow execution: {str(e)}", exc_info=True)
                print(f"ERROR: Workflow failed: {str(e)}")
                return 1
        
        # [Rest of the main() function remains the same as in the original implementation]
        # ... (including the file mode processing, metrics export, etc.)
        
    except Exception as e:
        logger.critical(f"Critical error: {str(e)}", exc_info=True)
        print(f"A critical error occurred: {str(e)}")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())