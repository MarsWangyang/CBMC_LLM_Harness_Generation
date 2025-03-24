#!/usr/bin/env python3
"""
Main entry point for the CBMC harness generator.
"""
import os
import glob
import argparse
from langchain_core.messages import HumanMessage

from core.workflow import create_workflow
from utils.file_utils import process_directory, calculate_recursion_limit, setup_verification_directories

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
    args = parser.parse_args()
    
    # Set up workflow
    app = create_workflow()
    
    # Set up verification directories
    setup_verification_directories()
    
    if args.directory:
        # Directory mode
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
        
        # Calculate recursion limit based on file count
        recursion_limit = calculate_recursion_limit(source_files_count)
        
        # Run workflow with calculated limit
        result = app.invoke(
            {
                "messages": [initial_message],
                "source_code": "",
                "embeddings": {},
                "vulnerable_functions": [],
                "harnesses": {},
                "cbmc_results": {},
                "processed_functions": []
            },
            {"recursion_limit": recursion_limit}
        )
    elif args.file:
        # Single file mode - use a simpler estimation
        try:
            with open(args.file, 'r') as f:
                source_code = f.read()
                
            # For a single file, use a fixed recursion limit or estimate based on file size
            file_size = len(source_code)
            # Rough heuristic: 1 function per 100 lines, ~50 chars per line
            estimated_functions = max(5, file_size // 5000)
            recursion_limit = calculate_recursion_limit(estimated_functions // 8 + 1)  # Convert back to file count
                
            initial_message = HumanMessage(content=f"""
            I need to analyze the following C code for memory leaks and generate verification harnesses:

            ```c
            {source_code}
            ```

            Please identify any potential memory leaks and generate CBMC harnesses for verification.
            """)
            
            # Run workflow with calculated limit
            result = app.invoke(
                {
                    "messages": [initial_message],
                    "source_code": source_code,
                    "embeddings": {},
                    "vulnerable_functions": [],
                    "harnesses": {},
                    "cbmc_results": {},
                    "processed_functions": []
                },
                {"recursion_limit": recursion_limit}
            )
        except Exception as e:
            print(f"Error reading file {args.file}: {str(e)}")
            return
    else:
        print("Please provide either a directory (-d) or a file (-f) to analyze")
        return
    
    # Display the conversation
    print("=== Workflow Execution Results ===")
    for i, message in enumerate(result["messages"]):
        if isinstance(message, HumanMessage):
            print(f"\n===== Human Message {i+1} =====")
            print(message.content[:200] + "..." if len(message.content) > 200 else message.content)
        else:  # AIMessage
            print(f"\n===== AI Message {i+1} =====")
            print(message.content)

if __name__ == "__main__":
    main()