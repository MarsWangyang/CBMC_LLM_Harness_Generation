"""
LLM setup and utilities for the CBMC harness generator.
"""
import os
from langchain_anthropic import ChatAnthropic

def setup_llm():
    """Set up the LLM with optimized parameters for harness generation."""
    
    # Check if ANTHROPIC_API_KEY is set in environment variables
    api_key = os.environ.get("ANTHROPIC_API_KEY")
    
    # Configure system prompt to encourage complete, non-truncated code generation
    system_prompt = """
    You are an expert at generating complete, correct CBMC verification harnesses for C functions.
    
    When generating code:
    - Always provide complete, syntactically valid code
    - Never truncate code with comments like "//..." or "/* ... */"
    - Always include a complete main() function
    - Always ensure balanced braces and complete control structures
    - Keep harnesses simple, focused, and minimal while still testing the function thoroughly
    - Complete all control structures and function bodies
    
    Your code must compile and run correctly with CBMC verification.
    """
    
    # Create the LLM instance with optimized parameters
    llm = ChatAnthropic(
        model="claude-3-7-sonnet-latest",
        anthropic_api_key=api_key,
        temperature=0.2,  # Lower temperature for more deterministic code generation
        max_tokens=4000,  # Ensure we have enough tokens for complete responses
        model_kwargs={"system": system_prompt},  # Use model_kwargs for the system prompt
    )
    
    return llm