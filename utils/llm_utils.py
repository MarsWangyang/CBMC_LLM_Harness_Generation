"""
LLM setup and utilities for the CBMC harness generator.
"""
import os
import sys
from langchain_anthropic import ChatAnthropic
from langchain_openai import ChatOpenAI
import logging

# For Gemini support
try:
    from langchain_google_genai import ChatGoogleGenerativeAI
except ImportError:
    pass

# Global LLM instance
_global_llm = None

logger = logging.getLogger("llm_utils")

def setup_llm(model_choice='claude'):
    """Set up the LLM with optimized parameters for harness generation.
    
    Args:
        model_choice: 'claude', 'openai', or 'gemini' to select which LLM to use
    
    Returns:
        A configured LLM instance ready for use
    """
    global _global_llm
    
    # If already initialized, return the existing instance
    if _global_llm is not None:
        logger.debug("Using existing LLM instance")
        return _global_llm
    
    logger.info(f"Initializing new {model_choice} LLM instance")
    
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
    - IMPORTANT: If unable to find constant definitions like SHADOW_THINGNAME_MAX_LENGTH, create mock values with #define
      For example: #define SHADOW_THINGNAME_MAX_LENGTH 128  // Mock value
    - Always include guard comments for mock definitions to make them easy to identify:
      /* BEGIN MOCK CONSTANTS */
      #define MISSING_CONSTANT 10  // Mock value
      /* END MOCK CONSTANTS */
    
    Your code must compile and run correctly with CBMC verification.
    """
    
    try:
        # Determine which model to use based on the choice
        if model_choice.lower() == 'claude':
            anthropic_api_key = os.environ.get("ANTHROPIC_API_KEY")
            if not anthropic_api_key:
                print("ERROR: ANTHROPIC_API_KEY not set. Set this environment variable or use --llm openai or --llm gemini.")
                sys.exit(1)
            
            _global_llm = ChatAnthropic(
                model="claude-3-7-sonnet-latest",
                anthropic_api_key=anthropic_api_key,
                temperature=0.2,  # Lower temperature for more deterministic code generation
                max_tokens=20000,  # Ensure we have enough tokens for complete responses
                model_kwargs={"system": system_prompt},  # Use model_kwargs for the system prompt
            )
        
        elif model_choice.lower() == 'openai':
            openai_api_key = os.environ.get("OPENAI_API_KEY")
            if not openai_api_key:
                print("ERROR: OPENAI_API_KEY not set. Set this environment variable or use --llm claude or --llm gemini.")
                sys.exit(1)
            
            _global_llm = ChatOpenAI(
                model="gpt-4.1",  # Use GPT-4o for best code generation capabilities
                openai_api_key=openai_api_key,
                temperature=0.2,
                max_tokens=20000,
                model_kwargs={"response_format": {"type": "text"}},
            )
        
        elif model_choice.lower() == 'gemini':
            google_api_key = os.environ.get("GOOGLE_API_KEY")
            if not google_api_key:
                print("ERROR: GOOGLE_API_KEY not set. Set this environment variable or use --llm claude or --llm openai.")
                sys.exit(1)
            
            try:
                _global_llm = ChatGoogleGenerativeAI(
                    model="gemini-2.5-pro-exp-03-25",  # Use the latest Gemini 2.5 Pro model
                    google_api_key=google_api_key,
                    temperature=0.2,
                    max_output_tokens=20000,
                    convert_system_message_to_human=True,  # Handle system prompts correctly
                )
                # Add a system message for consistency with other models
                # Since Gemini doesn't support system messages directly, we'll add it in the generation calls
            except NameError:
                print("ERROR: langchain_google_genai package not installed. Install it with 'pip install langchain-google-genai'")
                sys.exit(1)
        
        else:
            raise ValueError(f"Unknown LLM choice: {model_choice}. Use 'claude', 'openai', or 'gemini'.")
        
        return _global_llm
        
    except Exception as e:
        print(f"ERROR: Failed to initialize LLM: {str(e)}")
        sys.exit(1)