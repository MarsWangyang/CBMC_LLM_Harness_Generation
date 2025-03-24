"""
State definitions for the CBMC harness generator workflow.
"""
from typing import Dict, List, Any
from langgraph.graph import MessagesState

class HarnessGenerationState(MessagesState):
    # Original fields
    source_code: str = ""  # For single file compatibility
    embeddings: Dict = {}
    vulnerable_functions: List[str] = []
    harnesses: Dict[str, str] = {}
    cbmc_results: Dict[str, Any] = {}
    refinement_attempts: Dict[str, int] = {}
    current_function: str = ""  # Track the function currently being processed
    processed_functions: List[str] = []  # Track functions that have been processed
    improvement_recommendation: str = ""  # Store recommendations for harness improvement
    loop_counter: int = 0  # Counter to detect and prevent infinite loops
    
    # New field to track harness version history
    harness_history: Dict[str, List[str]] = {}
    
    # Progress tracking
    total_functions: int = 0  # Total number of functions to process
    current_function_index: int = 0  # Index of current function being processed
    
    # Timing information
    start_time: float = 0.0  # Timestamp when process started
    function_times: Dict[str, Dict[str, float]] = {}  # Timing for each function phase
    
    # New fields for multi-file support
    source_files: Dict[str, str] = {}  # Map of file paths to content
    is_directory_mode: bool = False  # Flag to indicate if processing directory
    source_directory: str = ""  # Path to the source directory
    file_functions: Dict[str, List[str]] = {}  # Map of file paths to function names
    
    # Enhanced tracking for CBMC errors and harness issues
    cbmc_error_messages: Dict[str, str] = {}  # Track specific CBMC error messages by function
    harness_syntax_errors: Dict[str, str] = {}  # Track syntax errors in harnesses
    parsing_issues: Dict[str, bool] = {}  # Track which functions had parsing issues
    verification_failures: Dict[str, List[str]] = {}  # Track verification failure types by function