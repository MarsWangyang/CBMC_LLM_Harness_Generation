"""
Pattern detection and extraction utilities for the CBMC harness generator.

This module provides functions for detecting and extracting common patterns
in C code, particularly those related to memory management and pointer usage.
"""
import re
from typing import Dict, List, Optional, Set, Tuple

def extract_malloc_free_patterns(code: str) -> List[Tuple[str, str]]:
    """
    Extract malloc/free patterns from code.
    
    Args:
        code: The source code to analyze
        
    Returns:
        List of (variable, pattern) tuples
    """
    # Look for malloc followed by free
    patterns = []
    
    # Pattern 1: Simple malloc and free on same variable
    malloc_vars = re.findall(r'(\w+)\s*=\s*malloc\([^;]+;', code)
    for var in malloc_vars:
        # Check if this variable is freed
        if re.search(rf'free\s*\(\s*{var}\s*\)\s*;', code):
            # Extract the complete pattern
            malloc_match = re.search(rf'{var}\s*=\s*malloc\([^;]+;', code)
            free_match = re.search(rf'free\s*\(\s*{var}\s*\)\s*;', code)
            
            if malloc_match and free_match:
                # Find the code between malloc and free
                start_pos = malloc_match.start()
                end_pos = free_match.end()
                
                # Get the complete pattern
                pattern = code[start_pos:end_pos]
                patterns.append((var, pattern))
    
    return patterns

def extract_null_check_patterns(code: str) -> List[Tuple[str, str]]:
    """
    Extract NULL pointer check patterns from code.
    
    Args:
        code: The source code to analyze
        
    Returns:
        List of (variable, pattern) tuples
    """
    patterns = []
    
    # Pattern 1: if (ptr == NULL) or if (ptr != NULL)
    null_checks = re.finditer(r'if\s*\(\s*(\w+)\s*(==|!=)\s*NULL\s*\)', code)
    
    for match in null_checks:
        var = match.group(1)
        operator = match.group(2)
        
        # Find the complete if block
        start_pos = match.start()
        # Look for opening brace
        open_brace_pos = code.find('{', start_pos)
        if open_brace_pos != -1:
            # Find matching closing brace
            brace_count = 1
            pos = open_brace_pos + 1
            while brace_count > 0 and pos < len(code):
                if code[pos] == '{':
                    brace_count += 1
                elif code[pos] == '}':
                    brace_count -= 1
                pos += 1
            
            if brace_count == 0:
                # Found complete block
                end_pos = pos
                pattern = code[start_pos:end_pos]
                patterns.append((var, pattern))
    
    return patterns

def extract_cprover_patterns(code: str) -> List[str]:
    """
    Extract CPROVER-specific patterns from code.
    
    Args:
        code: The source code to analyze
        
    Returns:
        List of CPROVER patterns
    """
    patterns = []
    
    # Look for __CPROVER_assume statements
    assume_matches = re.finditer(r'__CPROVER_assume\s*\([^;]+;', code)
    for match in assume_matches:
        patterns.append(match.group(0))
    
    # Look for __CPROVER_assert statements
    assert_matches = re.finditer(r'__CPROVER_assert\s*\([^;]+;', code)
    for match in assert_matches:
        patterns.append(match.group(0))
    
    return patterns

def extract_function_signature(func_code: str) -> Optional[Dict[str, str]]:
    """
    Extract the function signature components from function code.
    
    Args:
        func_code: The function code
        
    Returns:
        Dictionary with return_type, name, and params, or None if not found
    """
    signature_match = re.search(r'^([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)', func_code.strip(), re.MULTILINE)
    if signature_match:
        return {
            "return_type": signature_match.group(1).strip(),
            "name": signature_match.group(2).strip(),
            "params": signature_match.group(3).strip()
        }
    return None

def get_function_calls(func_code: str) -> Set[str]:
    """
    Extract function calls from function code.
    
    Args:
        func_code: The function code
        
    Returns:
        Set of function names that are called
    """
    # Basic pattern for function calls
    calls = re.findall(r'\b(\w+)\s*\([^;]*\)', func_code)
    
    # Filter out common keywords that might match this pattern
    keywords = {"if", "for", "while", "switch", "return", "sizeof"}
    return {call for call in calls if call not in keywords}