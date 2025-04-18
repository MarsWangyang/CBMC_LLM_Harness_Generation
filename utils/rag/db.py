"""
Unified embedding database for the CBMC harness generator.

This module provides a consolidated RAG (Retrieval-Augmented Generation) database
that combines code embeddings, pattern embeddings, harness error embeddings, and
solution embeddings in a single interface.

Usage:
    from utils.rag.db import get_unified_db
    
    # Get the global instance
    db = get_unified_db(persistence_dir="results/rag_data")
    
    # Store and retrieve code functions
    db.add_code_function(func_id, func_code, metadata)
    function = db.get_code_function(func_id)
    
    # Query for similar functions
    similar_functions = db.query_code_function(query_text)
    
    # Query for matching patterns
    pattern_results = db.query_pattern_db(func_code)
    
    # Store errors and solutions
    error_id = db.store_error(func_name, harness_code, cbmc_result, iteration)
    solution_id = db.store_solution(error_id, func_name, harness_code, cbmc_result, iteration)
    
    # Get recommendations for function with errors
    recommendations = db.get_recommendations(func_name, func_code, cbmc_result, harness_code)
"""
import os
import re
import json
import time
import logging
import chromadb
from chromadb.utils import embedding_functions
from typing import Dict, List, Any, Optional, Tuple, Set

# Set up logging
logger = logging.getLogger("rag.db")

class UnifiedEmbeddingDB:
    """
    Unified database for storing and retrieving embeddings for code, patterns, errors, and solutions.
    """
    
    def __init__(self, persistence_dir: str = "rag_data"):
        """
        Initialize the unified embedding database.
        
        Args:
            persistence_dir: Directory to store the persistent database
        """
        self.persistence_dir = persistence_dir
        os.makedirs(persistence_dir, exist_ok=True)
        
        # Set up ChromaDB with persistence
        self.chroma_client = chromadb.PersistentClient(path=persistence_dir)
        self.sentence_transformer_ef = embedding_functions.SentenceTransformerEmbeddingFunction(
            model_name="all-MiniLM-L6-v2"
        )
        
        # Initialize all collections
        self._initialize_collections()
        
        logger.info(f"Initialized UnifiedEmbeddingDB with persistence at {persistence_dir}")

    def mark_ineffective_solution(self, func_name: str, version: int) -> bool:
        """
        Mark a solution as ineffective when the same errors persist across versions.
        
        Args:
            func_name: Name of the function
            version: Version number of the ineffective solution
            
        Returns:
            True if marked successfully, False otherwise
        """
        try:
            # Use proper where filter syntax with $eq operator
            where_filter = {"$and": [
                {"func_name": {"$eq": func_name}}, 
                {"iteration": {"$eq": version}}
            ]}
            
            # Find the solution by func_name and version
            solutions = self.solution_collection.get(
                where=where_filter
            )
            
            if not solutions or not solutions["ids"]:
                logger.warning(f"No solution found for {func_name} version {version} to mark as ineffective")
                return False
            
            solution_id = solutions["ids"][0]
            metadata = solutions["metadatas"][0]
            
            # Update the metadata to mark as ineffective
            metadata["is_effective"] = False
            metadata["ineffective_reason"] = "Same errors persisted after refinement"
            
            # Update the solution in the collection
            self.solution_collection.update(
                ids=[solution_id],
                metadatas=[metadata]
            )
            
            logger.info(f"Marked solution {solution_id} for {func_name} version {version} as ineffective")
            return True
        
        except Exception as e:
            logger.error(f"Error marking solution as ineffective: {str(e)}")
            return False

    def remove_ineffective_solution(self, func_name: str, version: int) -> bool:
        """
        Remove an ineffective solution from the RAG database.
        
        Args:
            func_name: Name of the function
            version: Version number of the ineffective solution
            
        Returns:
            True if removed successfully, False otherwise
        """
        try:
            # Use proper where filter syntax with $eq operator
            where_filter = {"$and": [
                {"func_name": {"$eq": func_name}}, 
                {"iteration": {"$eq": version}}
            ]}
            
            # Find the solution by func_name and version
            solutions = self.solution_collection.get(
                where=where_filter
            )
            
            if not solutions or not solutions["ids"]:
                logger.warning(f"No solution found for {func_name} version {version} to remove")
                return False
            
            solution_id = solutions["ids"][0]
            
            # Remove the solution from the collection
            self.solution_collection.delete(ids=[solution_id])
            
            logger.info(f"Removed ineffective solution {solution_id} for {func_name} version {version} from RAG database")
            return True
        
        except Exception as e:
            logger.error(f"Error removing ineffective solution: {str(e)}")
            return False
    
    def _initialize_collections(self):
        """Initialize all embedding collections."""
        # Create or get code collection
        try:
            self.code_collection = self.chroma_client.get_collection(
                name="code_embeddings",
                embedding_function=self.sentence_transformer_ef
            )
            logger.info(f"Retrieved existing code collection with {self.code_collection.count()} entries")
        except:
            self.code_collection = self.chroma_client.create_collection(
                name="code_embeddings",
                embedding_function=self.sentence_transformer_ef,
                metadata={"hnsw:space": "cosine"}
            )
            logger.info("Created new code collection")
        
        # Create or get pattern collection
        try:
            self.pattern_collection = self.chroma_client.get_collection(
                name="pattern_embeddings",
                embedding_function=self.sentence_transformer_ef
            )
            logger.info(f"Retrieved existing pattern collection with {self.pattern_collection.count()} entries")
        except:
            self.pattern_collection = self.chroma_client.create_collection(
                name="pattern_embeddings",
                embedding_function=self.sentence_transformer_ef,
                metadata={"hnsw:space": "cosine"}
            )
            self._initialize_pattern_collection()
            logger.info("Created new pattern collection with initial patterns")
        
        # Create or get error collection
        try:
            self.error_collection = self.chroma_client.get_collection(
                name="harness_errors",
                embedding_function=self.sentence_transformer_ef
            )
            logger.info(f"Retrieved existing error collection with {self.error_collection.count()} entries")
        except:
            self.error_collection = self.chroma_client.create_collection(
                name="harness_errors",
                embedding_function=self.sentence_transformer_ef,
                metadata={"hnsw:space": "cosine"}
            )
            logger.info("Created new error collection")
        
        # Create or get solution collection
        try:
            self.solution_collection = self.chroma_client.get_collection(
                name="harness_solutions",
                embedding_function=self.sentence_transformer_ef
            )
            logger.info(f"Retrieved existing solution collection with {self.solution_collection.count()} entries")
        except:
            self.solution_collection = self.chroma_client.create_collection(
                name="harness_solutions",
                embedding_function=self.sentence_transformer_ef,
                metadata={"hnsw:space": "cosine"}
            )
            logger.info("Created new solution collection")
    
    def _initialize_pattern_collection(self):
        """Initialize pattern collection with common memory and arithmetic patterns."""
        self.pattern_collection.add(
            ids=[
                # Memory patterns
                "pattern1", "pattern2", "pattern3", "pattern4", "pattern5",
                # Arithmetic patterns
                "pattern6", "pattern7", "pattern8", "pattern9", "pattern10",
                # CBMC verification knowledge
                "cbmc1", "cbmc2", "cbmc3", "cbmc4", "cbmc5", "cbmc6"
            ],
            documents=[
                # Memory patterns
                "Allocation without corresponding deallocation (malloc without free)",
                "Nested malloc calls with potential for partial free",
                "Conditional free that might not execute in all paths",
                "Memory leak through improper return path",
                "Double free or invalid free operations",
                
                # Arithmetic patterns
                "Integer overflow in arithmetic operations",
                "Division by zero risk",
                "Buffer overflow through array indexing",
                "Pointer arithmetic exceeding bounds",
                "Type conversion issues leading to data loss",
                
                # CBMC verification knowledge
                "CBMC memory-leak-check verification for allocated but not freed memory",
                "CBMC memory-cleanup-check verification for proper memory cleanup before exit",
                "CBMC bounds-check verification for array access within bounds",
                "CBMC pointer-overflow-check verification for pointer arithmetic operations",
                "CBMC conversion-check verification for problematic type conversions",
                "CBMC div-by-zero-check verification for division by zero risks"
            ],
            metadatas=[
                # Memory patterns metadata
                {
                    "name": "malloc_without_free",
                    "category": "memory",
                    "description": "Allocation without corresponding deallocation",
                    "severity": "high",
                    "verification_strategy": "Check all execution paths for memory deallocation",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(ptr == NULL, \"Memory leak detected\");"
                },
                {
                    "name": "nested_malloc",
                    "category": "memory",
                    "description": "Nested malloc calls with potential for partial free",
                    "severity": "medium",
                    "verification_strategy": "Ensure all allocations are freed in all execution paths",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(ptr1 == NULL && ptr2 == NULL, \"Nested memory leak detected\");"
                },
                {
                    "name": "conditional_free",
                    "category": "memory",
                    "description": "Conditional free that might not execute",
                    "severity": "medium",
                    "verification_strategy": "Verify all conditions that lead to memory release",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(condition || ptr == NULL, \"Conditional path may leak memory\");"
                },
                {
                    "name": "return_leak",
                    "category": "memory",
                    "description": "Memory leak through improper return path",
                    "severity": "medium",
                    "verification_strategy": "Check all return paths for proper memory cleanup",
                    "cbmc_flags": "--memory-leak-check --memory-cleanup-check",
                    "assertion_template": "__CPROVER_assert(returned_ptr == NULL, \"Function may leak memory through return\");"
                },
                {
                    "name": "double_free",
                    "category": "memory",
                    "description": "Double free or invalid free operations",
                    "severity": "high",
                    "verification_strategy": "Ensure each pointer is freed exactly once",
                    "cbmc_flags": "--memory-leak-check",
                    "assertion_template": "__CPROVER_assert(!freed[ptr_index], \"Potential double free\");"
                },
                
                # Arithmetic patterns metadata
                {
                    "name": "integer_overflow",
                    "category": "arithmetic",
                    "description": "Integer overflow in arithmetic operations",
                    "severity": "medium",
                    "verification_strategy": "Check bounds of integer arithmetic",
                    "cbmc_flags": "--conversion-check",
                    "assertion_template": "__CPROVER_assert(result >= INT_MIN && result <= INT_MAX, \"Integer overflow detected\");"
                },
                {
                    "name": "division_by_zero",
                    "category": "arithmetic",
                    "description": "Division by zero risk",
                    "severity": "high",
                    "verification_strategy": "Verify divisors are non-zero",
                    "cbmc_flags": "--div-by-zero-check",
                    "assertion_template": "__CPROVER_assume(divisor != 0);"
                },
                {
                    "name": "buffer_overflow",
                    "category": "arithmetic",
                    "description": "Buffer overflow through array indexing",
                    "severity": "high",
                    "verification_strategy": "Ensure array indices are within bounds",
                    "cbmc_flags": "--bounds-check",
                    "assertion_template": "__CPROVER_assert(index >= 0 && index < array_size, \"Buffer overflow detected\");"
                },
                {
                    "name": "pointer_arithmetic",
                    "category": "arithmetic",
                    "description": "Pointer arithmetic exceeding bounds",
                    "severity": "high",
                    "verification_strategy": "Verify pointer arithmetic stays within allocated bounds",
                    "cbmc_flags": "--pointer-overflow-check",
                    "assertion_template": "__CPROVER_assert(ptr >= base && ptr < base + size, \"Pointer arithmetic out of bounds\");"
                },
                {
                    "name": "type_conversion",
                    "category": "arithmetic",
                    "description": "Type conversion issues leading to data loss",
                    "severity": "low",
                    "verification_strategy": "Check for potential data loss in type conversions",
                    "cbmc_flags": "--conversion-check",
                    "assertion_template": "__CPROVER_assert(orig_value == (OrigType)((DestType)orig_value), \"Data loss in type conversion\");"
                },
                
                # CBMC verification knowledge metadata
                {
                    "name": "cbmc_memory_leak_check",
                    "category": "cbmc_verification",
                    "description": "Checks for memory that is allocated but not freed",
                    "verification_details": "Detects allocated memory that is never freed, memory that becomes unreachable, and double free operations",
                    "harness_usage": "Create appropriate memory allocations and verify they are properly freed",
                    "flag": "--memory-leak-check"
                },
                {
                    "name": "cbmc_memory_cleanup_check",
                    "category": "cbmc_verification",
                    "description": "Verifies all allocated memory is properly freed before program exit",
                    "verification_details": "More stringent than memory-leak-check, requires explicit cleanup of all allocations",
                    "harness_usage": "Ensure all memory allocations have corresponding free operations",
                    "flag": "--memory-cleanup-check"
                },
                {
                    "name": "cbmc_bounds_check",
                    "category": "cbmc_verification",
                    "description": "Verifies array accesses are within bounds",
                    "verification_details": "Detects buffer overflows and underflows for both static and dynamic arrays",
                    "harness_usage": "Test array accesses with both valid and invalid indices",
                    "flag": "--bounds-check"
                },
                {
                    "name": "cbmc_pointer_overflow_check",
                    "category": "cbmc_verification",
                    "description": "Detects pointer arithmetic that results in overflow",
                    "verification_details": "Checks pointer arithmetic operations to prevent undefined behavior",
                    "harness_usage": "Test pointer arithmetic operations with boundary values",
                    "flag": "--pointer-overflow-check"
                },
                {
                    "name": "cbmc_conversion_check",
                    "category": "cbmc_verification",
                    "description": "Detects problematic type conversions",
                    "verification_details": "Identifies loss of information in numeric conversions and sign conversion issues",
                    "harness_usage": "Test type conversions with values that may cause information loss",
                    "flag": "--conversion-check"
                },
                {
                    "name": "cbmc_div_by_zero_check",
                    "category": "cbmc_verification",
                    "description": "Checks for division by zero errors",
                    "verification_details": "Verifies both integer and floating-point divisions and modulo operations with zero divisor",
                    "harness_usage": "Test division operations with zero and near-zero divisors",
                    "flag": "--div-by-zero-check"
                }
            ]
        )
    
    # CODE EMBEDDING METHODS
    
    def add_code_function(self, func_id: str, func_code: str, metadata: Dict[str, Any]) -> bool:
        """
        Add a function to the code collection.
        
        Args:
            func_id: Unique ID for the function
            func_code: The function code
            metadata: Metadata about the function
            
        Returns:
            True if successful, False otherwise
        """
        try:
            self.code_collection.add(
                ids=[func_id],
                documents=[func_code],
                metadatas=[metadata]
            )
            logger.info(f"Added function {func_id} to code collection")
            return True
        except Exception as e:
            logger.error(f"Error adding function {func_id} to code collection: {str(e)}")
            return False
    
    def query_code_function(self, query: str, n_results: int = 5) -> List[Dict[str, Any]]:
        """
        Query the code collection for functions matching the query.
        
        Args:
            query: The search query
            n_results: Number of results to return
            
        Returns:
            List of matching functions with metadata
        """
        try:
            results = self.code_collection.query(
                query_texts=[query],
                n_results=n_results
            )
            
            functions = []
            if results["ids"] and results["ids"][0]:
                for i, func_id in enumerate(results["ids"][0]):
                    metadata = results["metadatas"][0][i]
                    distance = results["distances"][0][i] if "distances" in results else 1.0
                    
                    functions.append({
                        "func_id": func_id,
                        "code": results["documents"][0][i] if "documents" in results else "",
                        "metadata": metadata,
                        "similarity_score": 1.0 - distance
                    })
            
            return functions
        except Exception as e:
            logger.error(f"Error querying code collection: {str(e)}")
            return []
    
    def get_code_function(self, func_id: str) -> Optional[Dict[str, Any]]:
        """
        Get a specific function by ID.
        
        Args:
            func_id: ID of the function
            
        Returns:
            Function data or None if not found
        """
        try:
            result = self.code_collection.get(
                ids=[func_id],
                include=["documents", "metadatas"]
            )
            
            if result["ids"]:
                return {
                    "func_id": result["ids"][0],
                    "code": result["documents"][0],
                    "metadata": result["metadatas"][0]
                }
            return None
        except Exception as e:
            logger.error(f"Error getting function {func_id}: {str(e)}")
            return None
    
    # PATTERN METHODS
    
    def query_pattern_db(self, query: str) -> Dict[str, Any]:
        """
        Query the pattern collection for relevant patterns.
        
        Args:
            query: The search query
            
        Returns:
            Dictionary with matching patterns
        """
        # Query the pattern collection to find relevant patterns
        try:
            results = self.pattern_collection.query(
                query_texts=[query],
                n_results=3  # Get the top 3 matching patterns
            )
            
            # Also check via metadata if the function contains known indicators
            if "malloc(" in query and "free(" not in query:
                # Direct metadata match for malloc without free
                direct_match = "malloc_without_free"
            elif "if" in query and "free(" in query:
                # Potential conditional free
                direct_match = "conditional_free"
            elif query.count("malloc(") > 1:
                # Multiple malloc calls
                direct_match = "nested_malloc"
            else:
                direct_match = None
            
            # Process results
            matching_patterns = {}
            
            # Add patterns from semantic search
            if len(results['ids']) > 0:
                for i, (pattern_id, metadata, distance) in enumerate(zip(
                    results['ids'][0],
                    results['metadatas'][0],
                    results['distances'][0]
                )):
                    # Only include if reasonably close in embedding space
                    if distance < 0.3:
                        matching_patterns[metadata['name']] = {
                            "description": metadata["description"],
                            "severity": metadata["severity"],
                            "verification_strategy": metadata["verification_strategy"],
                            "similarity_score": 1.0 - distance  # Convert to similarity
                        }
            
            # Add direct match if found and not already included
            if direct_match and direct_match not in matching_patterns:
                # Find the metadata for this pattern
                pattern_match_idx = ['malloc_without_free', 'nested_malloc', 'conditional_free'].index(direct_match) + 1
                pattern_id = f"pattern{pattern_match_idx}"
                metadata_results = self.pattern_collection.get(ids=[pattern_id])
                if metadata_results['ids']:
                    for metadata in metadata_results['metadatas']:
                        if metadata['name'] == direct_match:
                            matching_patterns[direct_match] = {
                                "description": metadata["description"],
                                "severity": metadata["severity"],
                                "verification_strategy": metadata["verification_strategy"],
                                "similarity_score": 1.0  # Direct match gets perfect score
                            }
                            break
            
            return {
                "matching_patterns": matching_patterns,
                "message": f"Found {len(matching_patterns)} potential matching patterns"
            }
        except Exception as e:
            logger.error(f"Error querying pattern database: {str(e)}")
            return {
                "matching_patterns": {},
                "message": f"Error querying pattern database: {str(e)}"
            }
    
    # ERROR AND SOLUTION METHODS
    
    def store_error(self, 
                func_name: str, 
                harness_code: str, 
                cbmc_result: Dict[str, Any], 
                iteration: int) -> str:
        """
        Enhanced error storage with pattern evolution tracking.
        """
        # Generate a unique ID
        error_id = f"{func_name}_error_{iteration}_{int(time.time())}"
        
        # Extract key error information
        error_categories = cbmc_result.get("error_categories", [])
        error_message = cbmc_result.get("message", "Unknown error")
        
        # Create error description for embedding
        error_description = f"Function: {func_name}\nError: {error_message}\nCategories: {', '.join(error_categories)}"
        
        # Extract failing code patterns for better retrieval
        error_locations = cbmc_result.get("error_locations", {})
        error_lines = []
        
        # Find the harness lines corresponding to errors
        for file_name, line_nums in error_locations.items():
            harness_lines = harness_code.split('\n')
            for line_num in line_nums:
                # Convert line_num to integer if it's a string
                if isinstance(line_num, str):
                    try:
                        line_num = int(line_num)
                    except ValueError:
                        continue
                
                # Only add lines that exist in the harness (adjust for 0-indexing)
                if 0 <= line_num - 1 < len(harness_lines):
                    error_lines.append(harness_lines[line_num - 1].strip())
        
        # Add error line snippets to description if available
        if error_lines:
            error_description += f"\nError patterns:\n" + "\n".join(error_lines)
        
        # Store error in knowledge base with enhanced tracking
        try:
            # Convert lists to strings for ChromaDB compatibility
            # Fix: Convert the list to a JSON string
            refinement_attempts_str = json.dumps([iteration])
            
            # Add new metadata fields for pattern evolution
            error_metadata = {
                "func_name": func_name,
                "iteration": iteration,
                "error_categories": json.dumps(error_categories),  # Convert list to JSON string
                "error_message": error_message,
                "has_memory_leak": "memory_leak" in error_categories,
                "has_array_bounds": "array_bounds" in error_categories,
                "has_null_pointer": "null_pointer" in error_categories,
                "has_arithmetic_issue": any(cat in error_categories for cat in ["division_by_zero", "arithmetic_overflow"]),
                "timestamp": time.time(),
                
                # NEW FIELDS FOR TRACKING - Fix: Convert lists to JSON strings
                "refinement_attempts": refinement_attempts_str,  # Fixed: JSON string instead of list
                "persistence_count": 1,
                "is_resolved": False,
                "is_challenging": False,
                
                # Error pattern details - Fix: Convert lists to JSON strings
                "error_lines": json.dumps(error_lines),  # Convert list to JSON string
                "cbmc_error_details": json.dumps({
                    "reachable_lines": cbmc_result.get("reachable_lines", 0),
                    "covered_lines": cbmc_result.get("covered_lines", 0),
                    "coverage_pct": cbmc_result.get("coverage_pct", 0.0)
                })
            }
            
            # Add the error to the collection
            self.error_collection.add(
                ids=[error_id],
                documents=[error_description],
                metadatas=[error_metadata]
            )
            
            # Prune old entries if collection gets too large
            if self.error_collection.count() > 1000:
                # Remove oldest errors to keep the collection manageable
                oldest_errors = self.error_collection.get(
                    sort="timestamp", 
                    limit=100
                )
                if oldest_errors["ids"]:
                    self.error_collection.delete(ids=oldest_errors["ids"])
            
            logger.info(f"Stored error pattern {error_id} for {func_name}")
            return error_id
        except Exception as e:
            logger.error(f"Error storing error pattern: {str(e)}")
            return ""

    def store_solution(self, 
                       error_id: str, 
                       func_name: str, 
                       harness_code: str, 
                       cbmc_result: Dict[str, Any],
                       iteration: int) -> str:
        """
        Enhanced solution storage with effectiveness tracking.
        """
        # Generate a unique ID
        solution_id = f"{func_name}_solution_{iteration}_{int(time.time())}"
        
        # Determine solution effectiveness
        is_effective = cbmc_result.get("verification_status") == "SUCCESS"
        
        # Create solution description for embedding
        solution_description = f"Function: {func_name}\nHarness for iteration {iteration}"
        
        # Extract successful patterns
        patterns = []
        
        # Find malloc/free patterns
        malloc_free_pattern = self._extract_pattern(harness_code, r'(\w+\s*=\s*malloc\([^;]+;.*?free\(\s*\w+\s*\);)', 
                                                   "Memory allocation pattern")
        if malloc_free_pattern:
            patterns.append(malloc_free_pattern)
        
        # Find null checks
        null_check_pattern = self._extract_pattern(harness_code, r'(if\s*\(\s*\w+\s*==\s*NULL\s*\)[^}]+})', 
                                                  "Null check pattern")
        if null_check_pattern:
            patterns.append(null_check_pattern)
        
        # Find CPROVER assumes
        cprover_pattern = self._extract_pattern(harness_code, r'(__CPROVER_assume\([^;]+;)', 
                                               "CPROVER assumption pattern")
        if cprover_pattern:
            patterns.append(cprover_pattern)
        
        # Store solution in knowledge base with enhanced tracking
        try:
            # Check for existing solutions for this error or function
            # Make sure we only include non-empty strings in the query
            query_conditions = []
            if error_id and isinstance(error_id, str):
                query_conditions.append({"$contains": error_id})
            if func_name and isinstance(func_name, str):
                query_conditions.append({"$contains": func_name})
                
            # If we have conditions, execute the query
            if query_conditions:
                if len(query_conditions) == 1:
                    # If only one condition, use it directly
                    existing_solutions = self.solution_collection.get(
                        where_document=query_conditions[0],
                        include=["metadatas"]
                    )
                else:
                    # If multiple conditions, use $or operator
                    existing_solutions = self.solution_collection.get(
                        where_document={"$or": query_conditions},
                        include=["metadatas"]
                    )
            else:
                # Default empty result if no valid conditions
                existing_solutions = {"ids": [], "metadatas": []}
            
            # Track total attempts and effectiveness
            total_attempts = 1
            effectiveness_iterations = [iteration] if is_effective else []
            overall_effectiveness = is_effective
            
            # Update tracking if solution exists
            if existing_solutions["ids"]:
                for existing_metadata in existing_solutions["metadatas"]:
                    total_attempts = existing_metadata.get("total_attempts", 1) + 1
                    effectiveness_iterations = existing_metadata.get("effectiveness_iterations", [])
                    overall_effectiveness = existing_metadata.get("is_effective", is_effective)
                    
                    # Add current iteration if effective
                    if is_effective and iteration not in effectiveness_iterations:
                        effectiveness_iterations.append(iteration)
                        overall_effectiveness = True
            
            # Metadata for solution storage
            solution_metadata = {
                "func_name": func_name,
                "iteration": iteration,
                "related_error_id": error_id,
                "is_effective": overall_effectiveness,
                "total_attempts": total_attempts,
                "effectiveness_iterations": effectiveness_iterations,
                
                # Detailed metadata
                "coverage": cbmc_result.get("coverage_pct", 0.0),
                "patterns_found": len(patterns),
                "has_malloc_free": bool(malloc_free_pattern),
                "has_null_check": bool(null_check_pattern),
                "has_cprover_assume": bool(cprover_pattern),
                "timestamp": time.time(),
                
                # Store complete harness for potential reuse
                "harness_code": harness_code,
                
                # Additional function-specific metrics
                "func_reachable_lines": cbmc_result.get("func_reachable_lines", 0),
                "func_coverage_pct": cbmc_result.get("func_coverage_pct", 0.0)
            }
            
            # Add solution to collection
            self.solution_collection.add(
                ids=[solution_id],
                documents=[solution_description],
                metadatas=[solution_metadata]
            )
            
            # Prune old solutions to keep collection manageable
            if self.solution_collection.count() > 1000:
                oldest_solutions = self.solution_collection.get(
                    sort="timestamp", 
                    limit=100
                )
                if oldest_solutions["ids"]:
                    self.solution_collection.delete(ids=oldest_solutions["ids"])
            
            logger.info(f"Stored solution {solution_id} for {func_name}")
            return solution_id
        except Exception as e:
            logger.error(f"Error storing solution: {str(e)}")
            return ""

    def get_recommendations(self, 
                           func_name: str, 
                           func_code: str, 
                           cbmc_result: Dict[str, Any],
                           previous_harness: str) -> Dict[str, Any]:
        """
        Enhanced recommendation generation with solution effectiveness filtering.
        """
        # Extract error information
        error_categories = cbmc_result.get("error_categories", [])
        error_message = cbmc_result.get("message", "Unknown error")
        
        # Build error description
        error_description = f"{error_message}"
        if error_categories:
            error_description += f" Categories: {', '.join(error_categories)}"
        
        # Query for similar errors
        similar_errors = self.query_similar_errors(func_name, func_code, error_description)
        
        # Get solutions for similar errors
        solutions = []
        if similar_errors:
            # Get the most similar error
            most_similar = similar_errors[0]
            
            # Enhanced solution filtering
            all_solutions = self.query_solutions_for_error(most_similar["error_id"], func_name)
            
            # Filter for only effective solutions with high success rate
            solutions = [
                sol for sol in all_solutions 
                if sol.get('is_effective', False) and 
                   (sol.get('total_attempts', 0) <= 3 or  # Prefer newer solutions
                    len(sol.get('effectiveness_iterations', [])) / sol.get('total_attempts', 1) > 0.5)  # High effectiveness ratio
            ]
        
        # Query for patterns that match this function's issues
        pattern_results = self.query_pattern_db(func_code)
        matching_patterns = pattern_results.get("matching_patterns", {})
        
        # Build recommendation
        recommendation = {
            "has_similar_errors": bool(similar_errors),
            "similar_errors": similar_errors,
            "has_solutions": bool(solutions),
            "solutions": solutions[:2],  # Limit to top 2 solutions
            "has_matching_patterns": bool(matching_patterns),
            "matching_patterns": matching_patterns,
            "error_categories": error_categories,
            "recommendations": []
        }
        
        # Generate recommendations with enhanced effectiveness filtering
        if solutions:
            # Prioritize most effective solution
            best_solution = solutions[0]
            recommendation["recommendations"].append({
                "type": "effective_solution",
                "message": f"Found an effective solution with {len(best_solution.get('effectiveness_iterations', []))} successful runs",
                "harness_code": best_solution.get("harness_code", ""),
                "effectiveness_score": (len(best_solution.get('effectiveness_iterations', [])) / 
                                        best_solution.get('total_attempts', 1)) * 100
            })
        elif matching_patterns:
            # Fall back to pattern recommendations
            for pattern_name, pattern_info in matching_patterns.items():
                recommendation["recommendations"].append({
                    "type": "pattern",
                    "pattern_name": pattern_name,
                    "message": f"Found a matching pattern: {pattern_info['description']}",
                    "verification_strategy": pattern_info["verification_strategy"],
                    "severity": pattern_info["severity"]
                })
        
        # Add default recommendations based on error categories
        default_recommendations = []
        if "memory_leak" in error_categories:
            default_recommendations.append({
                "type": "memory",
                "message": "Ensure comprehensive memory cleanup",
                "suggestion": "Add explicit free() for all malloc() calls, verify memory paths"
            })
        
        if "null_pointer" in error_categories:
            default_recommendations.append({
                "type": "pointer",
                "message": "Implement robust null pointer handling",
                "suggestion": "Add comprehensive null checks, use __CPROVER_assume() for constraining pointer usage"
            })
        
        recommendation["recommendations"].extend(default_recommendations)
        
        return recommendation

    def query_solutions_for_error(self, 
                                  error_id: str, 
                                  func_name: str, 
                                  top_k: int = 3) -> List[Dict[str, Any]]:
        """
        Enhanced solution query with effectiveness scoring.
        """
        def solution_score(solution):
            """Calculate a score based on solution effectiveness."""
            effectiveness_iterations = solution.get('effectiveness_iterations', [])
            total_attempts = solution.get('total_attempts', 1)
            
            # Core effectiveness calculation
            effectiveness_ratio = len(effectiveness_iterations) / total_attempts
            
            # Age penalty - solutions become less relevant over time
            age_penalty = (time.time() - solution.get('timestamp', time.time())) / (24 * 3600)  # Daily decay
            
            # Combine effectiveness and recency
            return effectiveness_ratio / (1 + age_penalty)
        
        # Query solutions
        if not error_id:
            solutions = self.solution_collection.get(
                where={"func_name": func_name},
                include=["documents", "metadatas"]
            )
        else:
            # Build query conditions
            query_conditions = []
            if error_id and isinstance(error_id, str):
                query_conditions.append({"$contains": error_id})
            if func_name and isinstance(func_name, str):
                query_conditions.append({"$contains": func_name})
            
            # Try to find solutions for the specific error
            if not query_conditions:
                # No valid conditions, use empty result
                solutions = {"ids": [], "metadatas": []}
            elif len(query_conditions) == 1:
                # Only one condition, use it directly
                solutions = self.solution_collection.get(
                    where_document=query_conditions[0],
                    include=["documents", "metadatas"]
                )
            else:
                # Multiple conditions, use $or
                solutions = self.solution_collection.get(
                    where_document={"$or": query_conditions},
                    include=["documents", "metadatas"]
                )
        
        # Process solutions
        solution_list = []
        for i, sol_id in enumerate(solutions.get("ids", [])):
            solution_list.append({
                "solution_id": sol_id,
                "func_name": solutions["metadatas"][i].get("func_name", ""),
                "iteration": solutions["metadatas"][i].get("iteration", 0),
                "is_effective": solutions["metadatas"][i].get("is_effective", False),
                "total_attempts": solutions["metadatas"][i].get("total_attempts", 1),
                "coverage": solutions["metadatas"][i].get("coverage", 0.0),
                "effectiveness_score": 0.0,  # Will be filled in sorting
                "harness_code": solutions["metadatas"][i].get("harness_code", ""),
                "effectiveness_iterations": solutions["metadatas"][i].get("effectiveness_iterations", [])
            })
        
        # Sort solutions by effectiveness
                # Attach effectiveness scores
        for solution in solution_list:
            solution['effectiveness_score'] = solution_score(solution)
        
        # Sort solutions by effectiveness score
        sorted_solutions = sorted(
            solution_list, 
            key=lambda x: x['effectiveness_score'], 
            reverse=True
        )
        
        # Update solutions with their calculated score
        for solution in sorted_solutions:
            solution['effectiveness_pct'] = solution['effectiveness_score'] * 100
        
        # Return top k solutions
        return sorted_solutions[:top_k]

    def recognize_global_error_patterns(self) -> List[Dict[str, Any]]:
        """
        Analyze stored errors to identify systemic verification challenges.
        
        Returns:
            List of global error pattern recommendations
        """
        try:
            # Fetch all errors
            errors = self.error_collection.get(
                include=["documents", "metadatas"],
                limit=1000  # Reasonable upper limit
            )
            
            # Categorize error patterns
            error_categories = {}
            for i, metadata in enumerate(errors.get("metadatas", [])):
                categories = json.loads(metadata.get("error_categories", "[]"))
                for category in categories:
                    if category not in error_categories:
                        error_categories[category] = {
                            "count": 0,
                            "challenging_count": 0,
                            "persistence_details": []
                        }
                    
                    error_categories[category]["count"] += 1
                    
                    # Track challenging patterns
                    if metadata.get("is_challenging", False):
                        error_categories[category]["challenging_count"] += 1
                        error_categories[category]["persistence_details"].append({
                            "func_name": metadata.get("func_name", "Unknown"),
                            "iterations": json.loads(metadata.get("refinement_attempts", "[]")),
                            "error_message": metadata.get("error_message", "")
                        })
            
            # Generate recommendations based on error analysis
            global_recommendations = []
            for category, details in error_categories.items():
                # Calculate challenge ratio
                challenge_ratio = details["challenging_count"] / details["count"] if details["count"] > 0 else 0
                
                recommendation = {
                    "category": category,
                    "total_occurrences": details["count"],
                    "challenging_occurrences": details["challenging_count"],
                    "challenge_ratio": challenge_ratio,
                    "recommended_strategy": "Standard verification",
                    "mitigation_suggestions": []
                }
                
                # Provide targeted recommendations based on challenge ratio
                if challenge_ratio > 0.5:
                    recommendation["recommended_strategy"] = "Advanced verification required"
                    
                    if category == "memory_leak":
                        recommendation["mitigation_suggestions"] = [
                            "Implement comprehensive memory tracking",
                            "Use static analysis tools for memory management",
                            "Create more sophisticated memory cleanup harnesses"
                        ]
                    elif category == "null_pointer":
                        recommendation["mitigation_suggestions"] = [
                            "Enhance null pointer constraint generation",
                            "Implement more rigorous null check patterns",
                            "Use advanced CPROVER assume techniques"
                        ]
                    elif category == "array_bounds":
                        recommendation["mitigation_suggestions"] = [
                            "Develop more robust array access constraints",
                            "Generate harnesses with explicit bounds checking",
                            "Use symbolic execution techniques"
                        ]
                
                global_recommendations.append(recommendation)
            
            return global_recommendations
        
        except Exception as e:
            logger.error(f"Error in global error pattern recognition: {str(e)}")
            return []
    
    def query_similar_errors(self, 
                           func_name: str, 
                           func_code: str, 
                           error_description: str, 
                           top_k: int = 3) -> List[Dict[str, Any]]:
        """
        Query the error collection for similar error patterns.
        
        Args:
            func_name: Name of the function
            func_code: The function code
            error_description: Description of the current error
            top_k: Number of results to return
            
        Returns:
            List of similar error patterns with metadata
        """
        # Create query combining function information with error description
        function_signature = self._extract_function_signature(func_code)
        query = f"Function: {func_name}\n{function_signature}\nError: {error_description}"
        
        # Check if there are any errors in the database
        if self.error_collection.count() == 0:
            logger.info("No errors in knowledge base yet")
            return []
        
        try:
            # Query for similar errors
            results = self.error_collection.query(
                query_texts=[query],
                n_results=top_k
            )
            
            # Process and return results
            similar_errors = []
            if results["ids"] and results["ids"][0]:
                for i, error_id in enumerate(results["ids"][0]):
                    # Skip if we have no metadatas
                    if not results["metadatas"] or not results["metadatas"][0]:
                        continue
                        
                    metadata = results["metadatas"][0][i]
                    distance = results["distances"][0][i] if "distances" in results else 1.0
                    
                    # Convert JSON strings back to Python objects
                    error_categories = json.loads(metadata.get("error_categories", "[]"))
                    
                    similar_errors.append({
                        "error_id": error_id,
                        "func_name": metadata.get("func_name", ""),
                        "error_categories": error_categories,
                        "error_message": metadata.get("error_message", ""),
                        "similarity_score": 1.0 - distance,  # Convert distance to similarity
                        "document": results["documents"][0][i] if "documents" in results else ""
                    })
            
            logger.info(f"Found {len(similar_errors)} similar errors for {func_name}")
            return similar_errors
        except Exception as e:
            logger.error(f"Error querying similar errors: {str(e)}")
            return []

    def _extract_function_signature(self, func_code: str) -> str:
        """
        Extract the function signature from the function code.
        
        Args:
            func_code: The function code
            
        Returns:
            Function signature (return type, name, parameters)
        """
        signature_match = re.search(r'^([\w\s\*]+)\s+(\w+)\s*\(([^)]*)\)', func_code.strip(), re.MULTILINE)
        if signature_match:
            return_type = signature_match.group(1).strip()
            func_name = signature_match.group(2).strip()
            params = signature_match.group(3).strip()
            return f"{return_type} {func_name}({params})"
        return ""
   
    def _extract_pattern(self, code: str, pattern: str, label: str) -> str:
        """
        Extract reusable code patterns from harness code.
        
        Args:
            code: The harness code
            pattern: Regex pattern to extract
            label: Label for the pattern
            
        Returns:
            Extracted pattern with label or empty string if not found
        """
        # Ensure code is a string and pattern is valid
        if not isinstance(code, str) or not pattern:
            return ""
        
        # Use re.DOTALL to match across multiple lines
        matches = re.findall(pattern, code, re.DOTALL)
        
        if matches:
            # Return the first match with label
            first_match = matches[0]
            
            # If match is a tuple (from multiple capture groups), take the first element
            if isinstance(first_match, tuple):
                first_match = first_match[0]
            
            return f"{label}:\n{first_match.strip()}"
        
        return ""
# Global instance for convenience
_db_instance = None

def get_unified_db(persistence_dir: str = "rag_db") -> UnifiedEmbeddingDB:
    """
    Get the global unified database instance.
    
    Args:
        persistence_dir: Directory for persistence
        
    Returns:
        The global UnifiedEmbeddingDB instance
    """
    global _db_instance
    if _db_instance is None:
        _db_instance = UnifiedEmbeddingDB(persistence_dir)
    return _db_instance