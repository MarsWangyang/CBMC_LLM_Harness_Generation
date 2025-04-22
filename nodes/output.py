"""
Output node for CBMC harness generator workflow with unified RAG database integration.
"""
import os
import time
from langchain_core.messages import AIMessage
import logging
import polars as pl
from typing import Dict, List, Any, Optional
from utils.rag import get_unified_db

logger = logging.getLogger("output")

def output_node(state):
    """Provides final summary and generates reports with unified RAG database integration."""
    total_time = time.time() - state.get("start_time", time.time())

    logger.info("Generating final report and output summaries")
    
    # Get result directories from state
    result_directories = state.get("result_directories", {})
    reports_dir = result_directories.get("reports_dir", "reports")
    harnesses_dir = result_directories.get("harnesses_dir", "harnesses")
    verification_dir = result_directories.get("verification_dir", "verification")
    result_base_dir = result_directories.get("result_base_dir", "results")
    
    # Get the unified RAG database
    rag_db = get_unified_db(os.path.join(result_base_dir, "rag_data"))
    
    # Get LLM model info
    llm_used = state.get("llm_used", "claude")
    
    # Determine if we're in directory mode
    is_directory_mode = state.get("is_directory_mode", False)
    
    # Get all vulnerable functions and harnesses
    vulnerable_functions = state.get("vulnerable_functions", [])
    harnesses = state.get("harnesses", {})
    cbmc_results = state.get("cbmc_results", {})
    
    # Check if all harnesses have been generated and verified
    all_harnesses_complete = True
    for func_name in vulnerable_functions:
        if func_name not in harnesses or func_name not in cbmc_results:
            all_harnesses_complete = False
            logger.warning(f"Function {func_name} does not have complete harness or verification results")
    
    # Calculate summary statistics
    function_times = state.get("function_times", {})
    total_refinements = sum(state.get("refinement_attempts", {}).values())
    
    # Load both coverage and error metrics from existing CSV files
    # Construct the paths using the LLM model and result directories
    coverage_dir = os.path.join(result_base_dir, "coverage", "data")
    errors_dir = os.path.join(result_base_dir, "errors", "data")
    coverage_file_path = os.path.join(coverage_dir, "coverage_metrics.csv")
    error_file_path = os.path.join(errors_dir, "error_metrics.csv")
    coverage_df = pl.DataFrame()
    error_df = pl.DataFrame()
    
    # Load coverage metrics
    if os.path.exists(coverage_file_path):
        logger.info(f"Loading coverage metrics from {coverage_file_path}")
        try:
            coverage_df = pl.read_csv(coverage_file_path)
            logger.info(f"Loaded coverage data with {len(coverage_df)} rows")
        except Exception as e:
            logger.error(f"Error reading coverage CSV: {str(e)}")
    else:
        logger.warning(f"Coverage metrics file not found at {coverage_file_path}")
        
    # Load error metrics
    if os.path.exists(error_file_path):
        logger.info(f"Loading error metrics from {error_file_path}")
        try:
            error_df = pl.read_csv(error_file_path)
            logger.info(f"Loaded error data with {len(error_df)} rows")
        except Exception as e:
            logger.error(f"Error reading error CSV: {str(e)}")
    else:
        logger.warning(f"Error metrics file not found at {error_file_path}")
    
    # Calculate aggregate metrics from the coverage data if loaded
    aggregate_metrics = {
        "total_reachable_lines": 0,
        "total_covered_lines": 0,
        "func_reachable_lines": 0,
        "func_covered_lines": 0,
        "total_reported_errors": 0,
        "functions_with_full_coverage": 0,
        "functions_without_errors": 0
    }
    
    if not coverage_df.is_empty():
        # Get latest version for each function
        try:
            latest_versions = coverage_df.group_by("function").agg(pl.max("version").alias("max_version"))
            latest_metrics = []
            
            for func_name, max_version in zip(latest_versions["function"], latest_versions["max_version"]):
                # Get metrics for this function and version
                metrics = coverage_df.filter(
                    (pl.col("function") == func_name) & (pl.col("version") == max_version)
                ).row(0, named=True)
                
                latest_metrics.append(metrics)
                
                # Add to aggregate totals - ensure we're handling numeric values only
                for metric_key in ["total_reachable_lines", "total_covered_lines", "func_reachable_lines", "func_covered_lines"]:
                    if metric_key in metrics:
                        metric_val = metrics[metric_key]
                        if isinstance(metric_val, (int, float)) and metric_val != "NA":
                            aggregate_metrics[metric_key] += int(metric_val)
                
                # Get all error metrics and add the highest one to the total
                reported_error_val = 0
                failure_count_val = 0
                error_count_val = 0
                
                # Process reported_errors
                if "reported_errors" in metrics:
                    error_val = metrics["reported_errors"]
                    # Try to convert string to int if needed
                    if isinstance(error_val, str) and error_val != "NA":
                        try:
                            reported_error_val = int(float(error_val))
                        except (ValueError, TypeError):
                            pass
                    elif isinstance(error_val, (int, float)) and error_val != "NA":
                        reported_error_val = int(error_val)
                
                # Process failure_count
                if "failure_count" in metrics:
                    failure_val = metrics["failure_count"]
                    if isinstance(failure_val, str) and failure_val != "NA":
                        try:
                            failure_count_val = int(float(failure_val))
                        except (ValueError, TypeError):
                            pass
                    elif isinstance(failure_val, (int, float)) and failure_val != "NA":
                        failure_count_val = int(failure_val)
                
                # Process error_count
                if "error_count" in metrics:
                    error_count = metrics["error_count"]
                    if isinstance(error_count, str) and error_count != "NA":
                        try:
                            error_count_val = int(float(error_count))
                        except (ValueError, TypeError):
                            pass
                    elif isinstance(error_count, (int, float)) and error_count != "NA":
                        error_count_val = int(error_count)
                
                # Add the highest non-zero error value to the total
                max_error_value = max(reported_error_val, failure_count_val, error_count_val)
                aggregate_metrics["total_reported_errors"] += max_error_value
                
                # Count functions with full coverage
                if "func_coverage_pct" in metrics:
                    coverage_val = metrics["func_coverage_pct"]
                    if isinstance(coverage_val, (int, float)) and coverage_val != "NA" and float(coverage_val) >= 95.0:
                        aggregate_metrics["functions_with_full_coverage"] += 1
                
                # Count functions without errors by checking all error metrics
                # Convert the values we already calculated above for reported_error_val, failure_count_val, and error_count_val
                # If all error values are 0, increment functions without errors
                if max(reported_error_val, failure_count_val, error_count_val) == 0:
                    aggregate_metrics["functions_without_errors"] += 1
        except Exception as e:
            logger.error(f"Error processing coverage data: {str(e)}")
    
    # Calculate overall coverage percentages with safety checks
    overall_total_coverage = 0.0
    if aggregate_metrics["total_reachable_lines"] > 0 and aggregate_metrics["total_covered_lines"] > 0:
        overall_total_coverage = (aggregate_metrics["total_covered_lines"] / aggregate_metrics["total_reachable_lines"]) * 100
        
    overall_func_coverage = 0.0
    if aggregate_metrics["func_reachable_lines"] > 0 and aggregate_metrics["func_covered_lines"] > 0:
        overall_func_coverage = (aggregate_metrics["func_covered_lines"] / aggregate_metrics["func_reachable_lines"]) * 100
    
    # Create performance metrics
    if function_times:
        avg_generation_time = sum(times.get("generation", 0) for times in function_times.values()) / len(function_times)
        avg_verification_time = sum(times.get("verification", 0) for times in function_times.values()) / len(function_times)
        avg_evaluation_time = sum(times.get("evaluation", 0) for times in function_times.values()) / len(function_times)
        avg_refinements = total_refinements / len(state.get("refinement_attempts", {})) if state.get("refinement_attempts", {}) else 0
    else:
        avg_generation_time = avg_verification_time = avg_evaluation_time = avg_refinements = 0
    
    # Get RAG database statistics
    try:
        rag_stats = {
            "code_functions": rag_db.code_collection.count(),
            "patterns": rag_db.pattern_collection.count(),
            "errors": rag_db.error_collection.count(),
            "solutions": rag_db.solution_collection.count()
        }
        logger.info(f"RAG database statistics: {rag_stats}")
    except Exception as e:
        logger.error(f"Error getting RAG statistics: {str(e)}")
        rag_stats = {
            "code_functions": 0,
            "patterns": 0,
            "errors": 0,
            "solutions": 0
        }
    
    # Create a header based on mode
    if is_directory_mode:
        source_files = state.get("source_files", {})
        header = [
            f"# CBMC Harness Generation Complete - Directory Mode - {llm_used.capitalize()}",
            "",
            f"Total processing time: {total_time:.2f} seconds",
            f"Processed {len(source_files)} source files.",
            f"Analyzed {len(state.get('embeddings', {}).get('functions', {}))} functions.",
            f"Identified {len(state.get('vulnerable_functions', []))} functions with memory or arithmetic operations.",
            f"Generated {len(state.get('harnesses', {}))} verification harnesses.",
            f"Performed {total_refinements} harness refinements (average {avg_refinements:.2f} per function).",
        ]
        
        # Add file statistics
        header.extend([
            "",
            "## File Analysis",
        ])
        
        # Group functions by file
        files_functions = {}
        for func_id in state.get('vulnerable_functions', []):
            file_name = "unknown"
            if ":" in func_id:
                file_name, _ = func_id.split(":", 1)
            
            if file_name not in files_functions:
                files_functions[file_name] = []
            files_functions[file_name].append(func_id)
        
        # Add file details
        for file_name, funcs in files_functions.items():
            header.append(f"\n### {file_name}")
            header.append(f"Functions analyzed: {len(funcs)}")
            verified_funcs = [f for f in funcs if f in state.get('cbmc_results', {})]
            header.append(f"Functions verified: {len(verified_funcs)}")
            
            if verified_funcs:
                successful = sum(1 for f in verified_funcs if state.get('cbmc_results', {}).get(f, {}).get('status') == 'SUCCESS')
                header.append(f"Successful verifications: {successful}")
                header.append(f"Failed verifications: {len(verified_funcs) - successful}")
    else:
        # Single file mode header
        header = [
            f"# CBMC Harness Generation Complete - {llm_used.capitalize()}",
            "",
            f"Total processing time: {total_time:.2f} seconds",
            f"Analyzed {len(state.get('embeddings', {}).get('functions', {}))} functions.",
            f"Identified {len(state.get('vulnerable_functions', []))} functions with memory or arithmetic operations.",
            f"Generated {len(state.get('harnesses', {}))} verification harnesses.",
            f"Performed {total_refinements} harness refinements (average {avg_refinements:.2f} per function).",
        ]
    
    # Add RAG database statistics section
    header.extend([
        "",
        "## RAG Knowledge Base Statistics",
        f"Code functions stored: {rag_stats['code_functions']}",
        f"Pattern templates: {rag_stats['patterns']}",
        f"Error patterns stored: {rag_stats['errors']}",
        f"Successful solutions: {rag_stats['solutions']}",
        "",
        "The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.",
    ])
    
    # Add unit proof metrics summary
    header.extend([
        "",
        "## Unit Proof Metrics Summary",
        f"Total reachable lines: {aggregate_metrics['total_reachable_lines']}",
        f"Total coverage: {overall_total_coverage:.2f}%",
        f"Total reachable lines for harnessed functions only: {aggregate_metrics['func_reachable_lines']}",
        f"Coverage of harnessed functions only: {overall_func_coverage:.2f}%",
        f"Number of reported errors: {aggregate_metrics['total_reported_errors']}",
        f"Functions with full coverage: {aggregate_metrics['functions_with_full_coverage']} of {len(state.get('cbmc_results', {}))}",
        f"Functions without errors: {aggregate_metrics['functions_without_errors']} of {len(state.get('cbmc_results', {}))}",
        "",
        "### Note on Error Reporting:",
        "- Errors are grouped by line number (one error per line)",
        "- Errors about missing function bodies are excluded",
        "- Loop unwinding assertions are excluded from error count",
    ])
    
    # Generate the enhanced coverage matrix table with more detailed metrics
    if not coverage_df.is_empty():
        # Extract functions and versions from the dataframe
        functions = sorted(list(set(coverage_df["function"].to_list())))
        versions = sorted(list(set(coverage_df["version"].to_list())))
        
        # Add table title
        header.extend([
            "",
            "## Detailed Coverage Matrix by Function and Version",
            "",
            "The table below shows detailed metrics for each function across different versions of the generated harnesses:",
            ""
        ])
        
        # Create markdown table with functions as rows and versions as columns
        # For each version, we have three sub-columns: Total Coverage, Functional Coverage, and Errors
        
        # Table header row with version columns
        # Table header row with version columns
        header_row = "| Function "
        for version in versions:
            header_row += f"| Version {version} "
        header_row += "|"
        header.append(header_row)

        # Sub-header row with Total, Func, and Errors columns for each version
        subheader_row = "| --- "
        for _ in versions:
            subheader_row += "| Total % | Func % | Errors "
        subheader_row += "|"
        header.append(subheader_row)

        # Data rows
        for function in functions:
            func_row = f"| {function} "
            for version in versions:
                # Find the record for this function and version
                try:
                    func_data = coverage_df.filter(
                        (pl.col("function") == function) & (pl.col("version") == version)
                    )
                    
                    if not func_data.is_empty():
                        record = func_data.row(0, named=True)
                        
                        # Handle both numeric and string values safely
                        total_cov_val = record.get("total_coverage_pct", "N/A")
                        func_cov_val = record.get("func_coverage_pct", "N/A")
                        errors_val = record.get("reported_errors", "N/A")
                        
                        # Try to get error data from error_df if available
                        if not error_df.is_empty():
                            error_data = error_df.filter(
                                (pl.col("function") == function) & (pl.col("version") == version)
                            )
                            if not error_data.is_empty():
                                error_record = error_data.row(0, named=True)
                                # Use error data directly from error metrics
                                if "error_count" in error_record and error_record["error_count"] != "N/A":
                                    errors_val = error_record["error_count"]
                                elif "reported_errors" in error_record and error_record["reported_errors"] != "N/A":
                                    errors_val = error_record["reported_errors"]
                        
                        # Fallback to coverage metrics if error data not found
                        if errors_val == "N/A" and "failure_count" in record:
                            errors_val = record.get("failure_count", "N/A")
                        # Also check for error_count which might be present instead
                        if errors_val == "N/A" and "error_count" in record:
                            errors_val = record.get("error_count", "N/A")
                        
                        # Ensure errors_val is properly converted to integer if it's a string
                        if isinstance(errors_val, str) and errors_val != "N/A":
                            try:
                                errors_val = int(float(errors_val))
                            except (ValueError, TypeError):
                                errors_val = 0
                        
                        # Format values properly
                        if isinstance(total_cov_val, (int, float)):
                            total_cov = f"{total_cov_val:.2f}%"
                        else:
                            total_cov = "N/A"
                            
                        if isinstance(func_cov_val, (int, float)):
                            func_cov = f"{func_cov_val:.2f}%"
                        else:
                            func_cov = "N/A"
                            
                        if isinstance(errors_val, (int, float)):
                            errors = str(errors_val)
                        else:
                            errors = "0"  # Default to 0 instead of N/A for errors
                            
                        func_row += f"| {total_cov} | {func_cov} | {errors} "
                    else:
                        func_row += "| - | - | - "
                except Exception as e:
                    logger.error(f"Error formatting coverage data: {str(e)}")
                    func_row += "| - | - | - "
            
            func_row += "|"
            header.append(func_row)
        
        # Add a note about the metrics
        header.extend([
            "",
            "**Metrics Legend:**",
            "- **Total %**: Percentage of all reachable lines that were covered during verification.",
            "- **Func %**: Percentage of target function lines that were covered.",
            "- **Errors**: Number of verification errors or failures detected."
        ])
    
    # Add performance metrics
    header.extend([
        "",
        "## Performance Metrics",
        f"Average harness generation time: {avg_generation_time:.2f} seconds",
        f"Average verification time: {avg_verification_time:.2f} seconds",
        f"Average evaluation time: {avg_evaluation_time:.2f} seconds",
        "",
        "## Coverage Analysis",
        f"Coverage report available at: {os.path.join('coverage', 'coverage_report.html')}",
        "",
        "## Summary of Results"
    ])
    
    # Add results for each function
    for func_name in state.get("vulnerable_functions", []):
        if func_name in state.get("cbmc_results", {}):
            result = state.get("cbmc_results", {})[func_name]
            refinements = state.get("refinement_attempts", {}).get(func_name, 0)
            
            # Extract original function name and file if in directory mode
            display_name = func_name
            file_info = ""
            if ":" in func_name and is_directory_mode:
                file_name, orig_name = func_name.split(":", 1)
                display_name = orig_name
                file_info = f" (File: {file_name})"
            
            header.append(f"\n### Function: {display_name}{file_info}")
            header.append(f"Status: {result['status']}")
            header.append(f"Refinements: {refinements}")
            header.append(f"Message: {result['message']}")
            if result.get("suggestions"):
                header.append(f"Suggestions: {result['suggestions']}")
            
            # Add coverage metrics for this function if available
            if not coverage_df.is_empty():
                # Find latest version metrics for this function
                func_data = coverage_df.filter(pl.col("function") == func_name)
                if not func_data.is_empty():
                    max_version = func_data["version"].max()
                    func_metrics = func_data.filter(pl.col("version") == max_version).row(0, named=True)
                    
                    header.append(f"\n#### Coverage Metrics")
                    
                    # Handle different metric names and potential string values
                    for metric_name, display_name in [
                        ("total_reachable_lines", "Total reachable lines"),
                        ("total_covered_lines", "Total coverage"),
                        ("func_reachable_lines", "Function reachable lines"),
                        ("func_coverage_pct", "Function coverage"),
                        ("reported_errors", "Reported errors")
                    ]:
                        if metric_name in func_metrics:
                            metric_value = func_metrics[metric_name]
                            
                            # For reported_errors, also try alternative fields if this is zero or N/A
                            if metric_name == "reported_errors" and (metric_value == 0 or metric_value == "N/A"):
                                # Try failure_count
                                if "failure_count" in func_metrics:
                                    failure_val = func_metrics["failure_count"]
                                    if failure_val != 0 and failure_val != "N/A":
                                        metric_value = failure_val
                                
                                # Try error_count
                                if metric_value == 0 or metric_value == "N/A":
                                    if "error_count" in func_metrics:
                                        error_val = func_metrics["error_count"]
                                        if error_val != 0 and error_val != "N/A":
                                            metric_value = error_val
                            
                            # Format percentage values appropriately
                            if metric_name.endswith("_pct") and isinstance(metric_value, (int, float)):
                                header.append(f"- {display_name}: {metric_value:.2f}%")
                            else:
                                header.append(f"- {display_name}: {metric_value}")
                    
                    # Add evolution metrics if function has multiple versions
                    versions = func_data["version"].unique()
                    if len(versions) > 1:
                        first_version = versions.min()
                        first_metrics = func_data.filter(pl.col("version") == first_version).row(0, named=True)
                        
                        # Handle potential string values for coverage metrics
                        try:
                            initial_cov = float(first_metrics.get('func_coverage_pct', 0))
                            final_cov = float(func_metrics.get('func_coverage_pct', 0))
                            cov_improvement = final_cov - initial_cov
                            
                            # Get error values with fallbacks to alternative fields
                            initial_errors = 0
                            for field in ['reported_errors', 'failure_count', 'error_count']:
                                if field in first_metrics and first_metrics[field] != "N/A":
                                    try:
                                        if isinstance(first_metrics[field], str):
                                            initial_errors = int(float(first_metrics[field]))
                                        else:
                                            initial_errors = int(first_metrics[field])
                                        if initial_errors > 0:
                                            break
                                    except (ValueError, TypeError):
                                        pass
                            
                            final_errors = 0
                            for field in ['reported_errors', 'failure_count', 'error_count']:
                                if field in func_metrics and func_metrics[field] != "N/A":
                                    try:
                                        if isinstance(func_metrics[field], str):
                                            final_errors = int(float(func_metrics[field]))
                                        else:
                                            final_errors = int(func_metrics[field])
                                        if final_errors > 0:
                                            break
                                    except (ValueError, TypeError):
                                        pass
                            
                            error_reduction = initial_errors - final_errors
                            
                            header.append(f"\n#### Coverage Evolution")
                            header.append(f"- Initial coverage (v{first_version}): {initial_cov:.2f}%")
                            header.append(f"- Final coverage (v{max_version}): {final_cov:.2f}%")
                            header.append(f"- Coverage improvement: {cov_improvement:.2f}%")
                            header.append(f"- Error reduction: {error_reduction}")
                        except (ValueError, TypeError) as e:
                            logger.error(f"Error calculating coverage evolution: {str(e)}")
            
            # Add harness evolution information
            harness_history = state.get("harness_history", {}).get(func_name, [])
            if harness_history:
                header.append(f"\n#### Harness Evolution:")
                for i, _ in enumerate(harness_history):
                    header.append(f"  - Version {i+1}: {os.path.join(harnesses_dir, func_name, f'v{i+1}.c')}")
                
                # Add improvement metrics if there were multiple versions
                if len(harness_history) > 1:
                    # Compare first and last version
                    first_version = harness_history[0]
                    last_version = harness_history[-1]
                    
                    # Basic line count comparison
                    first_lines = len(first_version.split('\n'))
                    last_lines = len(last_version.split('\n'))
                    line_diff = last_lines - first_lines
                    
                    header.append(f"  - Size evolution: Initial {first_lines} lines → Final {last_lines} lines ({'+' if line_diff > 0 else ''}{line_diff} lines)")
                    
                    # Check if final version addressed verification issues
                    if result['status'] == 'SUCCESS':
                        header.append(f"  - Refinement result: Successfully addressed all verification issues")
                    else:
                        header.append(f"  - Refinement result: Some issues remain after {refinements} refinements")
            
            # List all verification reports with updated paths
            header.append(f"\n#### Verification Reports: ")
            for i in range(1, refinements + 2):  # +2 because initial version is 1, and we need to go one past the refinement count
                header.append(f"  - {os.path.join(verification_dir, func_name, f'v{i}_results.txt')}")
                header.append(f"  - {os.path.join(verification_dir, func_name, f'v{i}_report.md')}")
    
    final_summary = "\n".join(header)
    
    # Create the report file
    os.makedirs(reports_dir, exist_ok=True)
    
    # Save final report
    final_report_path = os.path.join(reports_dir, "final_report.md")
    with open(final_report_path, "w") as f:
        f.write(final_summary)
        f.flush()
        os.fsync(f.fileno())
    
    # Generate an HTML version of the report
    try:
        # Try to generate HTML report if markdown is available
        import markdown
        html_report_path = os.path.join(reports_dir, "final_report.html")
        with open(html_report_path, "w") as f:
            f.write("<html><head><title>CBMC Verification Report</title>")
            f.write("<style>body{font-family:Arial,sans-serif;line-height:1.6;max-width:900px;margin:0 auto;padding:20px}h1{color:#2c3e50}h2{color:#3498db}h3{color:#2980b9}pre{background:#f8f8f8;border:1px solid #ddd;padding:10px;overflow:auto;border-radius:3px}table{border-collapse:collapse;width:100%}table,th,td{border:1px solid #ddd;padding:8px}th{background-color:#f2f2f2}tr:nth-child(even){background-color:#f9f9f9}</style>")
            f.write("</head><body>")
            f.write(markdown.markdown(final_summary))
            f.write("</body></html>")
    except ImportError:
        # If markdown is not available, create a simple HTML version
        html_report_path = os.path.join(reports_dir, "final_report.html")
        with open(html_report_path, "w") as f:
            f.write("<html><head><title>CBMC Verification Report</title></head><body>")
            f.write("<pre>" + final_summary + "</pre>")
            f.write("</body></html>")
    
    # Generate index.html that links to all reports
    index_path = os.path.join(reports_dir, "coverage_report.html")
    with open(index_path, "w") as f:
        f.write("<html><head><title>CBMC Coverage and Error Table</title>")
        f.write("<style>body{font-family:Arial,sans-serif;line-height:1.6;max-width:900px;margin:0 auto;padding:20px}h1{color:#2c3e50}h2{color:#3498db}h3{color:#2980b9}table{border-collapse:collapse;width:100%}table,th,td{border:1px solid #ddd;padding:8px}th{background-color:#f2f2f2}tr:nth-child(even){background-color:#f9f9f9}a{color:#3498db;text-decoration:none}a:hover{text-decoration:underline}.info-box{background-color:#e8f4f8;border-left:5px solid #3498db;padding:15px;margin-bottom:20px}</style>")
        f.write("</head><body>")
        
        # Add explanation about the data sources
        f.write('<div class="info-box">')
        f.write('<h2>Coverage and Error Report</h2>')
        f.write('<p>This report combines data from two sources:</p>')
        f.write('<ul>')
        f.write('<li><strong>Coverage Metrics:</strong> Shows how much of the code was executed during verification</li>')
        f.write('<li><strong>Error Metrics:</strong> Tracks the number of errors detected in each version of the harness</li>')
        f.write('</ul>')
        f.write('<p>The "Errors" column shows the actual number of verification errors detected across all versions, enabling better tracking of error resolution progress.</p>')
        f.write('</div>')
        
        # Table of function reports with enhanced metrics
        f.write("<h2>Function Reports</h2>")
        f.write("<table>")
        f.write("<tr><th rowspan='2'>Function</th><th rowspan='2'>File</th><th rowspan='2'>Status</th>")
        
        # Add version column headers
        if not coverage_df.is_empty():
            versions = sorted(list(set(coverage_df["version"].to_list())))
            for version in versions:
                f.write(f"<th colspan='3'>Version {version}</th>")
            f.write("</tr><tr>")
            
            # Add subheaders for each version
            for _ in versions:
                f.write("<th>Total %</th><th>Func %</th><th>Errors</th>")
        
        f.write("</tr>")
        
        # Function to get color based on class name
        def get_color_for_class(class_name):
            """Return a color hex code based on the class name."""
            if class_name == "good":
                return "#00691c"  # Dark green
            elif class_name == "medium":
                return "#FFA500"  # Orange
            elif class_name == "poor":
                return "#d32f2f"  # Red
            else:
                return "#000000"  # Black
        
        # Process each function
        for func_name in state.get("vulnerable_functions", []):
            if func_name in state.get("cbmc_results", {}):
                result = state.get("cbmc_results", {})[func_name]
                refinements = state.get("refinement_attempts", {}).get(func_name, 0)
                
                # Extract original function name and file if in directory mode
                display_name = func_name
                file_name = ""
                if ":" in func_name:
                    file_name, display_name = func_name.split(":", 1)
                
                # Determine status color
                status_style = ""
                if result['status'] == "SUCCESS":
                    status_style = "style='color:green;font-weight:bold'"
                elif result['status'] == "FAILED":
                    status_style = "style='color:red;font-weight:bold'"
                elif result['status'] == "TIMEOUT":
                    status_style = "style='color:orange;font-weight:bold'"
                else:
                    status_style = "style='color:gray;font-weight:bold'"
                
                # Start the row
                f.write(f"<tr><td>{display_name}</td><td>{file_name}</td><td {status_style}>{result['status']}</td>")
                
                # Add coverage metrics for each version
                if not coverage_df.is_empty():
                    for version in versions:
                        # Get data for this function and version
                        try:
                            func_data = coverage_df.filter(
                                (pl.col("function") == func_name) & (pl.col("version") == version)
                            )
                            
                            if not func_data.is_empty():
                                metrics = func_data.row(0, named=True)
                                
                                # Process total coverage
                                total_cov_val = metrics.get("total_coverage_pct", "N/A")
                                if isinstance(total_cov_val, (int, float)):
                                    total_class = "good" if total_cov_val >= 80 else "medium" if total_cov_val >= 50 else "poor"
                                    f.write(f"<td style='color:{get_color_for_class(total_class)}'>{total_cov_val:.2f}%</td>")
                                else:
                                    f.write("<td>N/A</td>")
                                
                                # Process func coverage
                                func_cov_val = metrics.get("func_coverage_pct", "N/A")
                                if isinstance(func_cov_val, (int, float)):
                                    func_class = "good" if func_cov_val >= 80 else "medium" if func_cov_val >= 50 else "poor"
                                    f.write(f"<td style='color:{get_color_for_class(func_class)}'>{func_cov_val:.2f}%</td>")
                                else:
                                    f.write("<td>N/A</td>")
                                
                                # Process errors/failures - Get all error metrics
                                reported_errors = 0
                                failure_count = 0
                                error_count = 0
                                
                                # First try to get error data from error_df if available
                                if not error_df.is_empty():
                                    try:
                                        error_data = error_df.filter(
                                            (pl.col("function") == func_name) & (pl.col("version") == version)
                                        )
                                        if not error_data.is_empty():
                                            error_record = error_data.row(0, named=True)
                                            # Get error count from error metrics
                                            if "error_count" in error_record and error_record["error_count"] != "N/A":
                                                try:
                                                    if isinstance(error_record["error_count"], str):
                                                        error_count = int(float(error_record["error_count"]))
                                                    else:
                                                        error_count = int(error_record["error_count"])
                                                except (ValueError, TypeError):
                                                    pass
                                            
                                            # Get reported errors from error metrics
                                            if "reported_errors" in error_record and error_record["reported_errors"] != "N/A":
                                                try:
                                                    if isinstance(error_record["reported_errors"], str):
                                                        reported_errors = int(float(error_record["reported_errors"]))
                                                    else:
                                                        reported_errors = int(error_record["reported_errors"])
                                                except (ValueError, TypeError):
                                                    pass
                                                    
                                            # Get failure count from error metrics
                                            if "failure_count" in error_record and error_record["failure_count"] != "N/A":
                                                try:
                                                    if isinstance(error_record["failure_count"], str):
                                                        failure_count = int(float(error_record["failure_count"]))
                                                    else:
                                                        failure_count = int(error_record["failure_count"])
                                                except (ValueError, TypeError):
                                                    pass
                                    except Exception as e:
                                        logger.error(f"Error processing error data for HTML: {str(e)}")
                                
                                # Fallback to coverage metrics if error data not available or incomplete
                                if reported_errors == 0 and "reported_errors" in metrics and metrics["reported_errors"] != "N/A":
                                    try:
                                        if isinstance(metrics["reported_errors"], str):
                                            reported_errors = int(float(metrics["reported_errors"]))
                                        else:
                                            reported_errors = int(metrics["reported_errors"])
                                    except (ValueError, TypeError):
                                        pass
                                
                                if failure_count == 0 and "failure_count" in metrics and metrics["failure_count"] != "N/A":
                                    try:
                                        if isinstance(metrics["failure_count"], str):
                                            failure_count = int(float(metrics["failure_count"]))
                                        else:
                                            failure_count = int(metrics["failure_count"])
                                    except (ValueError, TypeError):
                                        pass
                                
                                if error_count == 0 and "error_count" in metrics and metrics["error_count"] != "N/A":
                                    try:
                                        if isinstance(metrics["error_count"], str):
                                            error_count = int(float(metrics["error_count"]))
                                        else:
                                            error_count = int(metrics["error_count"])
                                    except (ValueError, TypeError):
                                        pass
                                
                                # Use the highest non-zero value for display
                                error_val = max(reported_errors, failure_count, error_count)
                                
                                # Color code the errors - green for 0, red for any errors
                                error_class = "good" if error_val == 0 else "poor"
                                f.write(f"<td style='color:{get_color_for_class(error_class)}'>{error_val}</td>")
                            else:
                                f.write("<td>-</td><td>-</td><td>-</td>")
                        except Exception as e:
                            logger.error(f"Error formatting HTML metrics for {func_name}, version {version}: {str(e)}")
                            f.write("<td>-</td><td>-</td><td>-</td>")
                
                f.write("</tr>")
        
        f.write("</table>")
        f.write("</body></html>")
    
    # Calculate relative path for displaying in message
    result_path = os.path.relpath(result_base_dir)
    coverage_path = os.path.join(result_path, "coverage", "coverage_report.html")
    
    return {
        "messages": [AIMessage(content=f"Analysis complete! Reports generated in '{result_path}'. Main index at {os.path.join(result_path, 'reports', 'index.html')}. Coverage report at {coverage_path}")]
    }