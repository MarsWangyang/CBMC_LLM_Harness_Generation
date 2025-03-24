"""
Output node for CBMC harness generator workflow.
"""
import os
import time
from langchain_core.messages import AIMessage

def output_node(state):
    """Provides final summary of all processed functions with performance metrics and generates an index report."""
    total_time = time.time() - state.get("start_time", time.time())
    
    # Determine if we're in directory mode
    is_directory_mode = state.get("is_directory_mode", False)
    
    # Calculate summary statistics
    function_times = state.get("function_times", {})
    total_refinements = sum(state.get("refinement_attempts", {}).values())
    
    # Create performance metrics
    if function_times:
        avg_generation_time = sum(times.get("generation", 0) for times in function_times.values()) / len(function_times)
        avg_verification_time = sum(times.get("verification", 0) for times in function_times.values()) / len(function_times)
        avg_evaluation_time = sum(times.get("evaluation", 0) for times in function_times.values()) / len(function_times)
        avg_refinements = total_refinements / len(state.get("refinement_attempts", {})) if state.get("refinement_attempts", {}) else 0
    else:
        avg_generation_time = avg_verification_time = avg_evaluation_time = avg_refinements = 0
    
    # Create a header based on mode
    if is_directory_mode:
        source_files = state.get("source_files", {})
        header = [
            "# CBMC Harness Generation Complete - Directory Mode",
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
            "# CBMC Harness Generation Complete",
            "",
            f"Total processing time: {total_time:.2f} seconds",
            f"Analyzed {len(state.get('embeddings', {}).get('functions', {}))} functions.",
            f"Identified {len(state.get('vulnerable_functions', []))} functions with memory or arithmetic operations.",
            f"Generated {len(state.get('harnesses', {}))} verification harnesses.",
            f"Performed {total_refinements} harness refinements (average {avg_refinements:.2f} per function).",
        ]
    
    # Add performance metrics
    header.extend([
        "",
        "## Performance Metrics",
        f"Average harness generation time: {avg_generation_time:.2f} seconds",
        f"Average verification time: {avg_verification_time:.2f} seconds",
        f"Average evaluation time: {avg_evaluation_time:.2f} seconds",
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
            
            # Add harness evolution information
            harness_history = state.get("harness_history", {}).get(func_name, [])
            if harness_history:
                header.append(f"Harness Evolution:")
                for i, _ in enumerate(harness_history):
                    header.append(f"  - Version {i+1}: harnesses/{func_name}/v{i+1}.c")
                
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
            
            # List all verification reports
            header.append(f"Verification Reports: ")
            for i in range(1, refinements + 2):  # +2 because initial version is 1, and we need to go one past the refinement count
                header.append(f"  - verification/{func_name}/v{i}_results.txt")
                header.append(f"  - verification/{func_name}/v{i}_report.md")
    
    final_summary = "\n".join(header)
    
    # Create a main index report file
    report_dir = "reports"
    os.makedirs(report_dir, exist_ok=True)
    
    # Save final report
    with open(f"{report_dir}/final_report.md", "w") as f:
        f.write(final_summary)
        f.flush()
        os.fsync(f.fileno())
    
    # Generate an HTML version of the report
    try:
        # Try to generate HTML report if markdown is available
        import markdown
        with open(f"{report_dir}/final_report.html", "w") as f:
            f.write("<html><head><title>CBMC Verification Report</title>")
            f.write("<style>body{font-family:Arial,sans-serif;line-height:1.6;max-width:900px;margin:0 auto;padding:20px}h1{color:#2c3e50}h2{color:#3498db}h3{color:#2980b9}pre{background:#f8f8f8;border:1px solid #ddd;padding:10px;overflow:auto;border-radius:3px}table{border-collapse:collapse;width:100%}table,th,td{border:1px solid #ddd;padding:8px}th{background-color:#f2f2f2}tr:nth-child(even){background-color:#f9f9f9}</style>")
            f.write("</head><body>")
            f.write(markdown.markdown(final_summary))
            f.write("</body></html>")
    except ImportError:
        # If markdown is not available, create a simple HTML version
        with open(f"{report_dir}/final_report.html", "w") as f:
            f.write("<html><head><title>CBMC Verification Report</title></head><body>")
            f.write("<pre>" + final_summary + "</pre>")
            f.write("</body></html>")
    
    # Generate index.html that links to all reports
    with open(f"{report_dir}/index.html", "w") as f:
        f.write("<html><head><title>CBMC Verification Index</title>")
        f.write("<style>body{font-family:Arial,sans-serif;line-height:1.6;max-width:900px;margin:0 auto;padding:20px}h1{color:#2c3e50}h2{color:#3498db}h3{color:#2980b9}table{border-collapse:collapse;width:100%}table,th,td{border:1px solid #ddd;padding:8px}th{background-color:#f2f2f2}tr:nth-child(even){background-color:#f9f9f9}a{color:#3498db;text-decoration:none}a:hover{text-decoration:underline}</style>")
        f.write("</head><body>")
        f.write("<h1>CBMC Verification Reports</h1>")
        f.write("<p>This index provides links to all verification reports generated.</p>")
        
        # Link to final report
        f.write("<h2>Final Summary Report</h2>")
        f.write("<p><a href='final_report.html'>View Complete Summary Report</a></p>")
        
        # Table of function reports
        f.write("<h2>Function Reports</h2>")
        f.write("<table>")
        f.write("<tr><th>Function</th><th>File</th><th>Status</th><th>Versions</th><th>Reports</th></tr>")
        
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
                
                # Get version count
                version_count = len(state.get("harness_history", {}).get(func_name, [])) or refinements + 1
                
                f.write(f"<tr><td>{display_name}</td><td>{file_name}</td><td {status_style}>{result['status']}</td>")
                
                # Add links to all harness versions 
                f.write("<td>")
                for i in range(1, version_count + 1):
                    f.write(f"<a href='../harnesses/{func_name}/v{i}.c'>v{i}</a> ")
                f.write("</td>")
                
                # Add links to all version reports
                f.write("<td>")
                for i in range(1, refinements + 2):
                    f.write(f"<a href='../verification/{func_name}/v{i}_report.md'>v{i}</a> ")
                f.write("</td></tr>")
        
        f.write("</table>")
        
        # Add evolution section if any functions have multiple versions
        evolution_data = [func for func in state.get("vulnerable_functions", []) 
                         if len(state.get("harness_history", {}).get(func, [])) > 1]
        
        if evolution_data:
            f.write("<h2>Harness Evolution</h2>")
            f.write("<p>The following functions underwent multiple iterations of refinement:</p>")
            
            f.write("<table>")
            f.write("<tr><th>Function</th><th>Versions</th><th>Final Status</th><th>Line Count Evolution</th></tr>")
            
            for func_name in evolution_data:
                history = state.get("harness_history", {}).get(func_name, [])
                versions = len(history)
                status = state.get("cbmc_results", {}).get(func_name, {}).get("status", "UNKNOWN")
                
                # Calculate line count evolution
                if len(history) > 1:
                    first_lines = len(history[0].split('\n'))
                    last_lines = len(history[-1].split('\n'))
                    line_diff = last_lines - first_lines
                    line_evolution = f"{first_lines} → {last_lines} ({'+' if line_diff > 0 else ''}{line_diff})"
                else:
                    line_evolution = "N/A"
                
                # Determine status color
                status_style = ""
                if status == "SUCCESS":
                    status_style = "style='color:green;font-weight:bold'"
                elif status == "FAILED":
                    status_style = "style='color:red;font-weight:bold'"
                elif status == "TIMEOUT":
                    status_style = "style='color:orange;font-weight:bold'"
                else:
                    status_style = "style='color:gray;font-weight:bold'"
                
                # Extract display name
                display_name = func_name
                if ":" in func_name:
                    _, display_name = func_name.split(":", 1)
                
                f.write(f"<tr><td>{display_name}</td><td>{versions}</td>")
                f.write(f"<td {status_style}>{status}</td><td>{line_evolution}</td></tr>")
            
            f.write("</table>")
        
        f.write("</body></html>")
    
    return {
        "messages": [AIMessage(content=f"Analysis complete! Reports generated in the 'reports' directory. View the main index at reports/index.html")]
    }