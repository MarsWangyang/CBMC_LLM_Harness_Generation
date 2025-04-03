"""
Enhanced metrics tracking utilities using Polars DataFrame for the CBMC harness generator.
"""
import os
import polars as pl
import logging
from datetime import datetime

logger = logging.getLogger("metrics_utils")

class MetricsTracker:
    """Class for tracking verification metrics across iterations for all functions."""
    
    def __init__(self, output_dir="results"):
        """Initialize the metrics tracker with empty DataFrames."""
        self.output_dir = output_dir
        
        # Main DataFrame for tracking metrics across iterations and functions
        self.metrics_df = pl.DataFrame(schema={
            "function": pl.String,
            "iteration": pl.Int64,  # Changed from Int32 to Int64
            "timestamp": pl.Datetime,
            "status": pl.String,
            "reachable_lines": pl.Int64,  # Changed from Int32 to Int64
            "covered_lines": pl.Int64,    # Changed from Int32 to Int64
            "coverage_pct": pl.Float64,
            "errors": pl.Int64,           # Changed from Int32 to Int64
            "has_memory_leak": pl.Boolean,
            "has_array_bounds": pl.Boolean,
            "has_pointer_issue": pl.Boolean,
            "has_arithmetic_issue": pl.Boolean,
            "runtime_ms": pl.Int64
        })
        
        # NEW: Add enhanced metrics tracking
        self.detailed_metrics_df = pl.DataFrame(schema={
            "function": pl.String,
            "iteration": pl.Int64,
            "timestamp": pl.Datetime,
            "status": pl.String,
            "total_reachable_lines": pl.Int64,
            "total_covered_lines": pl.Int64, 
            "total_coverage_pct": pl.Float64,
            "func_reachable_lines": pl.Int64,
            "func_covered_lines": pl.Int64,
            "func_coverage_pct": pl.Float64,
            "reported_errors": pl.Int64,
            "error_categories": pl.String,
            "runtime_ms": pl.Int64
        })
        
        # Summary DataFrame for final results
        self.summary_df = None
        
        logger.info("Initialized metrics tracker")
    
    def add_function_metrics(self, func_name, iteration, metrics, runtime_ms):
        """
        Add metrics for a specific function and iteration.
        
        Args:
            func_name: Name of the function
            iteration: Iteration number (starting from 1)
            metrics: Dictionary containing the metrics
            runtime_ms: Runtime in milliseconds
        """
        try:
            # Ensure all integer values are Int64
            iteration = int(iteration)  # Make sure it's an integer
            runtime_ms = int(runtime_ms)  # Make sure it's an integer
            
            # Extract metrics with default values for missing keys
            status = metrics.get("verification_status", "UNKNOWN")
            reachable_lines = int(metrics.get("reachable_lines", 0))
            covered_lines = int(metrics.get("covered_lines", 0))
            coverage_pct = float(metrics.get("coverage_pct", 0.0))
            errors = int(metrics.get("errors", 0))
            
            # Extract error categories
            error_categories = metrics.get("error_categories", [])
            has_memory_leak = "memory_leak" in error_categories
            has_array_bounds = "array_bounds" in error_categories
            has_pointer_issue = "null_pointer" in error_categories or "pointer_overflow" in error_categories
            has_arithmetic_issue = "division_by_zero" in error_categories or "arithmetic_overflow" in error_categories
            
            # Create new row with explicit types
            new_row = pl.DataFrame([{
                "function": str(func_name),
                "iteration": iteration,
                "timestamp": datetime.now(),
                "status": str(status),
                "reachable_lines": reachable_lines,
                "covered_lines": covered_lines,
                "coverage_pct": coverage_pct,
                "errors": errors,
                "has_memory_leak": bool(has_memory_leak),
                "has_array_bounds": bool(has_array_bounds),
                "has_pointer_issue": bool(has_pointer_issue),
                "has_arithmetic_issue": bool(has_arithmetic_issue),
                "runtime_ms": runtime_ms
            }])
            
            # NEW: Create detailed metrics row with function-specific metrics
            detailed_row = pl.DataFrame([{
                "function": str(func_name),
                "iteration": iteration,
                "timestamp": datetime.now(),
                "status": str(status),
                "total_reachable_lines": int(metrics.get("reachable_lines", 0)),
                "total_covered_lines": int(metrics.get("covered_lines", 0)),
                "total_coverage_pct": float(metrics.get("coverage_pct", 0.0)),
                "func_reachable_lines": int(metrics.get("func_reachable_lines", 0)),
                "func_covered_lines": int(metrics.get("func_covered_lines", 0)),
                "func_coverage_pct": float(metrics.get("func_coverage_pct", 0.0)),
                "reported_errors": int(metrics.get("errors", 0)),
                "error_categories": str(error_categories),
                "runtime_ms": runtime_ms
            }])
            
            # Append to main DataFrame
            self.metrics_df = pl.concat([self.metrics_df, new_row])
            
            # NEW: Append to detailed metrics DataFrame
            self.detailed_metrics_df = pl.concat([self.detailed_metrics_df, detailed_row])
            
            logger.debug(f"Added metrics for {func_name} iteration {iteration}")
            
        except Exception as e:
            logger.error(f"Error adding metrics for {func_name}: {str(e)}")
            # Continue without adding metrics rather than crashing the entire process
            logger.warning(f"Continuing without adding metrics for {func_name}")
    
    def generate_summary(self):
        """Generate a summary DataFrame with the final metrics for each function."""
        if len(self.metrics_df) == 0:
            logger.warning("No metrics data available to generate summary")
            return pl.DataFrame()
        
        try:
            # Get the latest iteration for each function
            latest_iterations = (
                self.metrics_df
                .groupby("function")
                .agg(pl.max("iteration").alias("max_iteration"))
            )
            
            # Join with main DataFrame to get final metrics
            self.summary_df = (
                latest_iterations
                .join(self.metrics_df, left_on=["function", "max_iteration"], right_on=["function", "iteration"])
                .select([
                    "function", 
                    "max_iteration", 
                    "status", 
                    "coverage_pct", 
                    "errors",
                    "has_memory_leak",
                    "has_array_bounds",
                    "has_pointer_issue",
                    "has_arithmetic_issue"
                ])
                .sort("function")
            )
            
            # NEW: Generate detailed summary
            if len(self.detailed_metrics_df) > 0:
                latest_detailed = (
                    self.detailed_metrics_df
                    .groupby("function")
                    .agg(pl.max("iteration").alias("max_iteration"))
                )
                
                self.detailed_summary_df = (
                    latest_detailed
                    .join(
                        self.detailed_metrics_df, 
                        left_on=["function", "max_iteration"], 
                        right_on=["function", "iteration"]
                    )
                    .select([
                        "function",
                        "max_iteration",
                        "status",
                        "total_covered_lines",
                        "total_coverage_pct",
                        "func_reachable_lines",
                        "func_covered_lines", 
                        "func_coverage_pct",
                        "reported_errors",
                        "error_categories"
                    ])
                    .sort("function")
                )
            
            return self.summary_df
        except Exception as e:
            logger.error(f"Error generating summary: {str(e)}")
            # Return empty DataFrame on error
            return pl.DataFrame()
    
    def export_to_csv(self, prefix="metrics"):
        """Export metrics to CSV files."""
        if not os.path.exists(self.output_dir):
            os.makedirs(self.output_dir)
        
        try:
            # Export full metrics
            metrics_path = os.path.join(self.output_dir, f"{prefix}_full.csv")
            self.metrics_df.write_csv(metrics_path)
            logger.info(f"Exported full metrics to {metrics_path}")
            
            # NEW: Export detailed metrics
            if len(self.detailed_metrics_df) > 0:
                detailed_path = os.path.join(self.output_dir, f"{prefix}_detailed.csv")
                self.detailed_metrics_df.write_csv(detailed_path)
                logger.info(f"Exported detailed metrics to {detailed_path}")
            
            # Export summary if available
            if self.summary_df is None:
                self.generate_summary()
                
            if len(self.summary_df) > 0:
                summary_path = os.path.join(self.output_dir, f"{prefix}_summary.csv")
                self.summary_df.write_csv(summary_path)
                logger.info(f"Exported summary metrics to {summary_path}")
                
                # NEW: Export detailed summary
                if hasattr(self, 'detailed_summary_df') and len(self.detailed_summary_df) > 0:
                    detailed_summary_path = os.path.join(self.output_dir, f"{prefix}_detailed_summary.csv")
                    self.detailed_summary_df.write_csv(detailed_summary_path)
                    logger.info(f"Exported detailed summary metrics to {detailed_summary_path}")
        except Exception as e:
            logger.error(f"Error exporting metrics to CSV: {str(e)}")
    
    def export_to_excel(self, filename="metrics.xlsx"):
        """Export metrics to Excel file with multiple sheets and enhanced visualizations."""
        if not os.path.exists(self.output_dir):
            os.makedirs(self.output_dir)
            
        excel_path = os.path.join(self.output_dir, filename)
        
        try:
            # Ensure we have a summary
            if self.summary_df is None:
                self.generate_summary()
            
            # Check if we have data
            if len(self.metrics_df) == 0:
                logger.warning("No metrics data available to export to Excel")
                return
            
            # Try to use pandas for Excel export
            try:
                import pandas as pd
                
                # Convert to pandas for Excel export (polars excel export is experimental)
                metrics_pd = self.metrics_df.to_pandas()
                
                # NEW: Convert detailed metrics
                if len(self.detailed_metrics_df) > 0:
                    detailed_pd = self.detailed_metrics_df.to_pandas()
                else:
                    detailed_pd = None
                
                # Create pivot table of coverage by function and iteration
                pivot_coverage = (
                    self.metrics_df
                    .pivot(
                        index="function",
                        columns="iteration",
                        values="coverage_pct",
                        aggregate_function="last"
                    )
                    .to_pandas()
                )
                
                pivot_errors = (
                    self.metrics_df
                    .pivot(
                        index="function",
                        columns="iteration",
                        values="errors",
                        aggregate_function="last"
                    )
                    .to_pandas()
                )
                
                # NEW: Create unit proof metric pivots
                if len(self.detailed_metrics_df) > 0:
                    # Total lines pivot
                    pivot_total_reachable = (
                        self.detailed_metrics_df
                        .pivot(
                            index="function",
                            columns="iteration",
                            values="total_reachable_lines",
                            aggregate_function="last"
                        )
                        .to_pandas()
                    )
                    
                    # Total coverage pivot
                    pivot_total_coverage = (
                        self.detailed_metrics_df
                        .pivot(
                            index="function",
                            columns="iteration",
                            values="total_coverage_pct",
                            aggregate_function="last"
                        )
                        .to_pandas()
                    )
                    
                    # Function reachable lines pivot
                    pivot_func_reachable = (
                        self.detailed_metrics_df
                        .pivot(
                            index="function",
                            columns="iteration",
                            values="func_reachable_lines",
                            aggregate_function="last"
                        )
                        .to_pandas()
                    )
                    
                    # Function coverage pivot
                    pivot_func_coverage = (
                        self.detailed_metrics_df
                        .pivot(
                            index="function",
                            columns="iteration",
                            values="func_coverage_pct",
                            aggregate_function="last"
                        )
                        .to_pandas()
                    )
                else:
                    pivot_total_reachable = None
                    pivot_total_coverage = None
                    pivot_func_reachable = None
                    pivot_func_coverage = None
                
                summary_pd = self.summary_df.to_pandas() if len(self.summary_df) > 0 else None
                
                # NEW: Convert detailed summary
                if hasattr(self, 'detailed_summary_df') and len(self.detailed_summary_df) > 0:
                    detailed_summary_pd = self.detailed_summary_df.to_pandas()
                else:
                    detailed_summary_pd = None
                
                # Export to Excel
                with pd.ExcelWriter(excel_path) as writer:
                    # Main metrics sheets
                    metrics_pd.to_excel(writer, sheet_name="Full Metrics", index=False)
                    if summary_pd is not None:
                        summary_pd.to_excel(writer, sheet_name="Summary", index=False)
                    
                    # Standard pivots
                    pivot_coverage.to_excel(writer, sheet_name="Coverage by Iteration")
                    pivot_errors.to_excel(writer, sheet_name="Errors by Iteration")
                    
                    # NEW: Add detailed metrics sheets
                    if detailed_pd is not None:
                        detailed_pd.to_excel(writer, sheet_name="Detailed Metrics", index=False)
                    
                    if detailed_summary_pd is not None:
                        detailed_summary_pd.to_excel(writer, sheet_name="Detailed Summary", index=False)
                    
                    # NEW: Add unit proof metric sheets
                    if pivot_total_reachable is not None:
                        pivot_total_reachable.to_excel(writer, sheet_name="Total Reachable Lines")
                    
                    if pivot_total_coverage is not None:
                        pivot_total_coverage.to_excel(writer, sheet_name="Total Coverage %")
                    
                    if pivot_func_reachable is not None:
                        pivot_func_reachable.to_excel(writer, sheet_name="Function Reachable Lines")
                    
                    if pivot_func_coverage is not None:
                        pivot_func_coverage.to_excel(writer, sheet_name="Function Coverage %")
                    
                    # NEW: Add consolidated unit proof metrics sheet
                    if detailed_summary_pd is not None:
                        # Create a special summary with just the requested metrics
                        unit_proof_metrics = detailed_summary_pd[
                            ['function', 'total_reachable_lines', 'total_coverage_pct', 
                             'func_reachable_lines', 'func_coverage_pct', 'reported_errors']
                        ]
                        unit_proof_metrics.to_excel(writer, sheet_name="Unit Proof Metrics", index=False)
                
                logger.info(f"Exported metrics to Excel: {excel_path}")
                
            except ImportError:
                # Fall back to just exporting CSVs if pandas is not available
                logger.warning("Pandas not available, falling back to CSV export")
                self.export_to_csv()
                
        except Exception as e:
            logger.error(f"Error exporting to Excel: {str(e)}")
            # Fallback to CSV
            try:
                self.export_to_csv()
            except:
                logger.error("Unable to export metrics in any format")

# Create global instance
metrics_tracker = MetricsTracker()

def get_metrics_tracker():
    """Get the global metrics tracker instance."""
    return metrics_tracker

def initialize_metrics_tracker(output_dir):
    """Initialize the global metrics tracker with the specified output directory."""
    global metrics_tracker
    metrics_tracker = MetricsTracker(output_dir)
    return metrics_tracker