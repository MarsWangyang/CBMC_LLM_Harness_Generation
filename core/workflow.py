"""
LangGraph workflow setup for CBMC harness generator.
"""
from langgraph.graph import StateGraph, START, END

from core.state import HarnessGenerationState
from nodes.frontend import frontend_node
from nodes.code_embedding import code_embedding_node
from nodes.analyzer import analyzer_node
from nodes.junction import junction_node, route_from_junction
from nodes.generator import generator_node, route_from_generator
from nodes.cbmc import cbmc_node, route_from_cbmc
from nodes.evaluator import harness_evaluator_node, route_from_evaluator
from nodes.output import output_node

def create_workflow():
    """
    Creates and returns the LangGraph workflow for the CBMC harness generator.
    """
    # Build the graph
    workflow = StateGraph(HarnessGenerationState)

    # Add nodes
    workflow.add_node("frontend", frontend_node)
    workflow.add_node("code_embedding", code_embedding_node)
    workflow.add_node("analyzer", analyzer_node)
    workflow.add_node("junction", junction_node)
    workflow.add_node("generator", generator_node)
    workflow.add_node("cbmc", cbmc_node)
    workflow.add_node("evaluator", harness_evaluator_node)
    workflow.add_node("output", output_node)

    # Connect the nodes with the main flow
    workflow.add_edge(START, "frontend")
    workflow.add_edge("frontend", "code_embedding")
    workflow.add_edge("code_embedding", "analyzer") 
    workflow.add_edge("analyzer", "junction")

    # Add conditional routing based on next state
    workflow.add_conditional_edges(
        "junction",
        route_from_junction,
        {
            "generator": "generator",
            "output": "output"
        }
    )

    workflow.add_conditional_edges(
        "generator",
        route_from_generator,
        {
            "cbmc": "cbmc",
            "junction": "junction"
        }
    )

    # Route from CBMC to Evaluator
    workflow.add_conditional_edges(
        "cbmc",
        route_from_cbmc,
        {
            "evaluator": "evaluator"
        }
    )

    # Route from Evaluator to either Generator (for refinement) or Junction (for next function)
    workflow.add_conditional_edges(
        "evaluator",
        route_from_evaluator,
        {
            "generator": "generator",  # For harness refinement
            "junction": "junction"     # For next function
        }
    )

    workflow.add_edge("output", END)

    # Compile the graph
    return workflow.compile()