import os
import langchain, langgraph, openai
from langchain_openai import ChatOpenAI
from langgraph.graph import StateGraph, MessagesState, START

from langchain_core.messages import AnyMessage
from langgraph.prebuilt import create_react_agent
from langgraph.types import Command
from langchain_core.messages import convert_to_messages
import config
import utils



os.environ["OPENAI_API_KEY"] = config.OPENAI_KEY
source = utils.read_c_file("test/1.c")

from typing_extensions import Literal



generator_llm = ChatOpenAI(model = "gpt-4", temperature = 0.7)
critic_llm = ChatOpenAI(model="gpt-4", temperature = 0)


# Define a helper for each of the agent nodes to call

def transfer_to_generator():
    return

def transfer_to_critic():
    return


def generator(
    state: MessagesState,
) -> Command[Literal["critic", "__end__"]]:
    system_prompt = (
        "You are a helpful software engineer assistor, specialized in generating CBMC harnesses for potentially faulty C/C++ code."
        "Request feedback on generation quality, ask 'critic'."
    )
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = generator_llm.bind_tools([transfer_to_critic]).invoke(messages)
    # If there are tool calls, the LLM needs to hand off to another agent
    if len(ai_msg.tool_calls) > 0:
        tool_call_id = ai_msg.tool_calls[-1]["id"]
        # NOTE: it's important to insert a tool message here because LLM providers are expecting
        # all AI messages to be followed by a corresponding tool result message
        tool_msg = {
            "role": "tool",
            "content": "Successfully transferred",
            "tool_call_id": tool_call_id,
        }
        print("generator to critic")
        return Command(goto="critic", update={"messages": [ai_msg, tool_msg]})


    # If the expert has an answer, return it directly to the user
    return {"messages": [ai_msg]}


def critic(
    state: MessagesState,
) -> Command[Literal["generator", "__end__"]]:
    system_prompt = (
        "You are a harsh critic that seeks to ensure a proper CBMC harness is generated for the given C/C++ code, evaluate the given harness and provide feedback."
        "If you think the harness could be improved, ask 'generator' for help."
    )
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = critic_llm.bind_tools([transfer_to_generator]).invoke(messages)
    # If there are tool calls, the LLM needs to hand off to another agent
    if len(ai_msg.tool_calls) > 0:
        tool_call_id = ai_msg.tool_calls[-1]["id"]
        # NOTE: it's important to insert a tool message here because LLM providers are expecting
        # all AI messages to be followed by a corresponding tool result message
        tool_msg = {
            "role": "tool",
            "content": "Successfully transferred",
            "tool_call_id": tool_call_id,
        }
        print("critic to generator")
        return Command(goto="generator", update={"messages": [ai_msg, tool_msg]})

    # If the expert has an answer, return it directly to the user
    return {"messages": [ai_msg]}


builder = StateGraph(MessagesState)
builder.add_node("generator", generator)
builder.add_node("critic", critic)
# we'll always start with a general travel advisor
builder.add_edge(START, "generator")

graph = builder.compile()

def pretty_print_messages(update):
    if isinstance(update, tuple):
        ns, update = update
        # skip parent graph updates in the printouts
        if len(ns) == 0:
            return

        graph_id = ns[-1].split(":")[0]
        print(f"Update from subgraph {graph_id}:")
        print("\n")

    for node_name, node_update in update.items():
        print(f"Update from node {node_name}:")
        print("\n")

        for m in convert_to_messages(node_update["messages"]):
            m.pretty_print()
        print("\n")

for chunk in graph.stream({"messages": [("user", source)]}):
    print(chunk)
    print("---------------------------------------------------------------------------------------------------------------")