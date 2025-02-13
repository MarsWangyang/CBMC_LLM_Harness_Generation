import os
import langchain, langgraph, openai
from langchain_openai import ChatOpenAI
from langgraph.graph import StateGraph, MessagesState, START

from langgraph.types import Command
from langchain_core.messages import convert_to_messages
import config
import utils
from typing_extensions import Literal


os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_KEY")
source = utils.read_c_file("test/1.c")




generator_llm = ChatOpenAI(model = "gpt-4", temperature = 0.7)
critic_llm = ChatOpenAI(model="gpt-4", temperature = 0)




def generator(state: MessagesState) -> Command[Literal["critic", "__end__"]]:
    system_prompt = (
        "You are a helpful software engineer assistor, specialized in generating CBMC harnesses for potentially faulty C/C++ code."
        "Request feedback on generation quality, ask 'critic'."
    )
    print("--------------------------ENTER GENERATOR------------------------------")
    print(state)
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = generator_llm.invoke(messages)
    header = "\n\n_____________________________________________ GENERATOR MODEL _____________________________________________\n"
    utils.write_to_log(header + ai_msg.content)
    print("--------------------------LEAVE GENERATOR------------------------------")
    return Command(
        goto="critic", 
        update={"messages": [ai_msg.content]}
        )


    # If the expert has an answer, return it directly to the user
    #return {"messages": [ai_msg]}


def critic(state: MessagesState) -> Command[Literal["generator", "__end__"]]:
    system_prompt = (
        "You are a harsh critic that seeks to ensure a proper CBMC harness is generated for the given C/C++ code, evaluate the given harness and provide feedback. Only critic, don't generate your idea of the solution."
        "If you think the harness could be improved, ask 'generator' for help."
    )
    print("--------------------------ENTER CRITIC------------------------------")
    print(state["messages"])
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = critic_llm.invoke(messages)
    header = "\n\n_____________________________________________ CRITIC MODEL _____________________________________________\n"
    utils.write_to_log(header + ai_msg.content)
    print("--------------------------LEAVE CRITIC------------------------------")
    return Command(
        goto="generator", 
        update={"messages": [ai_msg.content]}
        )

    # If the expert has an answer, return it directly to the user
    #return {"messages": [ai_msg]}


builder = StateGraph(MessagesState)
builder.add_node("generator", generator)
builder.add_node("critic", critic)
# we'll always start with a general travel advisor
builder.add_edge(START, "generator")


graph = builder.compile()



for chunk in graph.stream({"messages": [("user", source)]}):

    #add count for token
    print("---------------------------------------------------------------------------------------------------------------")