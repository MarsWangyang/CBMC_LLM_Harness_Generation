import os
import langchain, langgraph, openai
from langchain_openai import ChatOpenAI
from langgraph.graph import StateGraph, MessagesState, START, END

from langgraph.types import Command
from langchain_core.messages import convert_to_messages
import config
import utils
from typing_extensions import Literal


os.environ["OPENAI_API_KEY"] = os.getenv("OPENAI_KEY")
source = utils.read_c_file("test/1.c")




generator_llm = ChatOpenAI(model = "gpt-4", temperature = 0.7)
critic_llm = ChatOpenAI(model="gpt-4", temperature = 0)

utils.clear_log()


def generator(state: MessagesState) -> Command[Literal["critic", "__end__"]]:
    system_prompt = (
        '''You are a helpful software engineer assistor, specialized in generating CBMC harnesses for potentially faulty C/C++ code.'''
    )
    print(f"--------------------------ENTER GENERATOR {int(len(state['messages'])/2+1)}------------------------------")
    print(state["messages"])
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = generator_llm.invoke(messages)
    header = f"\n\n_____________________________________________ GENERATOR MODEL {int(len(state['messages'])/2+1)} _____________________________________________\n"
    utils.write_to_log(header + ai_msg.content)
    print("--------------------------LEAVE GENERATOR------------------------------")
    return Command(
        goto="critic", 
        update={"messages": [ai_msg.content]}
        )

def critic(state: MessagesState) -> Command[Literal["generator", "__end__"]]:
    system_prompt = (
        '''You are a harsh critic that seeks to ensure a proper CBMC harness is generated for the given C/C++ code, evaluate the 
        given harness and provide feedback. Only critic, don't generate your idea of the solution. If you are satisfied with the 
        generation or believe it can do its job, respond with "FINISH".'''
    )
    print(f"--------------------------ENTER CRITIC {int(len(state['messages'])/2)}------------------------------")
    print(state["messages"])
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = critic_llm.invoke(messages)
    header = f"\n\n_____________________________________________ CRITIC MODEL {int(len(state['messages'])/2)}_____________________________________________\n"
    utils.write_to_log(header + ai_msg.content)
    print("--------------------------LEAVE CRITIC------------------------------")
    if "FINISH" in ai_msg.content:
        return Command(
            goto= END,
            update={"messages": [ai_msg.content]}
        )
    return Command(
        goto="generator", 
        update={"messages": [ai_msg.content]}
        )



builder = StateGraph(MessagesState)

builder.add_node("generator", generator)
builder.add_node("critic", critic)
builder.add_edge(START, "generator")


graph = builder.compile()



for chunk in graph.stream({"messages": [("user", source)]}):

    #add count for token
    print("---------------------------------------------------------------------------------------------------------------")