import os
import langchain, langgraph, openai
from langchain_openai import ChatOpenAI
from langgraph.graph import StateGraph, MessagesState, START, END
from langgraph.types import Command

import config
import utils
from typing_extensions import Literal


os.environ["OPENAI_API_KEY"] = os.getenv("KEY")
source = utils.read_c_file("source/1.c")



callback_handler = OpenAICallbackHandler
generator_llm = ChatOpenAI(model = "gpt-4", temperature = 0.7)
critic_llm = ChatOpenAI(model="gpt-4", temperature = 0)

utils.clear_log()


def generator(state: MessagesState) -> Command[Literal["critic", "__end__"]]:
    system_prompt = (
        '''You are a helpful software engineer assistor, specialized in generating CBMC harnesses for potentially faulty C/C++ code.
        output only the C code for the harness'''
    )
    #print(f"--------------------------ENTER GENERATOR {int(len(state['messages'])/2+1)}------------------------------")
    #print(state["messages"])
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = generator_llm.invoke(messages)
    header = f"\n\n_____________________________________________ GENERATOR MODEL {int(len(state['messages'])/2+1)} _____________________________________________\n"
    #utils.write_to_log(header + ai_msg.content)
    return Command(
        goto="critic", 
        update={"messages": [ai_msg.content]}
        )

def critic(state: MessagesState) -> Command[Literal["generator", "__end__"]]:
    system_prompt = (
        '''You are a harsh critic that seeks to ensure a proper CBMC harness is generated for the given C/C++ code, evaluate the 
        given harness and provide feedback. ONLY CRITIC, DO NOT generate your idea of the solution. If you are satisfied with the 
        generation or believe it can do its job, respond with "FINISH".'''
    )
    #print(f"--------------------------ENTER CRITIC {int(len(state['messages'])/2)}------------------------------")
    #print(state["messages"])
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = critic_llm.invoke(messages)
    header = f"\n\n_____________________________________________ CRITIC MODEL {int(len(state['messages'])/2)}_____________________________________________\n"
    #utils.write_to_log(header + ai_msg.content)
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



for idx, chunk in enumerate(graph.stream(
    {"messages": [source]}
    )):

    agent = next(iter(chunk))
    msg = next(iter(chunk[agent]))

    print(chunk[agent][msg][-1])

    header = f"\n_____________________________________________ {agent.upper()} MODEL {int(len(idx)/2)}_____________________________________________\n"
    utils.write_to_log(header + chunk[agent][msg][-1])
    #add count for token
    print("---------------------------------------------------------------------------------------------------------------")