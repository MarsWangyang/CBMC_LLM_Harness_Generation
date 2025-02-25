import os
import argparse
import langchain, langgraph, openai
from langchain_openai import ChatOpenAI
from langgraph.graph import StateGraph, MessagesState, START, END
from langgraph.types import Command

import utils
from typing_extensions import Literal


os.environ["OPENAI_API_KEY"] = os.getenv("KEY")
CONFIG = utils.load_config()
DATA = CONFIG["data_path"]
GENERATOR_MODEL= CONFIG["generator"]["model"]
CRITIC_MODEL= CONFIG["critic"]["model"]
GENERATOR_TEMPERATURE= CONFIG["generator"]["temperature"]
CRITIC_TEMPERATURE= CONFIG["critic"]["temperature"]


def generator(state: MessagesState) -> Command[Literal["critic", "__end__"]]:
    print(f"GENERATOR {int(len(state['messages'])/2+1)}->")
    generator_llm = ChatOpenAI(model = GENERATOR_MODEL, temperature = GENERATOR_TEMPERATURE)
    system_prompt = (
        '''You are a helpful software engineer assistor, specialized in generating CBMC harnesses for potentially faulty C/C++ code.
        output only the C code for the harness'''
    )
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = generator_llm.invoke(messages)
    return Command(
        goto="critic", 
        update={"messages": [ai_msg.content]}
        )

def critic(state: MessagesState) -> Command[Literal["generator", "__end__"]]:
    print(f"CRITIC {int(len(state['messages'])/2)}->")
    critic_llm = ChatOpenAI(model=CRITIC_MODEL, temperature = CRITIC_TEMPERATURE)
    system_prompt = (
        '''You are a harsh critic that seeks to ensure a proper CBMC harness is generated for the given C/C++ code, evaluate the 
        given harness and provide feedback. ONLY CRITIC, DO NOT generate your idea of the solution. If you are satisfied with the 
        generation or believe it can do its job, respond with "FINISH".'''
    )
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = critic_llm.invoke(messages)
    if "FINISH" in ai_msg.content:
        return Command(
            goto= END,
            update={"messages": [ai_msg.content]}
        )
    return Command(
        goto="generator", 
        update={"messages": [ai_msg.content]}
        )


def build_pipeline() -> StateGraph:
    builder = StateGraph(MessagesState)

    builder.add_node("generator", generator)
    builder.add_node("critic", critic)
    builder.add_edge(START, "generator")

    return builder.compile()

def run_pipeline(graph, source, path):
    for idx, chunk in enumerate(graph.stream(
        {"messages": [source]}
        )):
        agent = next(iter(chunk))
        msg = next(iter(chunk[agent]))

        response = chunk[agent][msg][-1]

        header = f"\n_____________________________________________ {agent.upper()} MODEL {int(idx/2+1)}_____________________________________________\n\n"
        utils.write_to_log(header + response + "\n", path)
        if agent == "generator":
            code = utils.extract_c_code(response)
            utils.save_c_file(code, path)
        #add count for token

def main(data_dir, start, num_files, run_all):


    folders = [f for f in os.listdir(data_dir) if os.path.isdir(os.path.join(data_dir, f))]

    if run_all:
        num_files = len(folders) - start
    
    if not num_files:
        num_files = 1

    for i in range(start, min(start + num_files, len(folders))):

        print(f"Working on data {i}")
        
        folder = folders[i]
        folder_path = os.path.join(data_dir, folder)
        
        source = utils.read_c_file(folder_path)

        if not source:
            print(f"\nWarning: {folder_path} source code not found \n\n")
            continue

        if not utils.create_log(folder_path):            
            utils.clear_log(folder_path)

        pipeline = build_pipeline()

        run_pipeline(pipeline, source, folder_path)
    


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Process data in the given folder.")
    parser.add_argument("--data_dir", type=str, required=True, help="Path to the data folder.")
    parser.add_argument("--start", type=int, default=0, help="Starting folder index.")
    parser.add_argument("-n", "--num_files", type=int, help="Number of files to process starting from the start_index.")
    parser.add_argument("-a", "--all", action="store_true", help="Flag to run all files starting from the start_index.")
    
    # Parse arguments
    args = parser.parse_args()
    
    # Determine if we should run all files or a specific range
    run_all = args.all
    num_files = args.num_files if not run_all else None
    
    # Call the main function with parsed arguments
    main(args.data_dir, args.start, num_files, run_all)