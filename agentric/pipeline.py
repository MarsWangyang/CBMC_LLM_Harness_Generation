import os
import argparse
import langchain, langgraph, openai
from langchain_openai import ChatOpenAI
from langgraph.graph import StateGraph, MessagesState, START, END
from langgraph.types import Command
from typing_extensions import Literal

import utils
from agents import Generator, Critic


os.environ["OPENAI_API_KEY"] = os.getenv("KEY")


def generator(state: MessagesState) -> Command[Literal["critic", "__end__"]]:
    print(f"GENERATOR {int(len(state['messages'])/2+1)}->")
    generator_llm = ChatOpenAI(model = Generator.MODEL, temperature = Generator.TEMPERATURE)
    system_prompt = (Generator.SYSTEM_PROMPT)
    messages = [{"role": "system", "content": system_prompt}] + state["messages"]
    ai_msg = generator_llm.invoke(messages)
    return Command(
        goto="critic", 
        update={"messages": [ai_msg.content]}
        )

def critic(state: MessagesState) -> Command[Literal["generator", "__end__"]]:
    print(f"CRITIC {int(len(state['messages'])/2)}->")
    critic_llm = ChatOpenAI(model=Critic.MODEL, temperature = Critic.TEMPERATURE)
    system_prompt = (Critic.SYSTEM_PROMPT
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

        header = f"\n{agent.upper()} MODEL {int(idx/2+1)}___________________________________________________________\n\n"
        utils.write_to_log(header + response + "\n", path)
        
        if agent == "generator":
            code = utils.extract_c_code(response)
            utils.save_c_file(code, path)
        
        #temp endpoint
        if idx == 4:
            break
        

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