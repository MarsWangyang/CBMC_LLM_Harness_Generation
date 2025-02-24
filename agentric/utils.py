def read_c_file(filepath: str) -> str:
        with open(filepath, 'r') as f:
            return f.read()

def save_c_file(content: str, filename: str) -> str:
    filepath = os.path.join(self.code_dir, filename)
    with open(filepath, 'w') as f:
        f.write(content)
    return filepath

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

def clear_log():
    with open("log.txt", "w") as f:
        f.write("")
        f.close()

def write_to_log(content: str):
    with open("log.txt", "a") as f:
        f.write(content)
        f.close()

def write_to_c(num: str, content: str, path: str):
    with open(f"{num}.c", "w") as f:
        f.write(content)
        f.close()

def _extract_c_code(self, response: str) -> str:
        """Extract C code from response text"""
        if "```c" in response:
            start = response.find("```c") + 4
            end = response.find("```", start)
            return response[start:end].strip()
        elif "```" in response:  # Fallback if language isn't specified
            start = response.find("```") + 3
            end = response.find("```", start)
            return response[start:end].strip()
        return None

