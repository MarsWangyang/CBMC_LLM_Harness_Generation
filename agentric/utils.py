import json
import os

def load_config():
     with open("config.json") as f:
          config = json.load(f)
          return config

def read_c_file(path: str) -> str:
        filepath = os.path.join(path, "sc.c")
        if os.path.exists(filepath):
            with open(filepath, 'r') as f:
                return f.read()
        return None

def save_c_file(content: str, path: str):
    filepath = os.path.join(path, "out.c")
    with open(filepath, 'w') as f:
        f.write(content)

def create_log(path:str) -> bool:
    filepath = os.path.join(path, "log.txt")
    if os.path.exists(filepath):
        return False
    with open(filepath, "w") as f:
        f.close()
    return True

def clear_log(path: str):
    filepath = os.path.join(path, "log.txt")
    with open(filepath, "w") as f:
        f.write("")
        f.close()

def write_to_log(content: str, path: str):
    filepath = os.path.join(path, "log.txt")
    with open(filepath, "a") as f:
        f.write(content)
        f.close()

def extract_c_code(response: str) -> str:
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

