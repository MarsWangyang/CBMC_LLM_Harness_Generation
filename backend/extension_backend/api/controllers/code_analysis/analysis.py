import os
import json
from ..call import queryLLM

initial_prompt = """
### Task: Code Dependency Analysis and Assumption Modeling

You are given a set of structured inputs that define relationships between functions in a codebase. Your goal is to analyze the function calls, dependencies, and interactions to extract relevant **assumptions** required for verification, focusing on **four key assumption types**:
1. **Global Variable Modeling** – Handling global variables shared across functions
2. **Input Variable Modeling** – Defining constraints on input parameters
3. **Stub Function Modeling** – Replacing function calls with safe assumptions when necessary
4. **Loop Unwinding Assertions** – Ensuring loops behave correctly within verification constraints

### **Input Description**
- **entryPoint**: A single function name that is the main function corresponding to 1 key that can be used to access functionMap, functionIndex, functionCode
- **callMatrix**: Represents function call dependencies, where keys are functions mapping to called functions with invocation counts, illustrating execution flow.
- **adjacencyMatrix**: An array of arrays representation of callMatrix, where each row represents a function and each column denotes its calls to other functions
- **functionMap**: A dictionary mapping `{ function_name: absolute_path_to_source_file }`, linking function names to their absolute path
- **functionIndex**: A mapping `{ function_name: index_in_adjacencyMatrix }`, linking function names to their indices for referencing **adjacencyMatrix**
- **functionCode**: A mapping `{ function_name: code_for_function }` linking function names to their relevant code

### **Expected Output (JSON Format)**
Starting from **entry_point** traverse through **callMatrix** until all **code** analyzed, output a JSON object listing its assumptions using the following format:

{
  "variable_name": ["variable_type", "assumption_type", "description of the assumption (within 20 words)"]
} 

Only produce the json object above. Do not include anything else in your response

### **Example**
\
#include <stdio.h>


// Insertion Sort function
void insertionSort(int arr[], int size) {
    for (int i = 1; i < size; i++) {
        for (int j = 0; j < i; j++) {
            if (arr[j] > arr[i]) {
                int temp = arr[j];
                arr[j] = arr[i];
                arr[i] = temp;
            }
        }
    }
}
\

### **Output**
{
  "insertionSort": {
    "arr": ["int[]", "input variable modeling", "The array should be initialized and its size must be known and fixed"],
    "size": ["int", "input variable modeling", "The size of the array must be positive and correctly reflect the number of elements in arr"],
    "i": ["int", "loop unwinding assertions", "The loop variable i should iterate from 1 to size-1, ensuring it stays within bounds"],
    "j": ["int", "loop unwinding assertions", "The loop variable j should iterate from 0 to i-1, ensuring it does not access out-of-bound elements"]
  }
}

"""

# call analysis function (write prompt logic here)
def analyze(company, context_data, model):
    context = context_data["context"]
    entry_point = context_data["entry"]
    code = context_data["code"]
    context_payload = {
        "entryPoint": entry_point,
        "functionMap": context["functionMap"],
        "callMatrix": context["callMatrix"],
        "adjacencyMatrix": context["adjacencyMatrix"],
        "functionIndex": context["functionIndex"],
        "functionCode": code
    }
    context_text = json.dumps(context_payload, indent = 4) # turn JSON to string for LLM
    prompt = initial_prompt + "\n" + context_text
    # print(prompt)
    response = queryLLM(company, prompt, model)
    if response == None:
        raise Exception("An error has occurred during API call to LLM")
    # log output in .txt file
    script_dir = os.path.dirname(os.path.abspath(__file__))
    log_file_path = os.path.join(script_dir, "analysis_log.txt")
    with open(log_file_path, 'w') as file:
        file.write(prompt + '\n\n')
        file.write(response)
    clean_response = response.strip("`").replace("json\n", "", 1) # strip start & end ``` and "json" text
    output = json.loads(clean_response) # Convert JSON string to Python dictionary
    return output
