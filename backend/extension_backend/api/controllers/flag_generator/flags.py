import os
import json
from ..call import queryLLM

initial_prompt = """
### Task: CBMC Flag Selection**
Analyze function properties and generate a JSON object containing appropriate CBMC flags that should be used for verification.
    - Only use documented CBMC flags that are directly relevant to the function analysis
    - Flags should be based on the syntax referenced in this prompt
    - Do not generate unnecessary or default flags—only those required by the function’s structure and verification needs

### **CBMC Flag Reference*
CBMC supports various verification and transformation options. Based on the function analysis, select appropriate flags from the following categories:
    - Analysis Options: (--trace, --stop-on-fail, --property id)
    - Instrumentation Options: (--bounds-check, --pointer-check, --memory-leak-check, --unwind nr, --no-assertions)
    - Backend Solver Options: (--sat-solver z3, --dimacs, --smt2)
    - Program Representations: (--show-symbol-table, --show-goto-functions)

### **Input Description**
- **entryPoint**: A single function name that is the main function corresponding to 1 key that can be used to access functionMap, functionIndex, functionCode
- **callMatrix**: Represents function call dependencies, where keys are functions mapping to called functions with invocation counts, illustrating execution flow.
- **adjacencyMatrix**: An array of arrays representation of callMatrix, where each row represents a function and each column denotes its calls to other functions
- **functionMap**: A dictionary mapping `{ function_name: absolute_path_to_source_file }`, linking function names to their absolute path
- **functionIndex**: A mapping `{ function_name: index_in_adjacencyMatrix }`, linking function names to their indices for referencing **adjacencyMatrix**
- **functionCode**: A mapping `{ function_name: code_for_function }` linking function names to their relevant code

### **Expected Output (JSON Format)**
Starting from **entry_point** traverse through **callMatrix** until all **code** analyzed, output a JSON object listing CBMC flags:
{
  "flag_name": "flag_value"
}
Only produce the JSON object as output, do not include anything else in your response

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
  "--bounds-check": "enabled",
  "--pointer-check": "enabled",
  "--signed-overflow-check": "enabled",
  "--unwind": "5",
  "--trace": "enabled"
}
"""

# call analysis function (write prompt logic here)
def get_flags(company, context_data, model):
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
    
    # print(response)
    # log output in .txt file
    script_dir = os.path.dirname(os.path.abspath(__file__))
    log_file_path = os.path.join(script_dir, "flag_log.txt")
    with open(log_file_path, 'w') as file:
        file.write(prompt + '\n\n')
        file.write(response)
    clean_response = response.strip("`").replace("json\n", "", 1) # strip start & end ``` and "json" text
    output = json.loads(clean_response) # Convert JSON string to Python dictionary
    return output
