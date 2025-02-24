import os
import json
from ..call import queryLLM

initial_prompt = """
### Task: Generating a CBMC Harness for Function Verification

You are given a function and its relevant assumptions, along with structured metadata representing function relationships and dependencies. Your task is to generate a **CBMC proof harness** using **only the specified syntax**.

### **Syntax Reference**
Use only the following syntax when generating assumptions:

unsigned int nondet_uint();
__CPROVER_assume(condition);
__CPROVER_assert(condition, "assertion message");

You must ensure that:
- All nondeterministic values are constrained with __CPROVER_assume
- Assertions are placed after assumptions to prevent vacuous proofs
- Loop unwinding assertions are included where necessary and appropriately
- Stub functions return nondeterministic values but are assumed within valid ranges

### **Input Description**
- **entryPoint**: The main function to generate the harness for is also a key that can be used to access functionMap, functionIndex, functionCode
- **callMatrix**: Represents function call dependencies, where keys are functions mapping to called functions with invocation counts, illustrating execution flow.
- **functionCode**: A mapping `{ function_name: code_for_function }` linking function names to their relevant code
- **codeAnalysis**: A mapping of function assumptions for verification, categorizing variables by type, modeling input constraints, global state, loop bounds, and stub behavior for analysis containing:
{
  "function_name": {"variable_name": ["variable_type", "assumption_type", "description of the assumption (within 20 words)"]}
} 

### **Expected Output (harness name should be entryPoint_harness) **
**entryPoint**_harness() {
    assumptions here
    **entryPoint** function here
    assumptions (where necessary)
}

Only produce the harness function above. Do not include anything other than that in your response

### **Example**
\
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
// **codeAnalysis** input:
{
  "arr": ["int[]", "input variable modeling", "The array should be initialized and its size must be known and fixed."],
  "size": ["int", "input variable modeling", "The size of the array must be positive and correctly reflect the number of elements in arr."],
  "i": ["int", "loop unwinding assertions", "The loop variable i should iterate from 1 to size-1, ensuring it stays within bounds."],
  "j": ["int", "loop unwinding assertions", "The loop variable j should iterate from 0 to i-1, ensuring it does not access out-of-bound elements."]
}

\
### **Output**
void insertionSort_harness() {
    int arr[10];
    int size = nondet_uint();

    __CPROVER_assume(size > 0 && size <= 10);

    for (int i = 1; i < size; i++) {
        __CPROVER_assume(i >= 1 && i < size);
        for (int j = 0; j < i; j++) {
            __CPROVER_assume(j >= 0 && j < i);
        }
    }

    insertionSort(arr, size);
}

"""

# call analysis function (write prompt logic here)
def write_harness(company, context_data, assumptions, model):
    context = context_data["context"]
    entry_point = context_data["entry"]
    code = context_data["code"]
    context_payload = {
        "entryPoint": entry_point,
        "callMatrix": context["callMatrix"],
        "functionCode": code,
        "codeAnalysis": assumptions
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
    log_file_path = os.path.join(script_dir, "write_log.txt")
    with open(log_file_path, 'w') as file:
        file.write(prompt + '\n\n')
        file.write(response)
    clean_response = response.strip("`").replace("c\n", "", 1) # strip start & end ``` and "c" text

    return clean_response # should return string
