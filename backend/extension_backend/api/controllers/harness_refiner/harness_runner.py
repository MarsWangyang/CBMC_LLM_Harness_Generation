import os
import json
import re
import subprocess
from ..call import queryLLM
initial_prompt = """\
### Task: CBMC Error Handling and Harness Correction

You are given a **CBMC proof harness**, an **error report**, and structured metadata representing function relationships, assumptions, and verification flags. Your goal is to:
1. **Analyze CBMC’s error report** and identify which constraints, assumptions, or flags may need adjustment
2. **Modify the proof harness** to resolve errors while preserving correctness
3. **Ensure that changes align with CBMC verification requirements**, without introducing unnecessary constraints


### **Input Metadata**
You will receive the following structured inputs:
- **generatedHarness**: The CBMC proof harness that was used in verification.
- **errorReport**: The output from CBMC detailing verification failures.
- **functionCode**: A dictionary `{ function_name: code_for_function }` containing the source code for relevant functions.
- **functionIndex**: A dictionary mapping `{ function_name: index_in_adjacencyMatrix }`, linking function names to their indices.
- **adjacencyMatrix**: An array representation of function call dependencies.
- **entryPoint**: The function that serves as the starting point of verification.
- **assumptions**: A structured dictionary `{ function_name: { variable_name: [variable_type, assumption_type, description] } }` containing assumptions for verification
- **cbmcFlags**: A JSON object `{ flag_name: flag_value }` containing CBMC verification flags used during the failed run.

---

### **Expected Output**
1. **Analyze CBMC’s error report** and determine which errors need to be addressed.
2. **Modify the harness accordingly** using only valid CBMC syntax (`__CPROVER_assume`, `__CPROVER_assert`, `unsigned int nondet_uint()` functions).
3. **Adjust assumptions or verification flags if needed** to ensure correctness.
4. **Return the corrected proof harness in valid C code format.**

Your output should **only contain the corrected harness**, **do not include any additional explanation or comments**.

---

### **Example Inputs**
#### **generatedHarness**
void insertionSort_harness() {
    int arr[10];
    int size = __CPROVER_nondet_size_t();
    
    __CPROVER_assume(size > 0 && size <= 10);
    
    for (int i = 1; i < size; i++) {
        __CPROVER_assume(i >= 1 && i < size);
        for (int j = 0; j < i; j++) {
            __CPROVER_assume(j >= 0 && j < i);
        }
    }

    insertionSort(arr, size);
}

#### **errorReport**
[insertionSort_harness.no-body.__CPROVER_nondet_size_t] line 3 no body for callee __CPROVER_nondet_size_t: FAILURE

### **Output**
void insertionSort_harness() {
    int arr[10];
    int size = nondet_uint();

    __CPROVER_assume(size > 0 && size <= 10);
    
    for (int i = 1; i < size; i++) {
        __CPROVER_assume(i >= 1 && i < size);
        for (int j = 0; j < i; j++) {
            __CPROVER_assume(j >= 0 && j < i);
            __CPROVER_assume(arr[j] >= 0 && arr[j] < 10);  // Added bounds check
        }
    }

    __CPROVER_assert(size <= 10, "size is within valid range");

    insertionSort(arr, size);
}
"""

# function to parse report
def parseReport(report):
    # parse results
    pattern = r"(\*\* Results:.*)" # match everything after (including) ** Results:
    match = re.search(pattern, report, re.DOTALL)
    processed_report = match.group(1)
    # Add error keywords here (Case sensitive)!
    error_keywords = [
        "no body for callee",
        "not found"
    ]
    keyword_pattern = "|".join(re.escape(keyword) for keyword in error_keywords)
    error_pattern = re.compile(r"^\[.*\] line \d+ .*(" + keyword_pattern + r").* FAILURE$")
    
    # Extract matching error lines
    errors = [line.strip() for line in processed_report.splitlines() if error_pattern.match(line)]
    # response
    result = {"success": False, "report": errors}
    if len(errors) > 0:
        return result
    # If all correct extract lines that are not errors
    valid = [line.strip() for line in processed_report.splitlines() if not error_pattern.match(line) and line != '']
    result["success"] = True
    result["report"] = valid
    return result

# Running CBMC + Parse report
def check_harness(entry_point, generated_harness, cbmc_flags, script_dir):
    # construct C file
    harnessName = entry_point + "_harness"
    fileName = harnessName + ".c"
    file_name_path = os.path.join(script_dir, fileName)
    with open(file_name_path, 'w') as file:
        file.write(generated_harness)
    # construct CLI commands
    commands = ["cbmc", fileName]
    for flag in cbmc_flags:
        commands.append(flag)
        if cbmc_flags[flag] != "enabled":
            commands.append(cbmc_flags[flag])
    # print(commands)
    # run CBMC through subprocess
    try:
        result = subprocess.run(commands, capture_output=True, text=True, check=True)
        print("Success:\n", result.stdout)
        parsedResults = parseReport(result.stdout)
        parsedResults["name"] = harnessName
        return parsedResults
    except FileNotFoundError as error:
        print("File was not found within system:\n", error)
        log_file_path = os.path.join(script_dir, "harness_runner_log.txt")
        with open(log_file_path, 'a') as file: # log CBMC not found error
            file.write(f"CBMC was not found on system:{error}")
        errorResult = {"success": False, "report": f"File not found on system: {error}", "name": harnessName}
        return errorResult
    except subprocess.CalledProcessError as e:
        print("System error occurred:\n", e.stderr)
        log_file_path = os.path.join(script_dir, "harness_runner_log.txt")
        with open(log_file_path, 'a') as file: # log error within harness_runner_log.txt
            file.write(f"System error occurred:\n{e.stderr}")
        errorResult = {"success": False, "report": f"System error occurred: {e.stderr}", "name": harnessName}
        return errorResult


# iteration to fix errors
def fix_error(company, context_data, generated_harness, error_report, analysis_assumptions, cbmc_flags, log_file_path, model, iteration):
    context = context_data["context"]
    entry_point = context_data["entry"]
    code = context_data["code"]
    context_payload = {
        "entryPoint": entry_point,
        "adjacencyMatrix": context["adjacencyMatrix"],
        "functionIndex": context["functionIndex"],
        "functionCode": code,
        "generatedHarness": generate_harness,
        "errorReport": error_report,
        "assumptions": analysis_assumptions,
        "cbmcFlags": cbmc_flags
    }
    context_text = json.dumps(context_payload, indent = 4) # turn JSON to string for LLM
    prompt = initial_prompt + "\n" + context_text
    # print(prompt)
    response = queryLLM(company, prompt, model)
    if response == None:
        raise Exception("An error has occurred during API call to LLM")
    # log each iteration prompt + response
    with open(log_file_path, 'a') as file:
        file.write(f"Iteration {iteration}:\n")
        file.write(prompt + '\n')
        file.write(response)

    clean_response = response.strip("`").replace("c\n", "", 1) # strip start & end ``` and "json" text
    output = json.loads(clean_response) # Convert JSON string to Python dictionary
    return output

# call analysis function (write prompt logic here)
def refine_run_harness(company, context_data, generated_harness, analysis_assumptions, cbmc_flags, maxIter, model):
    script_dir = os.path.dirname(os.path.abspath(__file__)) # current directory
    log_file_path = os.path.join(script_dir, "harness_runner_log.txt")
    entry_point = context_data["entry"] # for C file name

    # Return this
    result = {"correct": False, "generated_harness": generated_harness, "name": None}
    # validate
    validationResult = check_harness(entry_point, generated_harness, cbmc_flags, script_dir)
    if validationResult["success"] == False and (validationResult["report"].startswith("File not found on system:") or validationResult["report"].startswith("System error occurred:")):
        result["report"] = validationResult["report"]
        result["name"] = validationResult["name"]
        return result
    elif validationResult["success"]:
        result["correct"] = True
        result["name"] = validationResult["name"]
        result["report"] = validationResult["report"]
        return result
    # log output in .txt file
    with open(log_file_path, 'w') as file:
        file.write("Error detected!\n")
    # commence error fixing
    correctness = False
    for times_run in range(maxIter):
        generated_harness = fix_error(company, context_data, generated_harness, error_report, analysis_assumptions, cbmc_flags, log_file_path, model, times_run + 1)
        validationResult = check_harness(entry_point, generated_harness, cbmc_flags, script_dir)
        if validationResult["success"]:
            result["generated_harness"] = generated_harness
            result["report"] = validationResult["report"]
            result["correct"] = True
            return result
    # if it still fails, return most recent updated harness
    result["generated_harness"] = generated_harness
    result["report"] = validationResult["report"]
    return result
