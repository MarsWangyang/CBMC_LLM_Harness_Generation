from bs4 import BeautifulSoup
import os, json
from typing import *

def get_uncovered_files(html_cont: str) -> Dict[str, list]:
    """
        Get the files that have uncovered lines. (The coverage is not 1.00)
        :param html_cont: The html content of the coverage report
        :return: The dictionary of uncovered files
            key: The file path
            value: The list of uncovered functions
    """
    html = BeautifulSoup(html_cont, 'html.parser')
    td_tags = html.find_all("tr")
    uncovered_files_map = {}
    
    for tag in td_tags:
        if tag.find('td', class_ = 'coverage'):
            coverage = tag.find('td', class_ = 'coverage').get_text()
        else:
            continue
        if not coverage.startswith("1.00"):
            function_name = tag.find('td', class_ = 'function').get_text()
            file_path, start_line = tag.select_one('a')['href'].split('#')
            if not uncovered_files_map.get(file_path):
                uncovered_files_map[file_path] = uncovered_files_map.get(file_path, []) + [(function_name, start_line)]
            else:
                uncovered_files_map[file_path].append((function_name, start_line))

    return uncovered_files_map


def get_html_code(html: BeautifulSoup, line: str) -> Tuple[str, bool]:
    """
        Get the specific line in html file.
        :param html: The html file
        :param line: The specific line
        :return:
            [0]: The processed code in the line
            [1]: Is the line missed (True: tagged missed/both, False: tagged hit, None: tagged none)
    """
    start_code = html.find("div", {"id": line})
    if start_code is None:
        return ("/*------End of the file------*/", None)
    missed_line = False
    is_missed_line = start_code.attrs["class"][1]
    
    if is_missed_line == "hit":
        missed_line = False
    elif is_missed_line == "missed" or is_missed_line == "both":
        missed_line = True
    else:
        missed_line = None

    return (start_code.get_text().lstrip().split(" ", maxsplit=1)[1].lstrip(), missed_line)


def get_missed_code(uncovered_files: dict) -> Dict[str, list]:
    """
    Get the code snippet of the uncovered files
    :param uncovered_files: The dictionary of uncovered files
    :return: The code snippet of the uncovered files
        key: The function name
        value: The list of code snippet
            [0]: The whole function code snippet
            [1]: The concatanated string of missed code line (only the line with missed tag) -> test for now, need to be removed in next version
            [2]: The list of missed code snippet (the whole missed code snippet)
    """
    
    code_map = {}
    print("---Processing---")
    
    for file_path, uncovered_files in uncovered_files.items():
        file_path = os.path.join(ROOT_FILE_PATH, "html", file_path) # need to be modified in next version to be more general
        with open(file_path, 'r') as file:
                html_cont = file.read()
        
        html = BeautifulSoup(html_cont, 'html.parser')
        
        # process each uncovered function in the same html report file
        for i in range(len(uncovered_files)):
            function_name, current_line = uncovered_files[i]
            
            function_code_snippet = []
            missed_code_line = []
            missed_code_snippet = []
            last_hit_line = -1
            has_missed = False
            
            print(f"function: {function_name}, start from: {current_line}")
            
            # process the function until the end of the function
            while not get_html_code(html, current_line)[0].startswith("/*------"):        
                readline_code, is_missed = get_html_code(html, current_line)
                function_code_snippet.append(readline_code.strip())
                
                if is_missed:
                    missed_code_line.append(readline_code.strip())
                    has_missed = True
                elif is_missed == False:
                    # If previous lines are not missed, it will keep searching for the missed lines
                    if has_missed:
                        has_missed = False
                        inconcat_code_snippet = []
                        parse_line = str(int(last_hit_line))
                        
                        # If the following lines are missed, keep concatenating them until the next hit line 
                        while not get_html_code(html, parse_line)[0].startswith("/*------"):
                            inconcat_code_snippet.append(get_html_code(html, str(parse_line))[0])
                            parse_line = str(int(parse_line) + 1)
                            if get_html_code(html, parse_line)[1] == False:
                                break
                        missed_code_snippet.append(' '.join(inconcat_code_snippet))
                        
                    last_hit_line = current_line
                current_line = str(int(current_line) + 1)
            code_map[function_name] = [' '.join(function_code_snippet), ' '.join(missed_code_line), missed_code_snippet]
    print("---End Processing---")
    return code_map

def get_failure(property_cont: dict, result_cont: dict) -> List[str]:
    """
    Get the failure line from the property and result json file
    :param property_cont: The content of the property json file (viewer-property.json)
    :param result_cont: The content of the result json file (viewer-result.json)
    :return: The list of failure line
    """
    
    failure_map = {}
    
    fail_result_list = result_cont["viewer-result"]["results"]["false"]
    property_list = property_cont["viewer-property"]["properties"]
    
    for fail in fail_result_list:
        print("fail: ", fail)
        if fail.split(".")[1] == "no-body":
            failure_map[fail] = {
                "description": f"The harness currently doen't have function that is named after '{fail.split(".")[0]}' to be called"
            }
        else:
            if not property_list.get(fail):
                failure_map[fail] = {
                    "description": f"We currently don't know what is happening to this error. Need to figure this out"
                }
            else:
                fail_error = property_list.get(fail)
                fail_class = fail_error["class"]
                fail_description = fail_error["description"]
                fail_expression = fail_error["expression"] # what expression makes the line of the code wrong
                fail_location = fail_error["location"]["file"]
                fail_location_line = fail_error["location"]["line"]
                
                file_path = os.path.join(TEST_FILE_PATH , 'html/', fail_location+".html") # need to be modified in next version to be more general
                
                with open(file_path, 'r') as file:
                        html_cont = file.read()
                
                html = BeautifulSoup(html_cont, 'html.parser')
                fail_code = get_html_code(html, fail_location_line)
                
                failure_map[fail] = {
                    "class": f"{fail_class}",
                    "description": f"{fail_description}",
                    "expression": f"{fail_expression}",
                    "code": f"{fail_code[0]}"
                }
    if failure_map == {}:
        failure_map["noError"] = {
            "description": "No Error is found in the harness."
        }
        
    return failure_map


if __name__ == "__main__":
    # ------ Missed line parser ------
    FUNCTION_NAME = "HTTPClient_ReadHeader"
    # FUNCTION_NAME = "HTTPClient_Send"
    ROOT_FILE_PATH = f"./test/proof/artifacts/{FUNCTION_NAME}/report/"
    TEST_FILE_PATH = os.path.join(ROOT_FILE_PATH, "html", "index.html")
    print(TEST_FILE_PATH)
    with open(TEST_FILE_PATH, 'r', encoding='utf-8') as file:
        html_cont = file.read()
    uncovered_files = get_uncovered_files(html_cont)
    extracted_uncovered_file = get_missed_code(uncovered_files)
    print(extracted_uncovered_file)
    
    # ------ Property and Result parser ------
    
    # it only used for testing, need to remove '_test' for the real implementation
    PROPERTY = "viewer-property.json"
    RESULT = "viewer-result.json"
    with open(ROOT_FILE_PATH + 'json/' + PROPERTY, 'r', encoding='utf-8') as file:
        property_cont = json.load(file)
    with open(ROOT_FILE_PATH + 'json/' + RESULT, 'r', encoding='utf-8') as file:
        result_cont = json.load(file)
    
    print(get_failure(property_cont, result_cont))
