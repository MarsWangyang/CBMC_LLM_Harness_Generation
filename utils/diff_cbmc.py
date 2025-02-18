from bs4 import BeautifulSoup
import os
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
        file_path = os.path.join(TEST_FILE_PATH, file_path) # need to be modified in next version to be more general
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


if __name__ == "__main__":
    # FUNCTION_NAME = "HTTPClient_ReadHeader"
    FUNCTION_NAME = "HTTPClient_Send"
    TEST_FILE_PATH = f"./test/proof/artifacts/{FUNCTION_NAME}/report/html/"
    with open(TEST_FILE_PATH + 'index.html', 'r', encoding='utf-8') as file:
        html_cont = file.read()
    uncovered_files = get_uncovered_files(html_cont)
    extracted_uncovered_file = get_missed_code(uncovered_files)
