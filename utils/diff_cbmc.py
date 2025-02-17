from bs4 import BeautifulSoup
import os

def get_uncovered_files(html_cont: str) -> list:
    
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


def get_tested_code(uncovered_files: dict):
    code_map = {}
    print("---Processing---")
    for file_path, uncovered_files in uncovered_files.items():
        
        file_path = os.path.join(TEST_FILE_PATH, file_path) # need to be changed    
        with open(file_path, 'r') as file:
                html_cont = file.read()
        
        html = BeautifulSoup(html_cont, 'html.parser')
        
        for i in range(len(uncovered_files)):
            function_name, line = uncovered_files[i]
            
            function_code_snippet = []
            missed_code_snippet = []
            print(f"function: {function_name}, start from: {line}")
            while not get_html_code(html, line)[0].startswith("/*------"):        
                readline_code, is_missed = get_html_code(html, line)
                function_code_snippet.append(readline_code.strip())
                if is_missed:
                    missed_code_snippet.append(readline_code.strip())
                line = str(int(line) + 1)
                
            code_map[function_name] = [' '.join(function_code_snippet), ' '.join(missed_code_snippet)]
    print("---End Processing---")
    return code_map

def get_html_code(html: BeautifulSoup, line: str):
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
    return (start_code.get_text().lstrip().split(" ", maxsplit=1)[1], missed_line)

if __name__ == "__main__":
    
    FUNCTION_NAME = "HTTPClient_Send"
    TEST_FILE_PATH = f"./test/proof/artifacts/{FUNCTION_NAME}/report/html/"
    with open(TEST_FILE_PATH + 'index.html', 'r', encoding='utf-8') as file:
        html_cont = file.read()
    uncovered_files = get_uncovered_files(html_cont)
    print(get_tested_code(uncovered_files))
