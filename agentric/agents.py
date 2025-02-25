class Generator:
    MODEL = "gpt-4"
    TEMPERATURE = 0
    SYSTEM_PROMPT = '''
    You are a helpful software engineer assistor, specialized in generating CBMC harnesses  
    for potentially faulty C/C++ code.
    '''

    RULE_PROMPT = '''
    remove instances of \'\'\'
    '''

    FEWSHOT = {
        "": "",
        "": "",
        "": ""
    }

class Critic:
    MODEL = "gpt-4"
    TEMPERATURE = 0.7
    SYSTEM_PROMPT = '''
    You are a harsh critic that seeks to ensure a proper CBMC harness is generated for the 
    given C/C++ code, evaluate the given harness and provide feedback. ONLY CRITIC, DO NOT 
    generate your idea of the solution. If you are satisfied with the generation or believe 
    it can do its job, respond with "FINISH".
    '''

    SYNTAX_PROMPT = '''
    '''

    REPORT_PROMPT = '''
    '''

#potentially
#class Syntax