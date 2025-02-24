import os
from typing import Optional, Dict, Any, List
from dotenv import load_dotenv
import anthropic
from openai import OpenAI
import google.generativeai as genai
from datetime import datetime

load_dotenv()

class LLMClient:
    def __init__(self):
        self.anthropic_client = anthropic.Client(api_key=os.getenv("ANTHROPIC_API_KEY"))
        self.openai_client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        genai.configure(api_key=os.getenv("GOOGLE_API_KEY"))
        self.gemini_model = genai.GenerativeModel('gemini-pro')
        
        self.responses_dir = "responses"
        self.code_dir = "code"
        os.makedirs(self.responses_dir, exist_ok=True)
        os.makedirs(self.code_dir, exist_ok=True)

    def read_c_file(self, filepath: str) -> str:
        with open(filepath, 'r') as f:
            return f.read()

    def save_c_file(self, content: str, filename: str) -> str:
        filepath = os.path.join(self.code_dir, filename)
        with open(filepath, 'w') as f:
            f.write(content)
        return filepath

    def process_c_code(self, file_path: str, prompt_template: str = None, model: str = "claude") -> str:
        code_content = self.read_c_file(file_path)
        
        if prompt_template is None:
            prompt_template = """
            Analyze this C code and provide:
            1. Code review
            2. Potential improvements
            3. Security issues
            4. Optimized version of the code (wrap the optimized code in ```c code blocks)
            
            Here's the code:
            {code}
            """
            
        prompt = prompt_template.format(code=code_content)
        
        if model == "claude":
            response = self.call_claude(prompt)
        elif model == "gpt":
            response = self.call_gpt(prompt)
        elif model == "gemini":
            response = self.call_gemini(prompt)
            
        if response:
            try:
                optimized_code = self._extract_c_code(response)
                if optimized_code:
                    filename = f"optimized_{model}_{os.path.basename(file_path)}"
                    saved_path = self.save_c_file(optimized_code, filename)
                    print(f"Saved {model}'s optimized code to: {saved_path}")
            except Exception as e:
                print(f"Error saving optimized code from {model}: {str(e)}")
                
        return response

    def _extract_c_code(self, response: str) -> Optional[str]:
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

    def save_analysis_report(self, original_code: str, model_responses: Dict[str, str], file_path: str):
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        report_file = f"{self.responses_dir}/analysis_report_{timestamp}.txt"
        
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write("C CODE ANALYSIS REPORT\n")
            f.write("=" * 50 + "\n\n")
            
            f.write("Original Code:\n")
            f.write("-" * 20 + "\n")
            f.write(original_code + "\n\n")
            
            for model, response in model_responses.items():
                f.write(f"{model.upper()} ANALYSIS:\n")
                f.write("-" * 20 + "\n")
                f.write(response + "\n\n")
                
                opt_code = self._extract_c_code(response)
                if opt_code:
                    f.write(f"{model.upper()} Optimized Code:\n")
                    f.write("-" * 20 + "\n")
                    f.write(opt_code + "\n\n")
                    
            f.write("=" * 50 + "\n")
        return report_file

    def call_claude(self, prompt: str, model: str = "claude-3-opus-20240229",
                   max_tokens: int = 1000, temperature: float = 0.7) -> str:
        try:
            response = self.anthropic_client.messages.create(
                model=model,
                max_tokens=max_tokens,
                temperature=temperature,
                messages=[
                    {"role": "user", "content": prompt}
                ]
            )
            return str(response.content)
        except Exception as e:
            print(f"Error calling Claude API: {str(e)}")
            return None

    def call_gpt(self, prompt: str, model: str = "gpt-4-turbo-preview",
                 max_tokens: int = 1000, temperature: float = 0.7) -> str:
        try:
            response = self.openai_client.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=max_tokens,
                temperature=temperature
            )
            return response.choices[0].message.content
        except Exception as e:
            print(f"Error calling GPT API: {str(e)}")
            return None

    def call_gemini(self, prompt: str, model: str = "gemini-pro",
                    max_tokens: int = 1000, temperature: float = 0.7) -> str:
        try:
            response = self.gemini_model.generate_content(prompt,
                generation_config=genai.types.GenerationConfig(
                    max_output_tokens=max_tokens,
                    temperature=temperature
                )
            )
            return str(response.text)
        except Exception as e:
            print(f"Error calling Gemini API: {str(e)}")
            return None

    def save_response(self, model_name: str, prompt: str, response: str) -> str:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        filename = f"{self.responses_dir}/{model_name}_{timestamp}.txt"
        
        output = f"""Timestamp: {timestamp}
Model: {model_name}
Prompt: {prompt}
Response: {response}"""

        with open(filename, 'w', encoding='utf-8') as f:
            f.write(output)
        return filename

    def compare_responses(self, prompt: str, models: List[Dict[str, Any]] = None) -> Dict[str, str]:
        if models is None:
            models = [
                {"name": "claude", "model": "claude-3-opus-20240229"},
                {"name": "gpt", "model": "gpt-4-turbo-preview"},
                {"name": "gemini", "model": "gemini-pro"}
            ]
            
        responses = {}
        
        for model_config in models:
            name = model_config["name"]
            if name == "claude":
                response = self.call_claude(prompt, model=model_config["model"])
            elif name == "gpt":
                response = self.call_gpt(prompt, model=model_config["model"])
            elif name == "gemini":
                response = self.call_gemini(prompt, model=model_config["model"])
            else:
                print(f"Unknown model type: {name}")
                continue
            
            responses[name] = response
            if response:
                saved_file = self.save_response(name, prompt, response)
                print(f"Saved {name} response to: {saved_file}")
            
        return responses

def main():
    client = LLMClient()
    c_file_path = "example.c"
    
    with open(c_file_path, 'r') as f:
        original_code = f.read()
    
    model_responses = {}
    for model in ["claude", "gpt", "gemini"]:
        print(f"\n{model.upper()} Analysis:")
        response = client.process_c_code(c_file_path, model=model)
        model_responses[model] = response
        print(response)
    
    report_file = client.save_analysis_report(original_code, model_responses, c_file_path)
    print(f"\nDetailed analysis report saved to: {report_file}")

if __name__ == "__main__":
    main()