# main call function to communicate with o1, Gemini and Claude
import requests
from dotenv import load_dotenv
from pathlib import Path
import os
from openai import OpenAI
import google.generativeai as genai
import anthropic

# Construct the absolute path to the .env file
BASE_DIR = Path(__file__).resolve().parents[3]  # Move 3 levels up from call.py
ENV_PATH = BASE_DIR / ".env"
load_dotenv(ENV_PATH)

# OpenAI
def fetchOpenAI(payload, model):
    try:
        client = OpenAI(api_key=os.getenv("OPENAI_KEY"))
        response = client.chat.completions.create(
            messages=[
                {
                    "role": "user",
                    "content": payload,
                }
            ],
            model= model,
        )
        return response
    except requests.exceptions.RequestException as e:
        print(f"Exception occurred during OpenAI fetch call: {str(e)}")
        return None       

# for Gemini
def fetchGoogle(payload, model):
    try:
        genai.configure(api_key = os.getenv("GOOGLE_KEY"))
        model = genai.GenerativeModel(model)
        response = model.generate_content(payload)
        return response
    except requests.exceptions.RequestException as e:
        print(f"Exception occurred during Google Gemini fetch call: {str(e)}")
        return None

# for Anthropic
def fetchAnthropic(payload, model):
    try:
        client = anthropic.Anthropic(
            # defaults to os.environ.get("ANTHROPIC_API_KEY")
            api_key = os.getenv("ANTHROPIC_KEY"),
        )
        message = client.messages.create(
            model = model,
            max_tokens=1024, # not sure about this here
            messages=[
                {"role": "user", "content": payload}
            ]
        )
        return message
    except requests.exceptions.RequestException as e:
        print(f"Exception occurred during Anthropic fetch call: {str(e)}")
        return None 

def queryLLM(company, prompt, model, logPath = None):
    service = company.lower()
    # use match (switch cases) to parse different response structures
    match service:
        case "openai":
            model = "gpt-4o" if model is None else model
            response = fetchOpenAI(prompt, model)
            answer = response.choices[0].message.content if response is not None else None
            return answer
        case "google":
            model = "gemini-1.5-flash" if model is None else model
            response = fetchGoogle(prompt, model)
            answer = response.text if response is not None else None
            return answer
        case "anthropic":
            model = "claude-3-5-sonnet-20241022" if model is None else model
            response = fetchAnthropic(prompt, model)
            answer = response.content[0].text if response is not None else None
            return answer
        case _:
            raise ValueError("Company not specified")    