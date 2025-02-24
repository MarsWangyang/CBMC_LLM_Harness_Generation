import json
import concurrent.futures # for multiprocessing
from django.shortcuts import render
from django.http import JsonResponse
from django.views.decorators.csrf import csrf_exempt
from .controllers.call import queryLLM
from .controllers.code_analysis.analysis import analyze
from .controllers.flag_generator.flags import get_flags
from .controllers.generate_harness.write import write_harness
from .controllers.harness_refiner.harness_runner import refine_run_harness

def initial(request):
    return JsonResponse({"message": "Server up and running!", "status": 200})

# use curl http://localhost:8000/prompt -H "Content-Type: application/json" -d '{"company": specified-company-here, "prompt": your-prompt-here}'
@csrf_exempt
def test_prompt(request):
    if request.method == "POST":
        try:
            if not request.body:
                return JsonResponse({"status": 400, "message": "Empty request body"})
            user_input = json.loads(request.body)
            company = user_input["company"]
            prompt = user_input["prompt"]
            response = queryLLM(company, prompt, None)
            status = 200 if response is not None else 400
            reply = response if response is not None else "An error has occurred at queryLLM function"
            return JsonResponse({"status": status, "reply": reply})
        except json.JSONDecodeError:
            return JsonResponse({"status": 400, "message": "JSON decoding error"})
    else:
        return JsonResponse({"status": 400, "message": "Please use a POST request!"})

# To call this API endpoint use:
# curl http://localhost:8000/generate -H "Content-Type: application/json" -d '{payload}'
@csrf_exempt
def generate(request):
    if request.method == "POST":
        company = "openai" # specify company here (openai, google, anthropic)
        model = None# specify model here (can be None, see controllers/call.py for defaults)
        try:
            if not request.body:
                return JsonResponse({"status": 400, "message": "Empty request body"})
            data = json.loads(request.body) # context object from frontend
            # create thread pool executor with 2 workers (scalable)
            with concurrent.futures.ThreadPoolExecutor(max_workers = 2) as executor:
                # schedule the API calls concurrently
                future1 = executor.submit(analyze, company, data, model) # analysis LLM codeblock
                future2 = executor.submit(get_flags, company, data, model) # get flags LLM codeblock
                # retrieve results as they complete
                assumptions = future1.result()
                flags = future2.result()
            harness = write_harness(company, data, assumptions, model) # generate harness LLM codeblock
            result = refine_run_harness(company, data, harness, assumptions, flags, 1, model) # iterate for a max 1 times and fix errors within harness (if any) LLM codeblock 
            # print(result)
            # correct output through iteration LLM codeblock
            return JsonResponse({
                "status": 200,
                "message": "Data successfully received!",
                "success": result["correct"],
                "report": result["report"],
                "harness_name": result["name"],
                "harness": result["generated_harness"]
                })
        except json.JSONDecodeError:
            return JsonResponse({"status": 400, "message": "JSON decoding error"})
    else:
        return JsonResponse({"status": 400, "message": "Please use a POST request"})


