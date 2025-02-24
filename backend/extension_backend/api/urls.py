from django.urls import path
from . import views

urlpatterns = [
    path('', views.initial, name = "initial"),  # default endpoint
    path('prompt', views.test_prompt, name = "test_prompt"), # for the purposes of testing prompts out
    path('generate', views.generate, name = "generate"), # main endpoint handling harness generation
]
