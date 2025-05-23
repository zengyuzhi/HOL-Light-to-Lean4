# Pipeline for formalizing theorems in Lean 4
import os
import re
import json

from dotenv import load_dotenv
from loguru import logger
from openai import OpenAI

from utils.proof_utils import parse_client_response

load_dotenv()


class FormalizationPipeline:
    def __init__(
        self,
        model_for_sketch,
        model_for_proof,
        gpu_utilization=0.5,
        max_tokens=2048,
        temperature=0.1,
        top_p=0.95,
    ):
        self.model_for_sketch = model_for_sketch
        self.model_for_proof = model_for_proof
        self.gpu_utilization = gpu_utilization
        self.max_tokens = max_tokens
        self.temperature = temperature
        self.top_p = top_p

    def initialize_vllm(self):
        # Initialize the VLLM model
        pass

    def initialize_openai(self):
        # Initialize OpenAI API
        API_KEY = os.getenv("OPENAI_API_KEY")
        BASE_URL = os.getenv("OPENAI_API_BASE")
        if API_KEY is None:
            raise ValueError("Please set the OPENAI_API_KEY environment variable.")
        if BASE_URL is None:
            raise ValueError("Please set the OPENAI_API_BASE environment variable.")
        client = OpenAI(api_key=API_KEY, base_url=BASE_URL)
        return client

    def generate_sketch(self, system_prompt, user_prompt, imports, doc):
        # Generate a response using the OpenAI API
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt.format(imports=imports, doc=doc)

        if "deepseek" in self.model_for_sketch:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_sketch,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def postprocess_sketch(self, sketch):
        # Post-process the generated sketch
        # Using re to extract the Lean 4 code block
        match = re.search(r"```lean(.*?)```", sketch, re.DOTALL)
        if match:
            sketch = match.group(1).strip()
        else:
            raise ValueError("No Lean 4 code block found in the response.")
        return sketch

    def refine_sketch(self, system_prompt, user_prompt, doc, sketch, errors):
        # Generate a response using the OpenAI API
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt.format(doc=doc, sketch=sketch, errors=errors)

        if "deepseek" in self.model_for_sketch:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_sketch,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def postprocess_formalization(self, formalization):
        # Post-process the generated formalization
        # Using re to extract the Lean 4 code block
        match = re.search(r"```lean(.*?)```", formalization, re.DOTALL)
        if match:
            formalization = match.group(1).strip()
        else:
            raise ValueError("No Lean 4 code block found in the response.")
        return formalization

    def generate_formalization(self, system_prompt, user_prompt, doc, sketch, sorries):
        # Generate formalization using the OpenAI API
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt.format(sketch=sketch, doc=doc, sorries=sorries)

        if "deepseek" in self.model_for_proof:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": prompt},
            ]
        sampling_params = {
            "model": self.model_for_proof,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def refine_formalization(
        self, system_prompt, user_prompt, doc, formalization, errors
    ):
        # Generate a response using the OpenAI API
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt.format(doc=doc, file=formalization, errors=errors)

        if "deepseek" in self.model_for_proof:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_proof,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def generate_one_proof(self, system_prompt, user_prompt, doc, sketch, deps):
        # Formalize the proof for one theorem with dependencies
        client = self.initialize_openai()
        # Construct the prompt for formalziation
        prompt = user_prompt.format(doc=doc, sketch=sketch, deps=deps)
        if "deepseek" in self.model_for_proof:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_proof,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def fix_formalization(
        self, system_prompt, user_prompt, formalization, errors
    ):
        # Fix the formalization using the OpenAI API
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt.format(
            codes=formalization, errors=errors
        )

        if "deepseek" in self.model_for_proof:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_proof,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def fix_formalization_with_sorries(
        self, system_prompt, user_prompt, formalization, errors, informal_proof
    ):
        # Subsitutes the error part with sorries using the OpenAI API
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt.format(codes=formalization, errors=errors, informal_proof=informal_proof)

        if "deepseek" in self.model_for_sketch:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_sketch,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return response.choices[0].message.content

    def extract_stm_from_sketch(self, system_prompt, user_prompt, sketch):
        """
        ```json
        [
        {"HOL_Light_Name": "Lean4_Content"},
        ...
        ]
        ```
        """
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt + sketch

        if "deepseek" in self.model_for_proof:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            "model": self.model_for_sketch,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return self._postprocess_extraction(response.choices[0].message.content)
    
    def _postprocess_extraction(self, formalization):
        # Extract Json from LLM response and convert to dict
        match = re.search(r"```json(.*?)```", formalization, re.DOTALL)
        if match:
            formalization = match.group(1).strip()
        else:
            raise ValueError("No JSON block found in the response.")

        try:
            extracted = json.loads(formalization)
            if not isinstance(extracted, list):
                raise ValueError("Extracted JSON is not a list.")
            for item in extracted:
                if not isinstance(item, dict) or len(item) != 1:
                    raise ValueError(f"Invalid format for item: {item}")
            return extracted
        except json.JSONDecodeError as e:
            raise ValueError(f"Failed to parse extracted JSON: {e}")
    
    def extract_header_from_sketch(self, system_prompt, user_prompt, sketch):
        """
        Using LLM to extract the header from the sketch
        """
        client = self.initialize_openai()

        # Construct the prompt for formalziation
        prompt = user_prompt + sketch

        if "deepseek" in self.model_for_proof:
            messages = [{"role": "user", "content": prompt}]
        else:
            messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ]
        sampling_params = {
            # "model": "google/gemini-2.0-flash-001",
            "model": self.model_for_sketch,
            "max_tokens": self.max_tokens,
        }
        response = client.chat.completions.create(
            messages=messages,
            **sampling_params,
        )
        return self.postprocess_formalization(response.choices[0].message.content)
    
    def lean4_check(self, lean4_scheduler, code):
        # Check the Lean4 code using the Lean4 server scheduler
        request_id_list = lean4_scheduler.submit_all_request(
            [dict(code=code, ast=False, tactics=False)]
        )
        outputs_list = lean4_scheduler.get_all_request_outputs(request_id_list)
        return outputs_list

    def kimina_lean4_check(self, client, code):
        # Check the Lean4 code using the kimina_lean4_check server scheduler
        response = client.verify([{"proof": code, "custom_id": "1"}], timeout=60)

        verification_results = [
            parse_client_response(item) for item in response["results"]
        ]
        return response["results"][0]["response"], verification_results[0]


