# llm_doc.py
"""
Light‑weight wrappers around the two supported chat back‑ends
(vLLM and OpenAI) plus helper utilities.
"""
from __future__ import annotations

import re
from typing import List, Sequence, Tuple

from loguru import logger
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams
from openai import OpenAI


def _first_markdown_block(text: str, outer_fence: str = "```markdown") -> str:
    lines = text.splitlines()
    inside_block = False
    block_lines = []
    for line in lines:
        if line.strip().startswith(outer_fence):
            inside_block = True
            continue
        if inside_block and line.strip().startswith("```"):
            break
        if inside_block:
            block_lines.append(line)
    return "\n".join(block_lines).strip()


def _extract_remove_boxed_content(text: str) -> str:
    """Extracts the content inside the first \boxed{} in the text and removes it from the text."""
    boxed_pattern = r'\\boxed\{([^}]*)\}'
    match = re.search(boxed_pattern, text)
    if match:
        return match.group(1).strip(), text.replace(match.group(0), "").strip()
    return "", text


def _apply_chat_template(
    tokenizer: AutoTokenizer | None,
    messages: list[dict],
    model_name: str | None,
) -> str:
    """Return chat prompt string understood by vLLM."""
    if model_name and "mistral" in model_name:
        # manual ChatML
        result = ""
        for msg in messages:
            role = msg["role"]
            result += f"<|{role}|>\n{msg['content']}<|end|>\n"
        result += "<|assistant|>\n"
        return result
    if tokenizer is None:
        raise ValueError("Tokenizer required to render chat template.")
    return tokenizer.apply_chat_template(messages, add_generation_prompt=True, tokenize=False)


def _check_add_system_prompt(model_name: str | None, input: str | None) -> list[dict]:
    """Check if the system prompt should be added to the input."""
    if  "deepseek" in model_name:
        # manual ChatML
        return [{"role": "user", "content": input}]
    return [{"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": input}]

# ----------------------------------------------------------------------
# Public API
# ----------------------------------------------------------------------

def generate_docs(
    llm: LLM | "OpenAI.chat.completions.Completions",
    tokenizer: AutoTokenizer | None,
    params: SamplingParams | dict,
    prompts: Sequence[str],
    *,
    backend: str,
) -> List[str]:
    """LLM bulk call: user prompts → assistant texts."""
    if backend == "vllm":
        model_name = llm.llm_engine.model_config.model  # type: ignore[attr-defined]
        prompt_strs = [
            _apply_chat_template(tokenizer, _check_add_system_prompt(model_name, p), model_name)
            for p in prompts
        ]
        outs = llm.generate(prompt_strs, params)  # type: ignore[attr-defined]
        return [o.outputs[0].text for o in outs]

    # API Call
    results: List[str] = []
    for p in prompts:
        try:
            resp = llm.create(
                messages=_check_add_system_prompt(params['model'], p),  # type: ignore[call-arg]
                **params,
            )
            results.append(resp.choices[0].message.content)
        except Exception as e:
            logger.warning(f"Generation failed, retrying once: {e}")
            resp = llm.create(
                messages=_check_add_system_prompt(params['model'], p),  # type: ignore[call-arg]
                **params,
            )
            results.append(resp.choices[0].message.content)
    return results


def generate_overview(
    llm, tokenizer, params, prompt: str, *, backend: str
) -> str:
    """Thin wrapper around `generate_docs` for single prompt."""
    return generate_docs(llm, tokenizer, params, prompt, backend=backend)[0]

# ----------------------------------------------------------------------
# Multi‑agent mode (OpenAI only)
# ----------------------------------------------------------------------

def run_multi_agent( llm: "OpenAI.chat.completions.Completions", agent_params: List[dict], prompts: Sequence[str], formals: Sequence, template: str) -> List[str]: 
    """N‑1 formalizer + 1 writer (last entry in agent_params).""" 
    informalizers, writer = agent_params[:-1], agent_params[-1] 
    outputs: List[str] = []
    for user_prompt, formal in zip(prompts, formals):
        # informalizers
        versions = []
        for p in informalizers:
            try:
                resp = llm.create(messages=_check_add_system_prompt(p['model'], user_prompt ), **p)
                versions.append(resp.choices[0].message.content)
            except Exception as e:
                logger.warning(f"Generation failed, retrying once: {e}")
                resp = llm.create(messages=_check_add_system_prompt(p['model'], user_prompt ), **p)
                versions.append(resp.choices[0].message.content)

        joined = "\n\n".join(
            f"<Version_{i+1}>\n{v}\n</Version_{i+1}>" for i, v in enumerate(versions)
        )
        # writer
        writer_prompt = template.format(formal_stm=formal.formal_content, text=joined)
        try:
            writer_resp = llm.create(messages=_check_add_system_prompt(writer['model'], writer_prompt), **writer)
            merged = _first_markdown_block(writer_resp.choices[0].message.content) or versions[0]
        except Exception as e:
            logger.warning(f"Generation failed, retrying once: {e}")
            writer_resp = llm.create(messages=_check_add_system_prompt(writer['model'], writer_prompt), **writer)
            merged = _first_markdown_block(writer_resp.choices[0].message.content) or versions[0]
        outputs.append(merged)
        logger.info(f"Merged doc length {len(merged)} chars")

    return outputs

# ----------------------------------------------------------------------
# Judge feedback (single model)
# ----------------------------------------------------------------------
def generate_judge_feedback( llm, params, prompts: Sequence[str], *, backend: str, ) -> List[Tuple[bool, str]]: 
    """Return list of (accepted?, judge_text). OpenAI only.""" 
    assert backend == "openai", "Judge feedback only via OpenAI for now" 
    results = [] 
    for p in prompts: 
        resp = llm.create(messages=_check_add_system_prompt(params["model"], p), **params) 
        txt = resp.choices[0].message.content
        logger.debug(f"Judge feedback: {txt}") 
        # Extract the boxed content and remove it from the text
        boxed_content, txt = _extract_remove_boxed_content(txt)
        # if it is 0  then it is ok. If it is 1 then it is not ok.
        ok =  True if boxed_content == "0" else False
        results.append((ok, txt)) 
    return results
    

