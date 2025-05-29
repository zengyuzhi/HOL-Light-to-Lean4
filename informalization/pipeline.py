# pipeline.py
"""
Generate Markdown documentation for HOL Light files.

High‑level flow
---------------
1.  Walk *.ml files under the given path.
2.  For each file
      • parse overview, imports, statements
      • generate overview paragraph
      • generate per‑theorem docs (single‑ or multi‑agent)
      • optionally run a judge pass and patch docs
      • write a tidy Markdown file
"""

import argparse
import os
import sys
from pathlib import Path
from typing import Iterable, Sequence, Tuple

import torch
from dotenv import load_dotenv
from loguru import logger
from transformers import AutoTokenizer
from vllm import LLM, SamplingParams

from hollight_parser import HOLFile, parse_hol_file
from hol_dependency_extractor import deps_from_text, restrict_index
from llm_doc import (
    generate_docs,
    generate_judge_feedback,
    generate_overview,
    run_multi_agent,
)

# --------------------------------------------------------------------------- #
# Constants & helpers
# --------------------------------------------------------------------------- #
CACHE_FILE = Path("./HOL_Light_deps/.hol_index.pkl")
load_dotenv()

def walk_hol_files(root: Path) -> Iterable[Path]:
    """Yield every `.ml` file under *root* (recursive)."""
    if root.is_file() and root.suffix == ".ml":
        yield root
    elif root.is_dir():
        yield from root.rglob("*.ml")

def configure_logging(verbose: bool) -> None:
    """
    Set the logging level of loguru.
    The effect of this function is global, and it should
    be called only once in the main function
    """
    logger.remove()
    if verbose:
        logger.add(sys.stderr, level="DEBUG")
    else:
        logger.add(sys.stderr, level="INFO")

# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Generate informal documentation for HOL Light theorems"
    )
    p.add_argument("--input_path", help="A .ml file or directory containing them")
    p.add_argument(
        "--model",
        nargs="+",
        required=True,
        help="Model name(s) or path(s). For single agent, if you want to use other model as judge model, you should use --judge_model, otherwise the judge model is same as the --model. For multi‑agents, the last entry is the judge model.",
    )
    p.add_argument(
        "--judge_model",
        help=(
            "OpenAI model used for the judge pass. "
            "If omitted, defaults to the generator model (single‑agent) "
            "or to the last entry in --model (multi‑agents)."
        )
    )
    p.add_argument(
        "--backend",
        choices=("vllm", "openai"),
        default="openai",
        help="Which LLM backend to use. For vllm, only support one model for generation documentation.",
    )
    p.add_argument("--max_tokens", type=int, default=800)
    p.add_argument("--gpu_utilization", type=float, default=0.5)
    p.add_argument("--temperature", type=float, default=0.7)
    p.add_argument("--top_p", type=float, default=0.9)

    # Pipeline options
    p.add_argument("--use_agents", action="store_true", help="Enable multi‑llms generation mode.")
    p.add_argument("--use_judge", action="store_true", help="Enable judge refinement")

    # Templates
    p.add_argument("--output_dir", default="docs")
    p.add_argument("--template_path_overview", default="./templates/template_overview.txt")
    p.add_argument("--template_path_stm", default="./templates/template_stm.txt")
    p.add_argument("--template_path_stm_improve", default="./templates/template_stm_improve.txt")
    p.add_argument("--template_path_judger", default="./templates/template_judger.txt")
    p.add_argument("--template_path_multi_LLMs_writer", default="./templates/template_multi_llms_final_writer.txt")
    p.add_argument("--verbose", action="store_true")
    return p.parse_args()

# --------------------------------------------------------------------------- #
# Back‑end construction
# --------------------------------------------------------------------------- #
def init_vllm(
    model_name: str,
    *,
    gpu_util: float,
    max_tokens: int,
    temperature: float,
    top_p: float,
) -> Tuple[LLM, SamplingParams, AutoTokenizer]:
    """Return (LLM, sampling parameters, tokenizer) for vLLM backend."""
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    engine_options = dict(
        model=model_name,
        tokenizer=model_name,
        gpu_memory_utilization=gpu_util,
        tensor_parallel_size=torch.cuda.device_count(),
        enable_prefix_caching=True,
        swap_space=16,
    )

    # Model‑specific tweaks
    if "mistral" in model_name:
        engine_options.update(tokenizer_mode="mistral", load_format="mistral")
    if "awq" in model_name:
        engine_options["quantization"] = "awq"

    llm = LLM(**engine_options)
    sampling = SamplingParams(
        max_tokens=max_tokens, temperature=temperature, top_p=top_p
    )
    return llm, sampling, tokenizer


def init_openai(model_names: Sequence[str], *, max_tokens: int):
    """Return (chat client, per‑agent parameter list)."""
    from openai import OpenAI
    
    client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"), base_url=os.getenv("OPENAI_API_BASE"))
    params_list = [{"model": m, "max_tokens": max_tokens} for m in model_names]
    return client.chat.completions, params_list

# --------------------------------------------------------------------------
# Markdown writer
# --------------------------------------------------------------------------

def write_markdown(
    path: Path,
    file_info: HOLFile,
    overview_md: str,
    theorem_mds: Sequence[str],
) -> None:
    """Create a Markdown file with overview + theorem docs."""
    with path.open("w", encoding="utf‑8") as f:
        f.write(f"# {path.stem}.ml\n\n")
        f.write("## Overview\n\n")
        f.write(f"Number of statements: {len(file_info)}\n\n")
        f.write(overview_md + "\n\n")

        for doc, stm in zip(theorem_mds, file_info.statements):
            formal_block = f"```ocaml\n{stm.formal_content.strip()}\n```"
            f.write(f"## {stm.name}\n\n")
            f.write(doc.replace("<HOL_LIGHT_STATEMENT_PLACEHOLDER>", formal_block))
            f.write("\n\n---\n\n")

# --------------------------------------------------------------------------
# Main driver
# --------------------------------------------------------------------------

def main(
        input_path: str,
        model: Sequence[str],
        judge_model: str,
        backend: str,
        max_tokens: int,
        gpu_utilization: float,
        temperature: float,
        top_p: float,
        use_agents: bool,
        use_judge: bool,
        output_dir: str,
        template_path_overview: str,
        template_path_stm: str,
        template_path_stm_improve: str,
        template_path_judger: str,
        template_path_multi_LLMs_writer: str,
        verbose: bool,
        ) -> None:
    configure_logging(verbose)

    source_root = Path(input_path).expanduser()
    hol_files = list(walk_hol_files(source_root))
    if not hol_files:
        logger.warning("No .ml files found – exiting.")
        return

    # Read templates once
    overview_tpl = Path(template_path_overview).read_text(encoding="utf‑8").strip()
    stm_tpl = Path(template_path_stm).read_text(encoding="utf‑8").strip()
    judger_tpl = (Path(template_path_judger).read_text(encoding="utf‑8").strip() if use_judge else None)
    improve_tpl = (Path(template_path_stm_improve).read_text(encoding="utf‑8").strip() if use_judge else None)
    multi_llm_writer_tpl = (Path(template_path_multi_LLMs_writer).read_text(encoding="utf‑8").strip() if use_agents else None)

    # Initialise backend
    if backend == "vllm":
        llm, sampler, tokenizer = init_vllm(
            model[0],
            gpu_util=gpu_utilization,
            max_tokens=max_tokens,
            temperature=temperature,
            top_p=top_p,
        )
        agent_params = sampler
    else:  # API call
        llm, _ = init_openai(model, max_tokens=max_tokens)
        if backend == "openai":
            # -- Single‑agent generation (default) ----------------------
            if not use_agents:
                informalizer_params = {"model": model[0], "max_tokens": max_tokens}

                judger_params = {"model": judge_model or model[0], "max_tokens": max_tokens}

            # -- Multi‑agent generation ---------------------------------
            else:
                # informalizer models  = everything in --model except the last one
                # writer model    = last entry in --model
                informalizer_params = [
                    {"model": m, "max_tokens": max_tokens} for m in model[:-1]
                ]

                # writer model
                writer_params = {"model": model[-1], "max_tokens": max_tokens}

                # run_multi_agent expects informalizer *plus* writer in a single list
                agent_params = informalizer_params + [writer_params]

        else: # backend == vllm
            writer_params = agent_params       # vLLM unchanged
            judger_params  = None           # vLLM has no judge
        tokenizer = None

    # Dependency index
    if not CACHE_FILE.exists():
        raise FileNotFoundError(
            f"Dependency index {CACHE_FILE} missing. Build it first."
        )
    import pickle

    dep_index = pickle.loads(CACHE_FILE.read_bytes())

    # Output root
    out_root = Path(output_dir).expanduser()
    out_root.mkdir(parents=True, exist_ok=True)

    # ------------------------------------------------------------------
    # Loop over files
    # ------------------------------------------------------------------
    for ml_path in hol_files:
        rel_path = ml_path.relative_to(source_root)
        logger.info(f"Processing {ml_path}")

        file_info = parse_hol_file(ml_path)
        current_hol_file = ml_path.name
        logger.info(f"Current HOL file: {current_hol_file}")
        idx_restricted = restrict_index(dep_index, file_info.imports + [current_hol_file])
        logger.info(f"{len(file_info.statements)} numbers of statement needed to be processed for {ml_path.name}")

        # 1. overview paragraph
        logger.info("Generating overview")
        overview_prompt = overview_tpl.format(
            file_name=ml_path.name,
            imports=file_info.imports,
            comment=file_info.overview,
        )
        if use_agents and backend == "openai":
            overview_md = generate_overview(
                llm, tokenizer, informalizer_params[0], [overview_prompt], backend=backend
            )
        else:
            overview_md = generate_overview(
                llm, tokenizer, informalizer_params, [overview_prompt], backend=backend
            )

        # 2. theorem docs
        logger.info("Generating theorem docs")
        stmt_prompts = [
            stm_tpl.format(
                name=stm.name,
                content=stm.formal_content,
                comment=stm.pre_comment or "",
                # Truncate the name from the formal content
                deps=str(deps_from_text(stm.formal_content.split(stm.name, 1)[-1].strip(), idx_restricted)),
            )
            for stm in file_info.statements
        ]
        # logger.info(f"Stms prompt: {stmt_prompts}")
        
        if use_agents and backend == "openai":
            theorem_mds = run_multi_agent(
                llm, agent_params, stmt_prompts, file_info.statements, multi_llm_writer_tpl
            )
        else:
            theorem_mds = generate_docs(
                llm, tokenizer, informalizer_params, stmt_prompts, backend=backend
            )

        # 3. judge refinement (OpenAI only for now)
        if use_judge:
            logger.info("Generating judgement")
            logger.info("Using judge model: " + judge_model or model[0])
            judge_prompts = [
                judger_tpl.format(formal_stm=stm.formal_content, doc=doc)
                for stm, doc in zip(file_info.statements, theorem_mds)
            ]
            feedback = generate_judge_feedback(
                llm, judger_params, judge_prompts, backend=backend
            )
            # Patch docs that passed the judge
            idx_needing_fix: list[int] = []
            prompts_to_fix: list[str] = []
            for idx, (is_ok, judge_txt) in enumerate(feedback):
                stmt_name = file_info.statements[idx].name

                if is_ok:
                    # Accepted – nothing to do.
                    logger.info(f"[JUDGE] {stmt_name} accepted ✓")
                    continue

                # Rejected – we must produce a revised version.
                # logger.debug(f"[JUDGE] {stmt_name} rejected: {judge_txt}")
                logger.info(f"[JUDGE] {stmt_name} rejected ✗")

                improve_prompt = improve_tpl.format(
                    formal_stm=file_info.statements[idx].formal_content,  # formal statement
                    doc=theorem_mds[idx],                       # current (flawed) doc
                    judge_doc=judge_txt,                       # judge’s explanation of the error
                )

                idx_needing_fix.append(idx)
                prompts_to_fix.append(improve_prompt)

            if prompts_to_fix:        # may be empty if everything was accepted
                logger.info("Generating improved docs")
                improved_docs = generate_docs(
                    llm, tokenizer, informalizer_params, prompts_to_fix, backend=backend
                )

                for idx, new_doc in zip(idx_needing_fix, improved_docs):
                    theorem_mds[idx] = new_doc    

            # Log the judge feedback
            accepted_count = sum(is_ok for is_ok, _ in feedback)
            file_total     = len(feedback)
            logger.info(f"[JUDGE] {accepted_count}/{file_total} statements accepted for {ml_path.name}")

        # 4. write output
        model_tag = model[-1] if use_agents else model[0]
        output_dir = out_root / rel_path.parent / os.path.basename(model_tag)
        output_dir.mkdir(parents=True, exist_ok=True)
        write_markdown(output_dir / f"{ml_path.stem}.md", file_info, overview_md, theorem_mds)
        logger.info(f"✓ {output_dir / (ml_path.stem + '.md')}")

if __name__ == "__main__":
    # Parse command line arguments
    args = _build_parser()
    main(
        input_path=args.input_path,
        model=args.model,
        judge_model=args.judge_model,
        backend=args.backend,
        max_tokens=args.max_tokens,
        gpu_utilization=args.gpu_utilization,
        temperature=args.temperature,
        top_p=args.top_p,
        use_agents=args.use_agents,
        use_judge=args.use_judge,
        output_dir=args.output_dir,
        template_path_overview=args.template_path_overview,
        template_path_stm=args.template_path_stm,
        template_path_stm_improve=args.template_path_stm_improve,
        template_path_judger=args.template_path_judger,
        template_path_multi_LLMs_writer=args.template_path_multi_LLMs_writer,
        verbose=args.verbose,
    )
