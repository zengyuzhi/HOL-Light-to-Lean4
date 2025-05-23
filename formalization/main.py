import argparse
import os

from pipeline import FormalizationPipeline
from prompts import *
from loguru import logger
from client import Lean4Client
from common import (
    set_logger,
    save_file,
    setup_results_directory,
    load_documentation,
    load_txt_file,
)


def parse_args():
    parser = argparse.ArgumentParser(description="Formalization Pipeline")
    parser.add_argument(
        "--model_for_sketch",
        type=str,
        required=True,
        help="Model name or Path to the model",
    )
    parser.add_argument(
        "--model_for_proof",
        type=str,
        required=True,
        help="Model name or Path to the model",
    )
    parser.add_argument(
        "--docs_md_path",
        type=str,
        default="",
        help="Path to the documentation markdown file",
    )
    parser.add_argument(
        "--gpu_utilization", type=float, default=0.5, help="GPU utilization for vLLM"
    )
    parser.add_argument(
        "--max_tokens",
        type=int,
        default=8192,
        help="Maximum number of tokens for generation",
    )
    parser.add_argument(
        "--temperature", type=float, default=0.7, help="Temperature for sampling"
    )
    parser.add_argument(
        "--top_p", type=float, default=0.9, help="Top-p sampling parameter"
    )
    parser.add_argument(
        "--sketch_refinement_times",
        type=int,
        default=3,
        help="Number of times to refine the sketch using error messages",
    )
    parser.add_argument(
        "--formalization_refinement_times",
        type=int,
        default=3,
        help="Number of times to refine the formalization using error messages",
    )
    parser.add_argument(
        "--skip_formalization",
        action="store_true",
        help="If set, stop after generating and verifying the sketch.",
    )
    parser.add_argument(
        "--use_own_sketch",
        action="store_true",
        help="Use own sketch instead of generating one.",
    )
    parser.add_argument(
        "--sketch_path",
        type=str,
        default="",
        help="Path to the sketch file if using own sketch.",
    )
    return parser.parse_args()


def generate_and_verify_sketch(
    pipeline, lean_client, docs_md: str, result_dir: str, sketch_refinements: int
):
    """
    Generate a sketch, verify with Lean, and refine if necessary.
    Returns final sketch, proof states, and refinement count.
    """
    logger.info("Starting sketch generation")
    # Raw sketch
    sketch = pipeline.generate_sketch(
        SYSTEM_PROMPT, USER_PROMPT_FOR_SKETCH, LEAN4_DEFAULT_HEADER, docs_md
    )
    save_file(os.path.join(result_dir, "raw_sketch.txt"), sketch)
    logger.debug(f"Raw sketch content:\n{sketch}")

    sketch_processed = pipeline.postprocess_sketch(sketch)
    logger.debug(f"Post-processed sketch content:\n{sketch_processed}")
    feedback, result = pipeline.kimina_lean4_check(lean_client, sketch_processed)
    logger.info(f"Initial sketch verification result: {result['is_valid_with_sorry']}")

    # Refine sketch if needed
    count = 0
    while not result["is_valid_with_sorry"] and count < sketch_refinements:
        count += 1
        logger.info(f"Refinement attempt {count}...")
        # log errors
        err = feedback["messages"]
        append_content = f"Refinement {count} errors:\n{sketch_processed}\n{err}\n---\n"
        save_file(
            os.path.join(result_dir, "sketch_with_errors.txt"),
            append_content,
            append=True,
        )
        logger.debug(f"Logged sketch errors: {err}")

        refined = pipeline.refine_sketch(
            SYSTEM_PROMPT,
            USER_PROMPT_FOR_SKETCH_REFINEMENT,
            docs_md,
            sketch_processed,
            str(err),
        )
        sketch_processed = pipeline.postprocess_sketch(refined)
        feedback, result = pipeline.kimina_lean4_check(lean_client, sketch_processed)
        logger.info(
            f"Sketch verification after refinement {count}: {result['is_valid_with_sorry']}"
        )

    if not result["is_valid_with_sorry"]:
        raise ValueError("Sketch failed after max refinements")
    else:
        logger.info("Sketch passed verification after refinements")

    # save final sketch
    save_file(os.path.join(result_dir, "final_sketch.txt"), sketch_processed)
    proof_states = str(feedback.get("sorries", ""))
    return sketch_processed, proof_states, count


def generate_and_verify_formalizations(
    pipeline,
    lean_client,
    docs_list: dict,
    sketch: str,
    result_dir: str,
    form_refinements: int,
    skip: bool,
    model_for_sketch: str,
):
    """
    Iterate over statements extracted from sketch, generate proofs,
    verify with Lean, refine, and save results.
    """
    sketch_entries = pipeline.extract_stm_from_sketch(
        SYSTEM_PROMPT, USER_PROMPT_FOR_DEPS_EXT, sketch
    )
    # Save the sketch entries to a jsonl file
    save_file(os.path.join(result_dir, "sketch_entries.jsonl"), sketch_entries)
    logger.info(f"Found {len(sketch_entries)} statements to formalize.")

    LEAN4_DEFAULT_HEADER = pipeline.extract_header_from_sketch(
        SYSTEM_PROMPT, USER_PROMPT_FOR_HEADER, sketch
    ).strip()
    logger.info(f"Extracted header from sketch: \n{LEAN4_DEFAULT_HEADER}")

    previous_code = LEAN4_DEFAULT_HEADER + "\n\n"
    deps_str = ""

    for idx, entry in enumerate(sketch_entries, start=1):
        name, lean_stmt = next(iter(entry.items()))
        
        # Skip if the statement is a definition
        if 'theorem'not in lean_stmt:
            previous_code += lean_stmt + "\n\n"
            logger.info(f"Skipping definition statement {idx}: {name}")
            continue
        
        logger.info(f"Formalizing statement {idx}: {name}")

        # assemble documentation snippet
        md_text = ""
        for key, block in docs_list.items():
            if name in key:
                for sec_key, sec_val in block.items():
                    if sec_key not in [
                        "Mathematical insight",
                        "Porting notes",
                        "Dependencies",
                    ]:
                        md_text += f"{sec_key}\n{sec_val}\n\n"
        logger.debug(f"Documentation snippet for '{name}':\n{md_text}")

        # generate proof
        proof = pipeline.generate_one_proof(
            SYSTEM_PROMPT, USER_PROMPT_FOR_FORMALIZATION, md_text, lean_stmt, deps_str
        )
        proof_processed = pipeline.postprocess_formalization(proof)
        logger.debug(f"Generated formalization for '{name}':\n{proof_processed}")

        # verify proof
        codes = previous_code + proof_processed.strip()
        logger.debug(f"Codes for verification:\n{codes}")
        feedback, result = pipeline.kimina_lean4_check(lean_client, codes)
        # errors, _ = filter_response_messages(
        #     feedback, len(previous_code.splitlines()) - 2
        # )
        logger.info(
            f"Formalization verification result for '{name}': {result['is_valid_with_sorry']}"
        )

        ref_count = 0
        if not result['is_valid_with_sorry']:
            append_content = f"Formalization errors for '{name}':\n{proof_processed}\n{feedback}\n---\n"
            save_file(
                os.path.join(result_dir, "formalization_with_errors.txt"),
                append_content,
                append=True,
            )

        # refine on errors
        while ref_count < form_refinements and not result['is_valid_with_sorry']:
            ref_count += 1
            logger.info(f"Refinement {ref_count} for statement {idx}")
            refined = pipeline.fix_formalization(
                SYSTEM_PROMPT,
                USER_PROMPT_FOR_FORMALIZATION_REFINEMENT,
                proof_processed,
                str(feedback),
            )
            proof_processed = pipeline.postprocess_formalization(refined)
            logger.debug(
                f"Refined formalization content for '{name}':\n{proof_processed}"
            )

            codes = previous_code + proof_processed.strip()
            feedback, result = pipeline.kimina_lean4_check(lean_client, codes)
            # errors, _ = filter_response_messages(
            #     feedback, len(previous_code.splitlines()) - 2
            # )

            if not result['is_valid_with_sorry']:
                append_content = f"Stmt {idx} refinement {ref_count} errors:\n{proof_processed}\n{feedback}\n---\n"
                save_file(
                    os.path.join(result_dir, "formalization_with_errors.txt"),
                    append_content,
                    append=True,
                )

        # if still error, add sorries
        if not result['is_valid_with_sorry']:
            informal_proof_text = ""
            for key, block in docs_list.items():
                if name in key:
                    for sec_key, sec_val in block.items():
                        if sec_key in ["Informal proof"]:
                            informal_proof_text += f"{sec_key}\n{sec_val}\n\n"
            logger.info(f"Adding sorries to formalization for '{name}'")
            sorried = pipeline.fix_formalization_with_sorries(
                SYSTEM_PROMPT, USER_PROMPT_FOR_SORRY, proof_processed, str(feedback), informal_proof_text
            )
            proof_processed = pipeline.postprocess_formalization(sorried)

        # save success
        previous_code += proof_processed.strip() + "\n\n"
        deps_str += lean_stmt + "\n\n"
        save_file(os.path.join(result_dir, "formalization.txt"), previous_code)

    # record flags
    flags = {
        "model_name": model_for_sketch,
        "formalization_statements": len(sketch_entries),
    }
    save_file(
        os.path.join(result_dir, "success_flags.jsonl"), f"{flags}\n", append=True
    )


def main():
    args = parse_args()
    set_logger(verbose=False)
    logger.info(f"Starting the formalization pipeline with args {args}")

    result_dir = os.path.join(
        "results",
        os.path.splitext(os.path.basename(args.docs_md_path))[0],
        os.path.basename(args.model_for_sketch),
    )
    setup_results_directory(result_dir)

    pipeline = FormalizationPipeline(
        model_for_sketch=args.model_for_sketch,
        model_for_proof=args.model_for_proof,
        gpu_utilization=args.gpu_utilization,
        max_tokens=args.max_tokens,
        temperature=args.temperature,
        top_p=args.top_p,
    )
    logger.debug(
        f"Initialized FormalizationPipeline with sketch model {args.model_for_sketch} and proof model {args.model_for_proof}"
    )

    lean_client = Lean4Client(base_url="http://127.0.0.1:12332")
    logger.info("Connected to Lean4 scheduler at http://127.0.0.1:12332")

    docs_md, docs_list = load_documentation(args.docs_md_path)

    try:
        if not args.use_own_sketch:
            sketch, proof_states, sketch_ref_count = generate_and_verify_sketch(
                pipeline, lean_client, docs_md, result_dir, args.sketch_refinement_times
            )
            logger.info(f"Sketch finished with {sketch_ref_count} refinement(s)")
        else:
            logger.info("Using own sketch")
            sketch = load_txt_file(args.sketch_path)

        if not args.skip_formalization:
            generate_and_verify_formalizations(
                pipeline,
                lean_client,
                docs_list,
                sketch,
                result_dir,
                args.formalization_refinement_times,
                args.skip_formalization,
                args.model_for_sketch,
            )
    finally:
        logger.info("DONE!")


if __name__ == "__main__":
    main()
