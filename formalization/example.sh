#!\bin\bash
MODEL_1="deepseek/deepseek-chat-v3-0324"
MODEL_2="deepseek/deepseek-prover-v2"

MD_PATH="./docs/tiny/claude-3.7-sonnet/sqrt.md"

MAX_TOKEN=16582

# SKETCH_PATH="./results/sqrt/deepseek-chat-v3-0324/final_sketch.txt"

# This script is used to run the Lean4 formalization of the example
python main.py \
    --model_for_sketch "$MODEL_1" \
    --model_for_proof "$MODEL_2" \
    --docs_md_path "$MD_PATH"\
    --max_tokens "$MAX_TOKEN"\
    --sketch_refinement_times 3 \
    --formalization_refinement_times 1 \
    # --use_own_sketch \
    # --sketch_path "$SKETCH_PATH" \