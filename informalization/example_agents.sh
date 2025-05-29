#!/bin/bash
INPUT_PATH="./categorized_100/tiny/sqrt.ml"

MODEL_A="deepseek/deepseek-chat-v3-0324"
MODEL_B="anthropic/claude-3.7-sonnet"
MODEL_C="openai/gpt-4.1-mini"

MAX_TOKENS=16384

OUTPUT_DIR="./comparison_result/approach2/tiny"

TEMPERATURE=0.7
TOP_P=0.9
BACKEND="openai" # BACKEND="vllm"


python pipeline.py \
  --input_path "$INPUT_PATH" \
  --model "$MODEL_A" "$MODEL_B" "$MODEL_C" \
  --judge_model "$MODEL_JUDGE" \
  --max_tokens "$MAX_TOKENS" \
  --output_dir "$OUTPUT_DIR" \
  --temperature "$TEMPERATURE" \
  --top_p "$TOP_P" \
  --backend "$BACKEND" \
  --verbose \
  --use_agents \

echo "done"