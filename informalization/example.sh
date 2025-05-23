#!/bin/bash
INPUT_PATH="./categorized_100/tiny/sqrt.ml"

MODEL="anthropic/claude-3.7-sonnet"

MODEL_JUDGE="openai/gpt-4.1-mini"

MAX_TOKENS=16384

OUTPUT_DIR="./docs/tiny"

TEMPERATURE=0.7
TOP_P=0.9
BACKEND="openai" # BACKEND="vllm"


python pipeline.py \
  --input_path "$INPUT_PATH" \
  --model "$MODEL" \
  --judge_model "$MODEL_JUDGE" \
  --max_tokens "$MAX_TOKENS" \
  --output_dir "$OUTPUT_DIR" \
  --temperature "$TEMPERATURE" \
  --top_p "$TOP_P" \
  --backend "$BACKEND" \
  --use_judge \
  --verbose \

echo "done"