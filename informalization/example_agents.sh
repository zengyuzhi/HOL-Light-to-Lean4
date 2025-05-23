#!/bin/bash
INPUT_PATH="./categorized_100/tiny/sqrt.ml"

MODEL_A="anthropic/claude-3.7-sonnet"
MODEL_B="openai/gpt-4.1-mini"
MODEL_C="deepseek/deepseek-chat-v3-0324"

MAX_TOKENS=16384

OUTPUT_DIR="./test2"

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