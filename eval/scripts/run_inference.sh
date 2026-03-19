#!/bin/bash
# Example: Run inference with an open-source model via vllm serve
#
# Step 1: Start vllm server (in a separate terminal or tmux session)
#   vllm serve deepseek-ai/DeepSeek-Prover-V2-7B --port 8000
#
# Step 2: Run this script

MODEL="deepseek-ai/DeepSeek-Prover-V2-7B"
DATASET="../LeanPhysBench/LeanPhysBench_v0.json"
CKPT_DIR="./checkpoints"
OUTPUT_DIR="./output"

# Without PhysLib documentation
python ../prove_writer.py \
    --backend api \
    --base_url http://localhost:8000/v1 \
    --model "$MODEL" \
    --dataset_path "$DATASET" \
    --proof_num 16 \
    --temperature 0.8 \
    --top_p 0.95 \
    --max_tokens 14000 \
    --ckpt_path "$CKPT_DIR" \
    --save_path "$OUTPUT_DIR" \
    --dataset_workers 4 \
    --attempt_workers 4

# With PhysLib documentation (add --use_lib and --physlib_prompt)
# python ../prove_writer.py \
#     --backend api \
#     --base_url http://localhost:8000/v1 \
#     --model "$MODEL" \
#     --dataset_path "$DATASET" \
#     --use_lib \
#     --physlib_prompt ../prompts/PhysLib_Prompt_v1.txt \
#     --proof_num 16 \
#     --ckpt_path "$CKPT_DIR" \
#     --save_path "$OUTPUT_DIR"
