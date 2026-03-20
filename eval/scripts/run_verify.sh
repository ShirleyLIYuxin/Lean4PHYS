#!/bin/bash
# Example: Verify proofs against PhysLib_v1

MODEL_NAME="DeepSeek-Prover-V2-7B"
CKPT_DIR="./checkpoints/${MODEL_NAME}-num16-0-200"
PROJECT_DIR="../PhysLib_v1"

python ../verify.py \
    --checkpoint_dir "$CKPT_DIR" \
    --project_dir "$PROJECT_DIR" \
    --max_workers 16 \
    --verify_workers 16 \
    --max_heartbeats 10000000 \
    --lib_version v1

# For PhysLib_v2 verification:
# python ../verify.py \
#     --checkpoint_dir "$CKPT_DIR" \
#     --project_dir ../PhysLib_v2 \
#     --max_workers 16 \
#     --lib_version v2
