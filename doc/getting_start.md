## Repository Structure

```
Lean4PHYS/
├── PhysLib_v1/                     # PHYSlib (Lean 4.20.0 + Mathlib 4.20.0)
│   ├── lakefile.lean
│   ├── lean-toolchain
│   ├── PHYSlib.lean
│   └── PHYSlib/                    # 13 source files
├── PhysLib_v2/                     # PhysLib (Lean 4.28.0 + Mathlib 4.28.0)
│   ├── lakefile.lean
│   ├── lean-toolchain
│   ├── PhysLib.lean
│   └── PhysLib/                    # 13 source files
├── LeanPhysBench/
│   ├── LeanPhysBench_v0.json       # 200 problems
│   └── LICENSE                      # CC BY-NC 4.0
├── eval/
│   ├── prove_writer.py              # Unified inference (API + vLLM)
│   ├── verify.py                    # Lean 4 verification
│   ├── evaluate.py                  # pass@N statistics
│   ├── backends/
│   │   ├── api_backend.py           # OpenAI-compatible API backend
│   │   └── vllm_backend.py          # vLLM direct backend
│   ├── prompts/
│   │   ├── prompt_builder.py        # Model-agnostic prompt construction
│   │   ├── model_configs.py         # Per-model configurations
│   │   ├── PhysLib_Prompt_v1.txt       # v1 library documentation
│   │   └── PhysLib_Prompt_v2.txt       # v2 library documentation
│   ├── utils/
│   │   └── utils.py
│   ├── scripts/
│   │   ├── run_inference.sh
│   │   ├── run_verify.sh
│   │   └── slurm_launcher.py
│   └── requirements.txt
└── results/                         # Reference results (16 JSON files) (Not released Yet)
```

## Evaluation Pipeline

### Prerequisites

```bash
pip install -r eval/requirements.txt
# For vLLM direct mode: pip install vllm
```

### 1. Build PhysLib

```bash
cd PhysLib_v1 && lake exe cache get && lake build
# or
cd PhysLib_v2 && lake exe cache get && lake build
```

### 2. Inference: Generate Proofs

```bash
# Open-source model via vLLM direct mode
python eval/prove_writer.py \
    --backend vllm \
    --model deepseek-ai/DeepSeek-Prover-V2-7B \
    --dataset_path LeanPhysBench/LeanPhysBench_v0.json \
    --proof_num 16

# Open-source model via API (start vllm serve first)
vllm serve deepseek-ai/DeepSeek-Prover-V2-7B --port 8000
python eval/prove_writer.py \
    --backend api \
    --base_url http://localhost:8000/v1 \
    --model deepseek-ai/DeepSeek-Prover-V2-7B \
    --dataset_path LeanPhysBench/LeanPhysBench_v0.json \
    --proof_num 16

# Closed-source model
python eval/prove_writer.py \
    --backend api \
    --base_url https://api.openai.com/v1 \
    --api_key $OPENAI_API_KEY \
    --model gpt-4o \
    --dataset_path LeanPhysBench/LeanPhysBench_v0.json \
    --proof_num 16

# With PhysLib documentation in prompt (add --use_lib)
python eval/prove_writer.py \
    --backend api --base_url http://localhost:8000/v1 \
    --model deepseek-ai/DeepSeek-Prover-V2-7B \
    --dataset_path LeanPhysBench/LeanPhysBench_v0.json \
    --use_lib --physlib_prompt eval/prompts/PhysLib_Prompt_v1.txt \
    --proof_num 16
```

### 3. Verification: Check Proofs in Lean 4

```bash
python eval/verify.py \
    --checkpoint_dir ./checkpoints/<model-name>/ \
    --project_dir ./PhysLib_v1 \
    --output_dir ./checkpoints/<model-name>_verified/ \
    --lib_version v1 \
    --max_workers 16
```

For PhysLib v2 verification (auto-replaces `PHYSlib` → `PhysLib` in imports):
```bash
python eval/verify.py \
    --checkpoint_dir ./checkpoints/<model-name>/ \
    --project_dir ./PhysLib_v2 \
    --output_dir ./checkpoints/<model-name>_verified/ \
    --lib_version v2
```

### 4. Evaluation: Compute pass@N

```bash
python eval/evaluate.py \
    --verified_dir ./checkpoints/<model-name>_verified/ \
    --output results/<model-name>.json
```
