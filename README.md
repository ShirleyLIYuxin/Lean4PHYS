# Lean4Physics: Comprehensive Reasoning Framework for College-level Physics in Lean4

![Lean4PHYS](image/Lean4PHYS.png)

## Introduction
We present **Lean4PHYS**, a comprehensive reasoning framework for college-level physics problems in Lean4. To establish a solid foundation for formal reasoning in physics, **Lean4PHYS** launches *PhysLib*, a repository containing fundamental unit systems and essential theorems to formulate physics proofs in Lean4. It will be community-driven and long-term maintained. **Lean4PHYS** also includes *LeanPhysBench*, a college-level benchmark for evaluating LLMs' Lean4 formal physics reasoning capability. It contains 200 hand-crafted and peer-reviewed Lean4 theorem statements formalized from university textbooks and physics competition problems. Based on the *PhysLib* and *LeanPhysBench* we composed in Lean4PHYS, we perform exhaustive experiments of baseline results using major expert Math provers and state-of-the-art closed-source models, and provide an analysis of their performance. In the experiment, we identify that most expert provers do not outperform general models as they did in the math domain. This suggests potential overfitting to the math domain rather than learning formal reasoning for formal provers. We also conduct a comprehensive experiment showing that, with *PhysLib* in the context, LLMs' performance on *LeanPhysBench* increases by **11.90%** on average, proving the effectiveness of our repository in assisting LLMs in solving the Lean4 physics problem. To the best of our knowledge, we are the first study to provide a physics benchmark in Lean4.

## Useful Links
- Please see the details in our full paper: [arxiv](https://arxiv.org/abs/2510.26094)

- Please see the documentation of *PhysLib* : [document](https://yuxin.li/Lean4PHYS_web/docs/)

## LICENSE and Usage
The PhysLib library is licensed with Apache-2.0, of which parts come from [teorth_analysis](https://github.com/teorth/analysis) , aligned with the origin repository. 
The LeanPhysBench dataset is licensed with CC BY-NC 4.0, aligned with the copyright protection range of the source materials. Additionally, the dataset may not be used to train, fine-tune, or evaluate any machine learning or AI models, regardless of whether the use is commercial or non-commercial. 

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
└── results/                         # Reference results (16 JSON files)
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
    --lib_version v1 \
    --max_workers 16
```

For PhysLib v2 verification (auto-replaces `PHYSlib` → `PhysLib` in imports):
```bash
python eval/verify.py \
    --checkpoint_dir ./checkpoints/<model-name>/ \
    --project_dir ./PhysLib_v2 \
    --lib_version v2
```

### 4. Evaluation: Compute pass@N

```bash
python eval/evaluate.py \
    --verified_dir ./checkpoints/<model-name>_verified/ \
    --output results/<model-name>.json
```

## News
[2026.3.19] 🔉 We have released the evaluation pipeline for *LeanPhysBench*, including inference, verification, and evaluation scripts. Reference results for 8 models are available in `results/`.

[2026.3.5] 🔉 We have released the documentation for our enriched version of *PhysLib*. We will continue to improve the library and contributions from the community are more than welcome!

[2026.3.2] 🔉 We have uploaded our initial version of *PhysLib* and *LeanPhysBench*. A structured documentation of *PhysLib*, enriched version of *PhysLib*, and the evaluation pipeline of *LeanPhysBench* will coming soon.

## Citing Us
If you found our project useful, please cite us as: 
```
@article{li2025lean4physics,
  title={Lean4Physics: Comprehensive Reasoning Framework for College-level Physics in Lean4},
  author={Li, Yuxin and Liu, Minghao and Wang, Ruida and Ji, Wenzhao and He, Zhitao and Pan, Rui and Huang, Junming and Zhang, Tong and Fung, Yi R},
  year={2025},
  eprint={2510.26094},
  archivePrefix={arXiv},
  primaryClass={cs.AI},
  url={https://arxiv.org/abs/2510.26094}
}
```

## Contact Information 
For help or issues using Lean4PHYS, you can submit a GitHub issue, send messages in the [Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/PhysLib/with/553660982), or send emials to Yuxin Li（ylinq@connect.ust.hk). 
