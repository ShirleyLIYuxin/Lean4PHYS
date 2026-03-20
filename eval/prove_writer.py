#!/usr/bin/env python3
"""
Unified inference entry point for LeanPhysBench proof generation.

Supports two backends:
  --backend api   : OpenAI-compatible API (works with vllm serve, OpenAI, etc.)
  --backend vllm  : vLLM direct mode (no HTTP server, maximum throughput)

Examples:
  # Open-source model via vllm serve
  vllm serve deepseek-ai/DeepSeek-Prover-V2-7B --port 8000
  python prove_writer.py --backend api --base_url http://localhost:8000/v1 \\
    --model deepseek-ai/DeepSeek-Prover-V2-7B \\
    --dataset_path ../LeanPhysBench/LeanPhysBench_v0.json

  # Open-source model via vLLM direct
  python prove_writer.py --backend vllm \\
    --model deepseek-ai/DeepSeek-Prover-V2-7B \\
    --dataset_path ../LeanPhysBench/LeanPhysBench_v0.json

  # Closed-source model
  python prove_writer.py --backend api --base_url https://api.openai.com/v1 \\
    --model gpt-4o --api_key $OPENAI_API_KEY \\
    --dataset_path ../LeanPhysBench/LeanPhysBench_v0.json
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))

from utils.utils import read_from_json, write_to_json
from prompts.prompt_builder import build_messages, build_prompt_string, build_kimina_prompt
from prompts.model_configs import get_model_config
from pathlib import Path


def _get_nl_statement(rec):
    """Extract natural language statement from a record."""
    for key in ("Natural_language_statement", "Informal_statement", "natural_language"):
        if key in rec:
            return rec[key]
    raise KeyError(f"No NL statement found in record: {list(rec.keys())}")


def _get_lean4_statement(rec):
    """Extract Lean4 statement from a record."""
    for key in ("Theorem", "Statement", "formal_statement", "formal_theorem"):
        if key in rec:
            return rec[key]
    raise KeyError(f"No Lean4 statement found in record: {list(rec.keys())}")


def _get_header(rec):
    """Extract header from a record (dataset-specific field)."""
    return rec.get("Header", "")


def main():
    parser = argparse.ArgumentParser(description="LeanPhysBench proof generation")
    parser.add_argument("--dataset_path", type=str, required=True,
                        help="Path to LeanPhysBench_v0.json")
    parser.add_argument("--model", type=str, required=True,
                        help="Model name/path (e.g., deepseek-ai/DeepSeek-Prover-V2-7B)")
    parser.add_argument("--backend", type=str, choices=["api", "vllm"], default="api",
                        help="Inference backend: 'api' (OpenAI-compatible) or 'vllm' (direct)")
    parser.add_argument("--base_url", type=str, default="http://localhost:8000/v1",
                        help="API base URL (only for --backend api)")
    parser.add_argument("--api_key", type=str, default=os.environ.get("OPENAI_API_KEY", "EMPTY"),
                        help="API key (only for --backend api)")
    parser.add_argument("--use_lib", action="store_true",
                        help="Include PhysLib documentation in the prompt")
    parser.add_argument("--physlib_prompt", type=str, default="",
                        help="Path to PhysLib prompt text file")
    parser.add_argument("--proof_num", type=int, default=16,
                        help="Number of proofs per theorem")
    parser.add_argument("--temperature", type=float, default=0.8)
    parser.add_argument("--top_p", type=float, default=0.95)
    parser.add_argument("--max_tokens", type=int, default=14000)
    parser.add_argument("--batch_size", type=int, default=4,
                        help="Batch size (vLLM direct mode)")
    parser.add_argument("--repetition_penalty", type=float, default=1.0,
                        help="Repetition penalty (vLLM direct mode)")
    parser.add_argument("--gpu_memory_utilization", type=float, default=0.95,
                        help="GPU memory utilization (vLLM direct mode)")
    parser.add_argument("--ckpt_path", type=str, default="./checkpoints",
                        help="Checkpoint directory")
    parser.add_argument("--save_path", type=str, default="./output",
                        help="Final output directory")
    parser.add_argument("--begin_idx", type=int, default=0)
    parser.add_argument("--end_idx", type=int, default=-1)
    parser.add_argument("--dataset_workers", type=int, default=4,
                        help="Parallelism across records (API mode)")
    parser.add_argument("--attempt_workers", type=int, default=4,
                        help="Parallelism per record (API mode)")
    parser.add_argument("--print_result", action="store_true")
    args = parser.parse_args()

    # Load dataset
    dataset = read_from_json(args.dataset_path)
    if args.end_idx == -1:
        args.end_idx = len(dataset)
    dataset_slice = dataset[args.begin_idx:args.end_idx]
    print(f"Loaded {len(dataset_slice)} theorems [{args.begin_idx}:{args.end_idx}]")

    # Load PhysLib prompt
    physlib_doc = ""
    if args.use_lib and args.physlib_prompt:
        physlib_doc = Path(args.physlib_prompt).read_text(encoding="utf-8")
        print(f"Loaded PhysLib prompt ({len(physlib_doc)} chars)")

    # Setup checkpoint directory
    # If user provides --ckpt_path, use it directly as the checkpoint directory.
    # Otherwise, auto-generate a descriptive subdirectory under ./checkpoints/
    model_short = args.model.split("/")[-1]
    lib_prefix = "phylib-" if args.use_lib else ""
    if args.ckpt_path == "./checkpoints":
        ckpt_dir = f"{args.ckpt_path}/{lib_prefix}{model_short}-num{args.proof_num}-{args.begin_idx}-{args.end_idx}"
    else:
        ckpt_dir = args.ckpt_path
    Path(ckpt_dir).mkdir(parents=True, exist_ok=True)

    config = get_model_config(args.model)

    if args.backend == "api":
        from backends.api_backend import APIBackend

        backend = APIBackend(
            base_url=args.base_url,
            api_key=args.api_key,
            model_name=args.model,
        )

        def make_messages(rec):
            nl = _get_nl_statement(rec)
            header = _get_header(rec)
            lean4 = rec.get("Theorem", rec.get("Statement", ""))
            return build_messages(
                nl_statement=nl,
                lean4_statement=lean4,
                lean4_header=header,
                model_name=args.model,
                physlib_doc=physlib_doc,
                use_lib=args.use_lib,
            )

        results = backend.generate_proofs(
            dataset=dataset_slice,
            prompt_messages_fn=make_messages,
            proof_num=args.proof_num,
            temperature=args.temperature,
            top_p=args.top_p,
            max_tokens=args.max_tokens,
            ckpt_path=ckpt_dir,
            dataset_workers=args.dataset_workers,
            attempt_workers=args.attempt_workers,
        )

    elif args.backend == "vllm":
        from backends.vllm_backend import VLLMBackend

        backend = VLLMBackend(
            model_name=args.model,
            gpu_memory_utilization=args.gpu_memory_utilization,
        )

        def make_prompt_str(rec):
            nl = _get_nl_statement(rec)
            header = _get_header(rec)
            lean4 = rec.get("Theorem", rec.get("Statement", ""))

            if config.prompt_format == "kimina":
                return build_kimina_prompt(
                    nl_statement=nl,
                    lean4_statement=lean4,
                    lean4_header=header,
                    physlib_doc=physlib_doc,
                    use_lib=args.use_lib,
                )

            messages = build_messages(
                nl_statement=nl,
                lean4_statement=lean4,
                lean4_header=header,
                model_name=args.model,
                physlib_doc=physlib_doc,
                use_lib=args.use_lib,
            )
            return build_prompt_string(
                messages,
                tokenizer=backend.tokenizer,
                model_name=args.model,
            )

        results = backend.generate_proofs(
            dataset=dataset_slice,
            prompt_fn=make_prompt_str,
            proof_num=args.proof_num,
            temperature=args.temperature,
            top_p=args.top_p,
            repetition_penalty=args.repetition_penalty,
            max_tokens=args.max_tokens,
            batch_size=args.batch_size,
            ckpt_path=ckpt_dir,
            print_result=args.print_result,
        )

    # Save final output
    Path(args.save_path).mkdir(parents=True, exist_ok=True)
    out_file = f"{args.save_path}/{lib_prefix}{model_short}-num{args.proof_num}-{args.begin_idx}-{args.end_idx}.json"
    write_to_json(out_file, results)
    print(f"Done. Output saved to {out_file}")
    print(f"Checkpoints in: {ckpt_dir}")
    print(f"Next step: python eval/verify.py --checkpoint_dir {ckpt_dir} --project_dir ./PhysLib_v1 --lib_version v1")


if __name__ == "__main__":
    main()
