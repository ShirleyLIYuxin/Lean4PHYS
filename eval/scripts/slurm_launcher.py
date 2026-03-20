#!/usr/bin/env python3
"""
Optional SLURM job launcher for distributed proof generation.

Splits the dataset into slices and submits one SLURM job per slice.
Each job runs prove_writer.py on its assigned slice.

Usage:
  python slurm_launcher.py \\
    --dataset_path ../LeanPhysBench/LeanPhysBench_v0.json \\
    --model deepseek-ai/DeepSeek-Prover-V2-7B \\
    --num_jobs 4 \\
    --partition gpu \\
    --time_limit 12:00:00
"""

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional, Tuple


def split_range(begin: int, end: int, parts: int) -> List[Tuple[int, int]]:
    """Split [begin, end) into `parts` roughly equal sub-ranges."""
    total = max(0, end - begin)
    parts = max(1, parts)
    base, rem = divmod(total, parts)
    out = []
    cur = begin
    for i in range(parts):
        size = base + (1 if i < rem else 0)
        if size > 0:
            out.append((cur, cur + size))
            cur += size
    return out


def build_sbatch_script(
    *,
    job_name: str,
    out_path: str,
    err_path: str,
    partition: str,
    gpus: int,
    cpus: int,
    mem: str,
    time_limit: str,
    account: Optional[str],
    python_cmd: str,
) -> str:
    """Generate an sbatch script."""
    lines = ["#!/bin/bash"]
    if account:
        lines.append(f"#SBATCH --account={account}")
    lines += [
        f"#SBATCH --job-name={job_name}",
        f"#SBATCH --output={out_path}",
        f"#SBATCH --error={err_path}",
        f"#SBATCH --partition={partition}",
        "#SBATCH --nodes=1",
        "#SBATCH --ntasks-per-node=1",
        f"#SBATCH --gpus-per-node={gpus}",
        f"#SBATCH --cpus-per-task={cpus}",
        f"#SBATCH --mem={mem}",
        f"#SBATCH --time={time_limit}",
        "",
        "set -e",
        "",
        python_cmd,
    ]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="SLURM launcher for prove_writer.py")
    parser.add_argument("--dataset_path", type=str, required=True)
    parser.add_argument("--model", type=str, required=True)
    parser.add_argument("--backend", type=str, default="vllm", choices=["api", "vllm"])
    parser.add_argument("--num_jobs", type=int, default=4)
    parser.add_argument("--begin_idx", type=int, default=0)
    parser.add_argument("--end_idx", type=int, default=-1)
    parser.add_argument("--proof_num", type=int, default=16)
    parser.add_argument("--ckpt_path", type=str, default="./checkpoints")
    parser.add_argument("--save_path", type=str, default="./output")
    parser.add_argument("--use_lib", action="store_true")
    parser.add_argument("--physlib_prompt", type=str, default="")

    # SLURM options
    parser.add_argument("--partition", type=str, default="gpu")
    parser.add_argument("--time_limit", type=str, default="12:00:00")
    parser.add_argument("--mem", type=str, default="64g")
    parser.add_argument("--gpus", type=int, default=1)
    parser.add_argument("--cpus", type=int, default=16)
    parser.add_argument("--account", type=str, default="")
    args = parser.parse_args()

    # Determine dataset size
    import json
    with open(args.dataset_path) as f:
        dataset_size = len(json.load(f))
    if args.end_idx == -1:
        args.end_idx = dataset_size

    ranges = split_range(args.begin_idx, args.end_idx, args.num_jobs)
    log_dir = Path(args.ckpt_path) / "slurm_logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    sb_dir = Path(args.ckpt_path) / "sbatch_scripts"
    sb_dir.mkdir(parents=True, exist_ok=True)

    prove_writer = Path(__file__).resolve().parent.parent / "prove_writer.py"

    for s, e in ranges:
        job_name = f"pw-{s}-{e}"
        cmd_parts = [
            sys.executable, str(prove_writer),
            "--dataset_path", args.dataset_path,
            "--model", args.model,
            "--backend", args.backend,
            "--begin_idx", str(s),
            "--end_idx", str(e),
            "--proof_num", str(args.proof_num),
            "--ckpt_path", args.ckpt_path,
            "--save_path", args.save_path,
        ]
        if args.use_lib:
            cmd_parts += ["--use_lib", "--physlib_prompt", args.physlib_prompt]

        python_cmd = " ".join(cmd_parts)
        script = build_sbatch_script(
            job_name=job_name,
            out_path=str(log_dir / f"{job_name}.out"),
            err_path=str(log_dir / f"{job_name}.err"),
            partition=args.partition,
            gpus=args.gpus,
            cpus=args.cpus,
            mem=args.mem,
            time_limit=args.time_limit,
            account=args.account or None,
            python_cmd=python_cmd,
        )

        sb_file = sb_dir / f"{job_name}.sbatch"
        sb_file.write_text(script)
        result = subprocess.run(["sbatch", str(sb_file)], capture_output=True, text=True)
        print(f"[{s},{e}): {result.stdout.strip()}")


if __name__ == "__main__":
    main()
