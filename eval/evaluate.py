#!/usr/bin/env python3
"""
Evaluation script: compute pass@N statistics from verified results.

Usage:
  python evaluate.py \\
    --verified_dir ../checkpoints/DeepSeek-Prover-V2-7B-num16-0-200_verified/ \\
    --output ../results/DeepSeek-Prover-V2-7B.json
"""

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path


def parse_model_info(folder_path: str):
    """Extract model name and attempt count from folder naming convention."""
    folder_name = Path(folder_path).name
    match = re.search(r"(.*)-num(\d+)", folder_name)
    if match:
        return match.group(1), int(match.group(2))
    return folder_name, None


def compute_success_rate_by_level(folder_path: str):
    """Compute per-level success rates from verified JSON files."""
    folder = Path(folder_path)
    json_files = list(folder.glob("*.json"))
    stats = defaultdict(lambda: {"total": 0, "solved": 0, "solved_questions": []})

    for file in json_files:
        with open(file, "r") as f:
            data = json.load(f)
        level = data.get("Level", "unknown")
        stats[level]["total"] += 1

        question_id = data.get("Name", file.stem)
        if any(log.get("pass", False) for log in data.get("Proof_verification_log", [])):
            stats[level]["solved"] += 1
            stats[level]["solved_questions"].append(question_id)

    return dict(stats)


def report_folder(folder: str):
    """Generate a full evaluation report for a verified folder."""
    model_name, num_attempts = parse_model_info(folder)
    stats = compute_success_rate_by_level(folder)

    results = {
        "model": model_name,
        "num_attempts": num_attempts,
        "levels": {},
        "overall": {},
    }

    for lvl, vals in stats.items():
        total, solved = vals["total"], vals["solved"]
        rate = solved / total if total > 0 else 0
        results["levels"][lvl] = {
            "total": total,
            "solved": solved,
            f"pass@{num_attempts}": rate,
            "solved_questions": vals["solved_questions"],
        }

    overall_total = sum(v["total"] for v in stats.values())
    overall_solved = sum(v["solved"] for v in stats.values())
    overall_solved_questions = [q for v in stats.values() for q in v["solved_questions"]]
    overall_rate = overall_solved / overall_total if overall_total > 0 else 0
    results["overall"] = {
        "total": overall_total,
        "solved": overall_solved,
        f"pass@{num_attempts}": overall_rate,
        "solved_questions": overall_solved_questions,
    }

    return results


def main():
    parser = argparse.ArgumentParser(description="LeanPhysBench evaluation")
    parser.add_argument("--verified_dir", type=str, required=True,
                        help="Directory with verified checkpoint JSONs")
    parser.add_argument("--output", type=str, default="",
                        help="Output JSON file (default: stdout)")
    args = parser.parse_args()

    results = report_folder(args.verified_dir)

    if args.output:
        Path(args.output).parent.mkdir(parents=True, exist_ok=True)
        with open(args.output, "w") as f:
            json.dump(results, f, indent=2)
        print(f"Results saved to {args.output}")
    else:
        print(json.dumps(results, indent=2))

    # Print summary
    n = results["num_attempts"]
    print(f"\nModel: {results['model']}")
    print(f"Overall pass@{n}: {results['overall'].get(f'pass@{n}', 0):.4f} "
          f"({results['overall']['solved']}/{results['overall']['total']})")
    for lvl, vals in sorted(results["levels"].items()):
        print(f"  {lvl}: pass@{n}={vals.get(f'pass@{n}', 0):.4f} "
              f"({vals['solved']}/{vals['total']})")


if __name__ == "__main__":
    main()
