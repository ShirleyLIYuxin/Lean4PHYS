#!/usr/bin/env python3
"""
Lean4 proof verification for LeanPhysBench.

Reads checkpoint JSON files produced by prove_writer.py, verifies each
generated proof by running `lake lean` in the PhysLib project, and
writes results with Proof_verification_log.

Usage:
  python verify.py \\
    --checkpoint_dir ./checkpoints/DeepSeek-Prover-V2-7B-num16-0-200/ \\
    --project_dir ../PhysLib_v1 \\
    --output_dir ./checkpoints/DeepSeek-Prover-V2-7B-num16-0-200_verified/ \\
    --max_workers 16 \\
    --lib_version v1
"""

import argparse
import json
import os
import re
import subprocess
import tempfile
import time
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Union

from tqdm import tqdm


# ---------------------------------------------------------------------------
# Core verification functions
# ---------------------------------------------------------------------------

def merge_question_answer(question: str, proof: str) -> str:
    """Replace 'sorry' in the question template with the proof."""
    lines = question.splitlines()
    proof_lines = proof.strip("\n").splitlines()
    new_lines = []
    for line in lines:
        if "sorry" in line:
            indent = len(line) - len(line.lstrip(" "))
            indent_str = " " * indent
            if line.strip() == "sorry":
                new_lines.extend((indent_str + pl).rstrip() for pl in proof_lines)
            elif line.strip().endswith("by sorry"):
                before = line.replace("sorry", "").rstrip()
                new_lines.append(before)
                new_lines.extend((indent_str + "  " + pl).rstrip() for pl in proof_lines)
            else:
                raise ValueError(f"Unrecognized sorry format: {line}")
        else:
            new_lines.append(line)
    return "\n".join(new_lines)


def parse_lean_diagnostics(output: str) -> Dict[str, List[Dict]]:
    """Parse `lake lean` stdout/stderr into structured errors and warnings."""
    errors, warnings = [], []
    pattern = re.compile(r"^(.*?):(\d+):(\d+): (error|warning): (.*)$")
    lines = output.splitlines()
    i = 0
    while i < len(lines):
        m = pattern.match(lines[i].strip())
        if m:
            file_path, line_no, col_no, level, message = m.groups()
            detail_lines = []
            i += 1
            while i < len(lines) and not pattern.match(lines[i].strip()) and lines[i].strip():
                detail_lines.append(lines[i].rstrip())
                i += 1
            entry = {
                "file": file_path,
                "line": int(line_no),
                "column": int(col_no),
                "message": message.strip(),
                "detail": "\n".join(detail_lines).strip(),
            }
            (errors if level == "error" else warnings).append(entry)
        else:
            i += 1
    return {"errors": errors, "warnings": warnings}


def parse_by_or_sorry(proof: str, keep_after: bool) -> str:
    """Split a theorem at ':= by' or ':= sorry'."""
    match = re.search(r":=\s*(?:by|sorry)", proof, re.MULTILINE)
    if match:
        assign_pos = proof.find(":=", match.start())
        if keep_after:
            return proof[assign_pos + 2:].strip()
        else:
            return proof[:assign_pos + 2].strip()
    return proof.strip()


def verify_single_answer(
    item: Union[Dict, str],
    project_dir: str = ".",
    allow_sorry: bool = False,
    timeout: int = 1800,
) -> Dict:
    """
    Verify a single Lean4 proof by writing a temp file and running `lake lean`.

    Args:
        item: Either a dict with 'question'/'proof' keys, a file path, or inline code.
        project_dir: Path to the Lean project (where lakefile.lean lives).
        allow_sorry: If False, any sorry warning counts as failure.
        timeout: Maximum seconds for `lake lean`.

    Returns:
        Dict with 'verified', 'errors', 'warnings', 'stdout', 'stderr', 'time'.
    """
    temp_file = False
    lean_code, lean_file, file_id = None, None, None

    if isinstance(item, dict):
        lean_code = merge_question_answer(item["question"], item["proof"])
        file_id = item.get("id", "temp.lean")
        temp_file = True
    elif isinstance(item, str):
        if os.path.exists(item):
            lean_file = item
            file_id = os.path.basename(item)
        else:
            lean_code = item
            file_id = "inline.lean"
            temp_file = True
    else:
        raise ValueError(f"Invalid item type: {type(item)}")

    if temp_file:
        with tempfile.NamedTemporaryFile(
            delete=False, suffix=".lean", dir=project_dir, mode="w"
        ) as f:
            f.write(lean_code)
            lean_file = f.name

    start = time.perf_counter()
    try:
        try:
            result = subprocess.run(
                ["lake", "lean", lean_file],
                cwd=project_dir,
                text=True,
                capture_output=True,
                timeout=timeout,
            )
            elapsed = time.perf_counter() - start
            diags = parse_lean_diagnostics(result.stdout + "\n" + result.stderr)
            errors, warnings = diags["errors"], diags["warnings"]
            verified = result.returncode == 0 and not errors
            if not allow_sorry:
                if any("sorry" in w["message"] or "sorry" in w.get("detail", "") for w in warnings):
                    verified = False
            return {
                "id": file_id,
                "verified": verified,
                "errors": errors,
                "warnings": warnings,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "time": elapsed,
            }
        except subprocess.TimeoutExpired:
            elapsed = time.perf_counter() - start
            return {
                "id": file_id, "verified": False,
                "errors": [], "warnings": [],
                "stdout": "", "stderr": "",
                "time": "timeout",
            }
    finally:
        if temp_file and lean_file and os.path.exists(lean_file):
            os.remove(lean_file)


# ---------------------------------------------------------------------------
# Batch verification for checkpoint files
# ---------------------------------------------------------------------------

def _replace_imports_for_v2(header: str) -> str:
    """Replace PHYSlib imports with PhysLib for v2 verification."""
    return header.replace("PHYSlib", "PhysLib")


def verify_entry(args):
    """Verify a single proof entry (used by ProcessPoolExecutor)."""
    header, theorem, entry, project_dir, max_heartbeats = args
    generated_proof = entry["generated_proof"]
    filtered_proof = parse_by_or_sorry(generated_proof, keep_after=True)
    filtered_theorem = parse_by_or_sorry(theorem, keep_after=False)
    verified_code = f"{header}\nset_option maxHeartbeats {max_heartbeats}\n{filtered_theorem}\n{filtered_proof}"

    response = verify_single_answer(verified_code, project_dir=project_dir, allow_sorry=False)
    return {
        "custom_id": entry["generation_idx"],
        "proof": generated_proof,
        "pass": response["verified"],
        "verify_result": {
            "verified_code": verified_code,
            "error": response["errors"] or None,
            "warning": response["warnings"] or None,
            "response": (response["stdout"] + "\n" + response["stderr"]).splitlines(),
            "time": response["time"],
        },
    }


def process_json_file(
    src_file: Path,
    dst_folder: Path,
    project_dir: str,
    max_heartbeats: int,
    lib_version: str,
    verify_workers: int = 16,
):
    """Process a single checkpoint JSON file: verify all proofs and save results."""
    dst_file = dst_folder / src_file.name

    try:
        with open(src_file, "r", encoding="utf-8") as f:
            data = json.load(f)
    except json.JSONDecodeError as e:
        print(f"Skipping {src_file}: {e}")
        return

    # Resume: check existing verification log
    existing_verification = []
    if dst_file.exists():
        try:
            with open(dst_file, "r", encoding="utf-8") as f:
                dst_data = json.load(f)
            existing_verification = dst_data.get("Proof_verification_log", [])
        except json.JSONDecodeError:
            pass

    header = data.get("Header", "")
    theorem = data.get("Theorem", "")
    proof_log = data.get("Proof_generation_log", [])

    # Apply import substitution for v2
    if lib_version == "v2":
        header = _replace_imports_for_v2(header)

    verified_ids = {v["custom_id"] for v in existing_verification if "custom_id" in v}
    entries_to_verify = [
        e for e in proof_log if e.get("generation_idx") not in verified_ids
    ]

    if not entries_to_verify:
        return

    args_list = [
        (header, theorem, entry, project_dir, max_heartbeats)
        for entry in entries_to_verify
    ]

    verification_log = []
    with ProcessPoolExecutor(max_workers=verify_workers) as executor:
        futures = {executor.submit(verify_entry, a): a for a in args_list}
        for future in as_completed(futures):
            try:
                verification_log.append(future.result())
            except Exception as e:
                print(f"Error verifying in {src_file.name}: {e}")

    verification_log.extend(existing_verification)
    verification_log.sort(key=lambda x: x.get("custom_id", ""))
    data["Proof_verification_log"] = verification_log

    with open(dst_file, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def main():
    parser = argparse.ArgumentParser(description="LeanPhysBench proof verification")
    parser.add_argument("--checkpoint_dir", type=str, required=True,
                        help="Directory containing checkpoint JSON files")
    parser.add_argument("--project_dir", type=str, required=True,
                        help="Path to the PhysLib Lean project (with lakefile.lean)")
    parser.add_argument("--output_dir", type=str, default="",
                        help="Output directory (default: checkpoint_dir + '_verified')")
    parser.add_argument("--max_workers", type=int, default=16,
                        help="Max parallel workers for file-level processing")
    parser.add_argument("--verify_workers", type=int, default=16,
                        help="Max parallel workers per file for proof verification")
    parser.add_argument("--max_heartbeats", type=int, default=10_000_000,
                        help="Lean maxHeartbeats setting")
    parser.add_argument("--lib_version", type=str, choices=["v1", "v2"], default="v1",
                        help="PhysLib version (v2 replaces PHYSlib→PhysLib in imports)")
    args = parser.parse_args()

    src_folder = Path(args.checkpoint_dir)
    if args.output_dir:
        dst_folder = Path(args.output_dir)
    else:
        dst_folder = src_folder.parent / f"{src_folder.name}_verified"
    dst_folder.mkdir(parents=True, exist_ok=True)

    json_files = list(src_folder.glob("*.json"))
    print(f"Found {len(json_files)} checkpoint files in {src_folder}")

    with ProcessPoolExecutor(max_workers=args.max_workers) as executor:
        futures = {
            executor.submit(
                process_json_file,
                f, dst_folder, str(Path(args.project_dir).resolve()),
                args.max_heartbeats, args.lib_version, args.verify_workers,
            ): f
            for f in json_files
        }
        for future in tqdm(as_completed(futures), total=len(futures), desc="Verifying"):
            future.result()

    print(f"Verification complete. Results in {dst_folder}")


if __name__ == "__main__":
    main()
