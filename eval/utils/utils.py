"""Utility functions for proof processing and data management."""

import json
import os
import re
import hashlib
from typing import List, Dict, Any, Optional
from pathlib import Path


def rstrip_space_newline_and_by(s: str) -> str:
    """Remove trailing spaces, newlines, and trailing 'by' or 'sorry' keywords."""
    return re.sub(r'(?:[ \n]+|[ \n]*\b(?:by|sorry)\b[ \n]*)+$', '', s)


def preprocess_theorem_statement(lean4_statement: str) -> str:
    """Ensure Lean4 statement ends with ':= by'."""
    lean4_statement = lean4_statement.rstrip()
    lean4_statement = re.sub(r'[:=]+\s*$', '', lean4_statement)
    return lean4_statement + " := by"


def judge_statement_modification(original_statement: str, generated_proof: str) -> bool:
    """Check whether the statement was modified in the generated proof (True = modified)."""
    processed_original = rstrip_space_newline_and_by(original_statement)
    processed_original = processed_original.replace(" ", "").replace("\n", "").replace("\t", "")
    processed_proof = generated_proof.replace(" ", "").replace("\n", "").replace("\t", "")
    return processed_original not in processed_proof


def contains_code_block(text: str, code_type: str = "md") -> bool:
    """Check whether a code block of the given type exists in text."""
    pattern = rf'```{code_type}.*?```'
    return re.search(pattern, text, re.DOTALL) is not None


def extract_code_blocks_as_list(text: str, code_type: str = "md") -> List[str]:
    """
    Extract all code blocks of the given type from text.
    Returns a list of code block contents. Returns -1 if none found.
    """
    lines = text.split('\n')
    inside_code_block = False
    code_blocks = []
    current_block = []

    for line in lines:
        if line.strip().startswith(f'```{code_type}'):
            inside_code_block = True
            continue
        elif "```" in line.strip() and inside_code_block:
            code_blocks.append('\n'.join(current_block))
            current_block = []
            inside_code_block = False
            continue
        if inside_code_block:
            current_block.append(line)

    if current_block:
        code_blocks.append('\n'.join(current_block))

    return code_blocks if code_blocks else -1


def extract_theorem_proof(input_str: str, theorem_name: str) -> Optional[str]:
    """Extract a named theorem with its proof from Lean4 code."""
    pattern = re.compile(
        r'(?P<theorem>theorem\s+' + re.escape(theorem_name) + r'\s*.*?[^:])\s*:=\s*(?P<proof>by\s+.*?)(?=\n\n|\Z)',
        re.DOTALL
    )
    match = pattern.search(str(input_str))
    return match.group('theorem') + ' := ' + match.group('proof') if match else None


def find_theorem_name(input_str: str) -> Optional[str]:
    """Extract the theorem name from a Lean4 statement."""
    match = re.search(r'theorem\s+(\w+)', input_str)
    return match.group(1) if match else None


def remove_comments(text: str) -> str:
    """Remove Lean4 comments (block and line) from text."""
    text = re.sub(r'/-.*?-/', '', text, flags=re.DOTALL)
    lines = text.split('\n')
    cleaned_lines = [line.split('--', 1)[0] for line in lines]
    return '\n'.join(cleaned_lines).strip()


# --- Data I/O ---

def write_to_json(file_path: str, data: Any):
    """Save data to a JSON file."""
    Path(file_path).parent.mkdir(parents=True, exist_ok=True)
    with open(file_path, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False)


def read_from_json(file_path: str) -> Any:
    """Load data from a JSON file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def read_json_in_folder(folder_path: str) -> List[Any]:
    """Load all JSON files from a folder."""
    json_list = []
    for filename in os.listdir(folder_path):
        if filename.endswith(".json"):
            json_list.append(read_from_json(os.path.join(folder_path, filename)))
    return json_list


def hash_dict(d: Dict) -> str:
    """SHA256 hash of a JSON-serialized dictionary."""
    return hashlib.sha256(json.dumps(d, sort_keys=True).encode('utf-8')).hexdigest()


def split_batch(data: List[Any], batch_size: int) -> List[List[Any]]:
    """Split data into fixed-size batches."""
    return [data[i:i + batch_size] for i in range(0, len(data), batch_size)]
