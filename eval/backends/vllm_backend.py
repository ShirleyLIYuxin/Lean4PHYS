"""
vLLM direct backend for proof generation (no HTTP server needed).

Use this when running on a local GPU machine for maximum throughput.
"""

import hashlib
import re
from typing import List, Dict, Optional, Tuple
from pathlib import Path
from tqdm import tqdm

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from utils.utils import (
    extract_code_blocks_as_list, contains_code_block, write_to_json
)


class LLMRollout:
    """vLLM-based batched inference for theorem proof generation."""

    def __init__(self, model, tokenizer):
        """
        Args:
            model: A vllm.LLM instance.
            tokenizer: The corresponding HuggingFace tokenizer.
        """
        self.model = model
        self.tokenizer = tokenizer

    def batched_query_model(
        self,
        prompts: List[str],
        max_tokens: int = 4096,
        temperature: float = 1.0,
        top_p: float = 0.95,
        repetition_penalty: float = 1.0,
        sampling_num: int = 2,
        stop_strs: Optional[List[str]] = None,
    ) -> Tuple[List[str], List[int]]:
        """
        Query model with given prompts and return completed strings.

        Args:
            prompts: List of formatted prompt strings.
            max_tokens: Maximum tokens to generate.
            temperature: Sampling temperature.
            top_p: Top-p sampling.
            repetition_penalty: Penalty for token repetition.
            sampling_num: Number of samples per prompt.
            stop_strs: Optional stop strings.

        Returns:
            Tuple of (completed_strings, generated_token_counts).
        """
        from vllm import SamplingParams

        params_kwargs = {
            "temperature": temperature,
            "top_p": top_p,
            "repetition_penalty": repetition_penalty,
            "max_tokens": max_tokens,
            "n": sampling_num,
            "skip_special_tokens": False,
        }
        if stop_strs:
            params_kwargs["stop"] = stop_strs

        sampling_params = SamplingParams(**params_kwargs)

        # vLLM v0.10+ uses prompts directly as strings
        outputs = self.model.generate(
            prompts=prompts,
            sampling_params=sampling_params,
        )

        output_strings = []
        for out in outputs:
            for resp in out.outputs:
                output_strings.append(resp.text)

        # Duplicate prompts to match sampling_num
        return_strings = [p for p in prompts for _ in range(sampling_num)]
        generated_token_num = []

        assert len(output_strings) == len(return_strings), (
            f"Output ({len(output_strings)}) != prompts*n ({len(return_strings)})"
        )

        for i in range(len(return_strings)):
            return_strings[i] += output_strings[i]
            token_count = len(
                self.tokenizer(output_strings[i], add_special_tokens=False)["input_ids"]
            )
            generated_token_num.append(token_count)

        return return_strings, generated_token_num


class VLLMBackend:
    """vLLM direct backend for batch proof generation."""

    def __init__(self, model_name: str, gpu_memory_utilization: float = 0.95):
        from vllm import LLM
        from transformers import AutoTokenizer

        self.model = LLM(model_name, gpu_memory_utilization=gpu_memory_utilization)
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        self.generator = LLMRollout(self.model, self.tokenizer)

    def generate_proofs(
        self,
        dataset: List[Dict],
        prompt_fn,
        *,
        proof_num: int = 16,
        temperature: float = 0.8,
        top_p: float = 0.95,
        repetition_penalty: float = 1.0,
        max_tokens: int = 8192,
        batch_size: int = 4,
        ckpt_path: str = "./checkpoints",
        print_result: bool = False,
    ) -> List[Dict]:
        """
        Generate proofs for each record in the dataset.

        Args:
            dataset: List of theorem records.
            prompt_fn: Callable(rec) -> str that builds a formatted prompt string.
            proof_num: Number of proofs per theorem.
            temperature: Sampling temperature.
            top_p: Top-p sampling.
            repetition_penalty: Repetition penalty.
            max_tokens: Max tokens per generation.
            batch_size: vLLM batch size.
            ckpt_path: Checkpoint directory.
            print_result: Whether to print intermediate results.

        Returns:
            Updated dataset with Generated_proof and Proof_generation_log fields.
        """
        import math

        Path(ckpt_path).mkdir(parents=True, exist_ok=True)

        for rec in dataset:
            rec.setdefault("Generated_proof", [])
            rec.setdefault("Proof_generation_log", [])
            rec.setdefault("Proof_attempts", rec.get("Proof_attempts", 0))

        # Build work items
        work = []
        for idx, rec in enumerate(dataset):
            need = max(0, proof_num - rec["Proof_attempts"])
            if need > 0:
                prompt = prompt_fn(rec)
                work.append({"idx": idx, "prompt": prompt, "need": need})

        total = sum(w["need"] for w in work)
        pbar = tqdm(total=total, desc="Generating proofs (vLLM)")

        while True:
            work = [w for w in work if w["need"] > 0]
            if not work:
                break

            batch_prompts, owners = [], []
            for w in work:
                while w["need"] > 0 and len(batch_prompts) < batch_size:
                    batch_prompts.append(w["prompt"])
                    owners.append(w["idx"])
                    w["need"] -= 1
                if len(batch_prompts) >= batch_size:
                    break

            responses, gen_tok = self.generator.batched_query_model(
                batch_prompts,
                max_tokens=max_tokens,
                temperature=temperature,
                top_p=top_p,
                repetition_penalty=repetition_penalty,
                sampling_num=1,
            )

            for resp, gtok, owner_idx in zip(responses, gen_tok, owners):
                rec = dataset[owner_idx]
                prompt = batch_prompts[owners.index(owner_idx)]
                rec["Proof_attempts"] += 1
                pbar.update(1)

                gen = resp[len(prompt):] if resp.startswith(prompt) else resp
                blocks = extract_code_blocks_as_list(gen, code_type="lean4")
                if blocks != -1 and len(blocks) > 0:
                    proof_text = blocks[-1]
                    rec["Generated_proof"].append(proof_text)
                    rec["Proof_generation_log"].append({
                        "generation_idx": hashlib.sha256(proof_text.encode("utf-8")).hexdigest(),
                        "generated_content": resp,
                        "generated_token_num": gtok,
                        "generated_proof": proof_text,
                    })

                if print_result:
                    print(f"{'#' * 40}\nResponse:\n{resp}\n")

                write_to_json(f"{ckpt_path}/{rec['Name']}.json", rec)

        pbar.close()
        return dataset
