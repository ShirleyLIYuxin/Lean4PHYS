"""
Per-model configurations for prompt construction and generation parameters.

To evaluate a new model, add a new entry to MODEL_CONFIGS.
"""

from dataclasses import dataclass, field
from typing import Optional, Dict


@dataclass
class ModelConfig:
    """Configuration for a specific model."""
    system_prompt: Optional[str] = None
    enable_thinking: Optional[bool] = None  # For Qwen3-style models
    prompt_format: str = "messages"  # "messages" (default) or "kimina" (raw tokens)
    extra_params: Dict = field(default_factory=dict)


# --- Registry ---
# Keys are matched via substring against the model name (case-insensitive).
# More specific keys should come first; the first match wins.

MODEL_CONFIGS: Dict[str, ModelConfig] = {
    "kimina": ModelConfig(
        system_prompt="You are an expert in mathematics and Lean 4.",
        prompt_format="kimina",
    ),
    "qwen3": ModelConfig(
        enable_thinking=True,
    ),
    "deepseek-r1": ModelConfig(
        system_prompt="You are an expert in Lean4 theorem proving.",
    ),
    "goedel": ModelConfig(),
    "deepseek-prover": ModelConfig(),
    "stp": ModelConfig(
        system_prompt="You are a symbolic theorem prover specialized in Lean 4 formal verification.",
    ),
    "gpt-4o": ModelConfig(
        system_prompt="You are a helpful assistant skilled in Lean4 theorem proving.",
    ),
    "claude": ModelConfig(
        system_prompt="You are a helpful assistant skilled in Lean4 theorem proving.",
    ),
    "gemini": ModelConfig(
        system_prompt="You are a helpful assistant skilled in Lean4 theorem proving.",
    ),
    "o1": ModelConfig(
        system_prompt="You are a helpful assistant skilled in Lean4 theorem proving.",
    ),
}

# Default config for unrecognized models
_DEFAULT_CONFIG = ModelConfig(
    system_prompt="You are a helpful assistant skilled in Lean4 theorem proving."
)


def get_model_config(model_name: str) -> ModelConfig:
    """Look up the config for a model by substring match."""
    name_lower = model_name.lower()
    for key, config in MODEL_CONFIGS.items():
        if key in name_lower:
            return config
    return _DEFAULT_CONFIG
