"""
Model-agnostic prompt construction for Lean4 theorem proving.

Builds `messages` (list of dicts with role/content) that can be:
  - Passed directly to OpenAI-compatible APIs
  - Converted to a string via tokenizer.apply_chat_template() for vLLM direct mode
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from utils.utils import preprocess_theorem_statement
from prompts.model_configs import get_model_config


LEAN4_HEADER = """\
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat"""


def build_messages(
    nl_statement: str,
    lean4_statement: str,
    lean4_header: str,
    *,
    model_name: str = "",
    physlib_doc: str = "",
    use_lib: bool = False,
) -> list:
    """
    Build a chat messages list for proof generation.

    Args:
        nl_statement: Natural language description of the theorem.
        lean4_statement: The Lean4 theorem statement (will be preprocessed to end with ':= by').
        lean4_header: The import header for the theorem.
        model_name: Model identifier, used to look up per-model config.
        physlib_doc: PhysLib documentation text to inject (only used when use_lib=True).
        use_lib: Whether to include PhysLib documentation in the prompt.

    Returns:
        List of message dicts: [{"role": "system"|"user", "content": "..."}]
    """
    config = get_model_config(model_name)
    statement = preprocess_theorem_statement(lean4_statement)

    # --- Build user content ---
    parts = []

    if use_lib and physlib_doc:
        parts.append(
            "Please first learn the new library besides mathlib and usage examples "
            "before answering the question. You should refer to the new unit system.\n\n"
            f"{physlib_doc}\n"
        )

    parts.append(f"""\
Complete the following Lean 4 code:

```lean4
{lean4_header}

/-- {nl_statement} -/
{statement}
```

Before producing the Lean 4 code to formally prove the given theorem, \
provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures \
that will guide the construction of the final formal proof.""")

    user_content = "\n".join(parts)

    messages = []
    if config.system_prompt:
        messages.append({"role": "system", "content": config.system_prompt})
    messages.append({"role": "user", "content": user_content})

    return messages


def build_prompt_string(
    messages: list,
    tokenizer=None,
    model_name: str = "",
) -> str:
    """
    Convert messages to a single prompt string for vLLM direct mode.

    If a tokenizer is provided, uses apply_chat_template().
    Otherwise, falls back to a simple concatenation.
    """
    config = get_model_config(model_name)

    if tokenizer is not None:
        kwargs = {"tokenize": False, "add_generation_prompt": True}
        if config.enable_thinking is not None:
            kwargs["enable_thinking"] = config.enable_thinking
        return tokenizer.apply_chat_template(messages, **kwargs)

    # Fallback: simple concatenation
    parts = []
    for msg in messages:
        role = msg["role"]
        content = msg["content"]
        if role == "system":
            parts.append(f"System: {content}\n")
        elif role == "user":
            parts.append(f"User: {content}\n")
    parts.append("Assistant: ")
    return "\n".join(parts)


def build_kimina_prompt(
    nl_statement: str,
    lean4_statement: str,
    lean4_header: str = LEAN4_HEADER,
    *,
    physlib_doc: str = "",
    use_lib: bool = False,
    system_prompt: str = "You are an expert in mathematics and Lean 4.",
) -> str:
    """
    Build prompt string for Kimina-Prover models using raw <|im_start|> tokens.
    Kimina uses its own chat format rather than the standard messages API.
    """
    if lean4_statement.endswith("sorry"):
        lean4_statement = lean4_statement[:-len("sorry")]
    statement = preprocess_theorem_statement(lean4_statement)

    if use_lib and physlib_doc:
        user_content = f"""\
Please first learn the new library that you should refer to before answering the question.

{physlib_doc}

Think about and solve the following problem step by step in Lean 4.

```lean4
{lean4_header}

/-- {nl_statement}-/
{statement}
```"""
    else:
        user_content = f"""\
Think about and solve the following problem step by step in Lean 4.

```lean4
{lean4_header}

/-- {nl_statement}-/
{statement}
```"""

    return (
        f"<|im_start|>system\n{system_prompt}<|im_end|>\n"
        f"<|im_start|>user\n{user_content}<|im_end|>\n"
        f"<|im_start|>assistant\n"
    )
