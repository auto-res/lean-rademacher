# Codex / Lean Workflow (ATC)

This repository uses Lean 4 + Mathlib for automated theory construction in an equational setting.

This file is the authoritative runtime instruction set for this repository.
If external templates conflict with this file, follow this file.

## Repository focus

Main entry points:

- `AutomatedTheoryConstruction/Theory.lean`
- `AutomatedTheoryConstruction/Derived.lean`
- `AutomatedTheoryConstruction/Scratch.lean`
- `scripts/run_loop.py`
- `scripts/codex_worker.py`
- `.codex/skills/`

Core loop role split:

- LLM (`prover`): propose `proof`, `counterexample`, or `stuck` plus optional new problems in natural language
- LLM (`formalize` / `repair`): translate a chosen direction into Lean code and repair it after diagnostics
- Deterministic scripts: selection, state transitions, verification, and persistence
- Open problems and `new_problems` may be either Lean-formal statements or semi-formal natural-language research prompts.

Do not move deterministic state-transition logic into prompts.

## Module contract

- `AutomatedTheoryConstruction/Theory.lean`: base symbols and axioms
- `AutomatedTheoryConstruction/Derived.lean`: verified theorem accumulation target
- `AutomatedTheoryConstruction/Scratch.lean`: temporary verification artifact

Verification path:

- `lake env lean AutomatedTheoryConstruction/Scratch.lean`

## Formalization boundary

- `prover` does not emit `proof_text`; it emits natural-language reasoning only.
- `proof_text` belongs to `formalize` / `repair` and must be Lean tactic code only when result is `proof` or `counterexample`.
- Lean verification decides success; natural-language plausibility is not enough.
- If formalization or verification fails, keep the problem open unless deterministic update rules move it.

## Standard proof workflow

1. Read the target statement and nearby context.
2. Plan a short tactic strategy and theorem reuse path.
3. Use skeleton-first for non-trivial proofs (`have ... := by` blocks), then fill from the top.
4. Iterate with Lean diagnostics:
   - fix one top error at a time
   - re-run Lean check after each fix
5. Finish only after removing relevant `sorry` and passing Lean check.

## Proof style

- Keep steps small and local.
- Prefer `exact`, `simpa`, `rw`, `constructor`, `cases`, `intro`, `apply` before heavier automation.
- Prefer `simp only [...]` over broad `simp [*]` in fragile goals.
- Keep imports minimal; `import Mathlib` is allowed when needed.
- Use explicit `*` and `^` notation.
- [Required] Use notation-first style for seeds, expansions, and claims whenever abbreviations are possible.
  - In planning and implementation, write using the project notation first, and only switch to fully qualified names when notation is missing or ambiguous.

## Mathlib usage

- For Lean import issues, Mathlib import issues, or import-minimization decisions, always consult `.codex/skills/mathlib-usage/SKILL.md`.
- Search before inventing lemmas.
- Verify lemma names exist before using them.
- Useful search command: `rg -n "<pattern>" .lake/packages/mathlib/Mathlib`

## Common commands

- Type-check one file: `lake env lean path/to/File.lean`
- Build project: `lake build`
- Repo search: `rg -n "<pattern>" .`
- Python scripts: `uv run ...`

## Safety and operations

- Keep edits minimal and task-local.
- Do not run destructive git commands unless explicitly requested.
- Do not commit unless explicitly requested.
- Prefer deterministic behavior in orchestrator scripts; keep prompt-side logic lightweight.

## Non-interactive worker runs

- When invoked by `scripts/codex_worker.py` or another orchestrated worker path, treat the run as non-interactive.
- Do not ask the user questions, request clarification, or wait for confirmation in that mode.
- If the payload is incomplete or ambiguous, make the best conservative local inference and return a contract-compliant fallback result instead.

## Skills index

Use repository-local skills under `.codex/skills/` as supporting guidance:

- `lean-rule`
- `mathlib-usage`
- `prover-interface`
- `refactoring`

`AGENTS.md` remains the primary authority.
