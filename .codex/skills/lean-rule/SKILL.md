---
name: lean-rule
description: Rules to apply this repo's Lean workflow (plan → skeleton → error-driven iteration → mathlib search → minimal diffs) consistently across all `.lean` files.
---

# Guidelines

`workflow/proof-planning.md` is only for **proof planning and replanning**.

Do not auto-apply the following from that document during implementation:

- formatting rules for planning outputs
- olympiad-style syntax restrictions (e.g., avoiding interval notation, banning undeclared vars)

During implementation, follow `AGENTS.md` and this repo-local skill first.

The skeleton-first rule in this skill is for proof construction: new proofs, proof repair, and substantial proof extensions.
Do not auto-apply it to non-semantic refactoring or cleanup passes.

## Which Skill To Use (Routing)

Use this quick routing table to select skills by situation.

- Lean theorem formalization or proof repair in `.lean` files:
  - Use `lean-rule` as the primary workflow.
  - Then apply `mathlib-usage` for lemma/import/search decisions.
- Mathlib lemma discovery, import minimization, or "does this lemma exist":
  - Use `mathlib-usage`.
- The loop prover JSON contract (natural-language proof/counterexample/stuck + new problems):
  - Use `prover-interface`.

When multiple skills are relevant, resolve priority as:

1. `AGENTS.md` (source of truth)
2. `lean-rule` (execution workflow for Lean proof work)
3. Task-specific contract/policy skill (`mathlib-usage`, `prover-interface`)

## Workflow

1. Plan via `workflow/proof-planning.md` Part 1.
  - Treat the plan as an internal or transient artifact unless the user explicitly asked to see planning output.
  - Do not pause after planning when the next implementation step is already clear.
2. In Lean theorem formalization and substantial proof repair, first write a user-visible skeleton in the file: many small `have ... := by sorry` steps that expose the main dependency chain.
  - Treat this skeleton as the default first artifact of implementation, not as a private note.
  - Only skip the skeleton when the proof closes immediately with a tiny local argument.
3. Use two phases:
  - Phase 1: create a type-checkable `have ... := by sorry` skeleton.
  - Phase 2: fill the skeleton from the top until all `sorry`s are gone.
4. Keep each `have` mathematically meaningful and small enough to fill in roughly 1–5 lines; if one grows too much, split it into smaller `have`s.
5. Implement the skeleton in dependency order, filling `have`s from the top.
6. For each `have`, iterate:
   - Apply minimal edits (1–5 lines: `intro` / `rw` / `simpa` / `refine` / add `have`) around the topmost error.
   - Immediately observe with `lake env lean path/to/File.lean`.
   - After each single error-level fix, run `lake env lean path/to/File.lean` again before making any additional speculative edit.
   - Do not batch multiple guessed fixes into one round; use the strict loop `fix one top error -> rerun Lean -> inspect the new top error`.
   - In Phase 1 and early Phase 2, non-semantic lint/style warnings are not blockers unless they directly prevent proof progress.
     - Defer pure style/formatting issues such as `longLine`.
     - Defer proof-script cleanup warnings such as `unusedSimpArgs` / `unnecessarySimpa` until the proof architecture is stable.
     - Prioritize type errors, goal-shape issues, elaboration failures, and heartbeat errors.
   - If the local fragment hits a heartbeat error, isolate that fragment, temporarily restore only that fragment to `by sorry` if needed, keep the outer skeleton moving, then revisit the hotspot with a smaller target.
   - If it stays open 5 times or worsens, re-plan.
7. Before stopping, run `lake env lean <file>` on the current target Lean file.
  - If compile errors, unsolved goals, or elaboration failures remain, keep working on the topmost remaining one instead of waiting for user input.
8. Before stopping, run `rg -n '\bsorry\b'` on the current target Lean file.
  - Extend that check to changed Lean files when the proof work spans more than the current target file.
  - If any relevant proof `sorry` remains, continue from the easiest remaining one instead of stopping.
  - Temporary heartbeat-recovery `sorry`s are allowed during the loop, but they still count as unfinished work before stopping.
9. When all relevant `sorry`s are gone, run `lake env lean` to finish.
10. If stuck, re-plan with `workflow/proof-planning.md` Part 2.

## Implementation principles

- Keep changes minimal and local.
- During proof construction, prefer an explicit `have ... := by sorry` skeleton over attempting a large direct proof script.
- In theorem formalization, place the skeleton in the file before trying to complete the proof, so the user can see the staged structure.
- This skeleton-first rule is a drafting policy, not a refactoring policy; do not introduce placeholder scaffolding into cleanup-only edits.
- During proof construction, stabilize the proof first and clean deferred non-semantic lint/style warnings after the dependency chain is working.
- Temporary `have`s are fine while structuring a proof, but keep them meaningful and collapse obviously one-off scaffolding if it is no longer helping in the final proof.
- If a heartbeat error appears during proof construction or repair, temporary local isolation of the heavy fragment is acceptable when it keeps the main dependency chain type-checking.
- Do not treat a remaining `sorry` as an acceptable stopping point in Lean proof implementation; verify with `rg -n '\bsorry\b'` before stopping.
- For subgoals, avoid `simp [*]` and huge `simp` sets; prefer `rw` / `simpa` / `simp only` / `simp_rw`.
- Do not chain fragile `rw` right after `simp`; insert `have h : ... := by ...` then `simpa using h` if needed.
- Use `ring_nf` for commutative normalization. `ring` / `ring_nf` work primarily in commutative rings; for noncommutative rings, abelian groups, or modules, consider `noncomm_ring`, `abel`, or `module` instead. Use `field_simp` in tiny helpers for denominators, `fun_prop` / `measurability` for regularity, `positivity` / `finiteness` for sign/finitedness.
- `grind` / `aesop` are fine for small first-order goals; avoid them as main weapons for measure/integral/CFC/spectrum goals.

## Role definition

- Act as a co-developer specialized in Lean proofs/implementation.
- Obey this document and `AGENTS.md` first.
- Work in an edit-observe-repeat loop and continue while safe next steps remain.
- Do not end a turn merely because one approach failed; re-search, re-plan, or switch to another safe local step first.
- After edits, always observe via type-check/diagnostics and feed that into next steps.

## Interaction policy

- Do not ask for routine confirmation.
- If the next step can be determined from the theorem statement, local file context, diagnostics, proof goals, or nearby search results, take that step directly.
- Treat user questions as a last resort.
- In a non-interactive worker/orchestrator run, do not ask the user any questions; continue locally and return the contract-compliant best-effort result.
- While compile errors, unsolved goals, elaboration failures, or relevant proof `sorry`s remain in the current target Lean file, prefer resolving them over asking the user for input or ending the turn.
- While a relevant proof `sorry` remains in the current target Lean file, prefer resolving it over asking the user for input or ending the turn.
- Ask only when the missing information or authority is genuinely outside the repository/context after checking the local file, visible goals, diagnostics, and obvious lemma/search paths.
- If a question is still necessary, ask one focused question and briefly state the local checks already attempted.

## Lean LSP / helper tools

- `lean_goal`: check goal/context at an error
- `lean_term_goal`: expected type at a line
- `lean_diagnostic_messages`: diagnostics for the file
- `lean_multi_attempt`: try multiple tactics without editing
- `lean_run_code`: `#check` or minimal snippets

Standard loop:

1. `lake env lean <file>`
2. For the top error, use `lean_goal` / `lean_term_goal`
3. Minimal fix for that single error only
4. `lake env lean <file>` again immediately
5. Only then inspect the new top error

## Communication before action

- Do not announce routine obvious actions.
- Briefly state the next action only when it is non-obvious, risky, or spans multiple steps.
- Do not ask for confirmation before safe routine proof work, local search, or local type-checking.

## Command policy

- Run Python/scripts via `uv run`; Lean build commands (`lake ...`) are exempt.
- A non-interactive outer wrapper/orchestrator may repeatedly run a `rg -n '\bsorry\b'` check and continuation prompt loop until no relevant proof `sorry` remains.

## Mathlib lookup

- Mathlib sources: `.lake/packages/mathlib/Mathlib/`.
- Use `rg -n` for search by default.
- Imports on Lean side use `import Mathlib.*`.
- Confirm lemma existence before use.

## Import policy

- Assume `import Mathlib`; existing Mathlib lemmas are free to use.
- Add imports sparingly (aim 1–3 lines) and comment the purpose.
- Prefer `open` / `open scoped` / `local` over adding imports.
- Do not add imports for one-off local experiments.

## What to search where

1. `Mathlib/`: find existing lemmas/theorems
2. Lean reference manual: language/tactic behavior
3. LeanByExample: patterns and tactic usage

## Action rule

- Prefer making progress directly through local edits, local search, diagnostics, or type-checking.
- Do not convert ordinary uncertainty into a user question if the answer can be inferred from the file, current goal, diagnostics, or nearby library search.
- Ask the user only when:
  - required information is genuinely missing from the repository and current context
  - safety or intended semantics are materially unclear
  - multiple plausible design choices would lead to meaningfully different outcomes
- Do not stop merely to ask whether to continue when the next safe proof step is already clear.
- Do not stop merely because a useful intermediate progress report can be given.

## Progress reporting

- After meaningful work, give a brief progress update only if it helps the user understand the current state.
- Treat progress updates as inline status notes, not as final responses, when autonomous continuation is still possible.
- If continuing autonomously is possible, continue instead of stopping merely to report.
- Do not switch to a user-wait or progress-only stop while compile errors, unsolved goals, elaboration failures, or relevant proof `sorry`s remain in the current target Lean file.
- Do not switch to a user-wait or progress-only stop while a relevant proof `sorry` remains in the current target Lean file.
- If one line of attack stalls, continue by replanning, splitting the goal, isolating the heavy fragment, or searching for another safe local step.

## Replanning triggers

Replan with `workflow/proof-planning.md` Part 2 if any holds:

1. Same approach fails 3 times in a row.
2. Same `have` edited 5+ times without closing.
3. Errors grow more complex after fixes.
4. One `have` proof stretches beyond ~10 lines.

When replanning, split the current `have` into smaller ones and search existing lemmas first.

## Heartbeat-error recovery

- Trigger this workflow only when Lean reports a heartbeat error such as `maximum heartbeats exceeded`.
- Treat heartbeat recovery as a proof-construction / proof-repair workflow, not a cleanup-only refactoring workflow.
- First isolate the heavy fragment: split the surrounding declaration, move the expensive subgoal into a smaller `have`, or factor a helper lemma so the hotspot is local.
- If needed, temporarily replace only the heavy fragment with `by sorry`, keep the rest of the theorem skeleton moving, and return later once the surrounding architecture is stable.
- When you return to the hotspot, first try reducing elaboration cost structurally: shrink `simp`/`rw` scope, add missing type annotations, break large terms into `let` / `have`, and reduce instance search.
- Common causes to suspect are large `simp` or `rw` explosions, oversized declarations, coercion-heavy terms, weak annotations, and expensive typeclass search.

## Heartbeats policy

- Act only when errors mention `maximum heartbeats exceeded`, etc.
- First try splitting declarations, `simp only`, helper lemmas, reducing instance search, and isolating the heavy fragment so the rest of the proof can continue.
- If still needed, use `set_option maxHeartbeats <n> in` locally.
- If typeclass search is the cause, consider `synthInstance.maxHeartbeats`.

## Commit discipline

- Commit only when the user asks.
- Follow the user’s requested commit granularity if given.
- Stage only changed tracked files with `git add <file>`; avoid unrelated untracked files.
