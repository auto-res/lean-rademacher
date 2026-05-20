description: Lean 4 proof planning guide (initial planning & dynamic replanning)
alwaysApply: false
---

# Lean 4 Proof Planning Guide

Use this document for **planning and replanning proofs**.
During implementation, repo-local rules in `AGENTS.md` and `.codex/skills/lean-rule/SKILL.md` take priority.

Some formatting rules here are inspired by olympiad-style planning and should not be auto-applied to general Lean implementation (measure/topology/operator/matrix).

## Overview

This guide covers two scenarios:

1. **Initial Planning**: build a proof plan from the theorem statement.
2. **Dynamic Replanning**: replan the remaining proof from proven parts and stuck goals.

## Common rules (repo-local planning)

1. For Lean theorem formalization, planning output should normally be a `have ... := by sorry` skeleton.
   - A plain list of `have` statements is acceptable only for tiny local arguments or planning-only requests.
   - Treat that output as an internal or transient artifact unless the user explicitly asked for planning output.
   - When implementation can proceed safely, do not stop after producing the plan.
2. Keep `have` granularity small (aim 1–5 lines to fill).
3. Use existing mathlib names; do not coin lemma names.
4. Introduce new variables/functions/indices locally with `let` / `set` / `have` / explicit binders.
5. Match interval/set notation to downstream API; using `Set.Icc`, `Set.Ioo`, etc. is fine.
6. Add numeric type annotations when ambiguity exists (division/subtraction/coercions).
7. Use existing named theorems/inequalities when they shorten proofs and fit the API.
8. Always write multiplication `*` explicitly.
9. Avoid chained inequalities; split with `∧` if needed.
10. In replanning, preserve proven parts and split stuck goals into smaller `have`s.
11. Use notation-first style **by default** for seeds, expansions, and claims.
   - If notation is unavailable or ambiguous, fall back to fully qualified names, and add a short note in the plan that explains why.

## Part 1: Initial Planning

### Task

Analyze a Lean 4 theorem statement and design a coherent chain of `have` steps from assumptions to conclusion.

Break complex arguments into small lemmas that can be implemented in the same session. In planning, prioritize dependencies and order over full proofs, then continue directly into implementation unless blocked.

### Instructions

- Understand the main structure of the theorem.
- Prefer `have` steps that form key branching points over immediate closures.
- Order `have`s as a logical chain toward the theorem.
- Use `have ... := by sorry` skeletons by default so the dependency order becomes a type-checkable first draft.

### Example (format)

**Input:**

```lean
theorem sample (x : ℝ) (hx : 0 < x) : x + x = 2 * x := by
```

**Planning Output:**

```lean
have h1 : x + x = x * 2 := by sorry
have h2 : x * 2 = 2 * x := by sorry
```

### Next step: immediate continuation into implementation

1. Place each `have` with `by sorry` temporarily.
2. Fill them one by one, fixing errors top-down.
3. If stuck, go to Part 2 (Dynamic Replanning).
4. Do not stop after this planning stage when a safe implementation step is already clear.

## Part 2: Dynamic Replanning

### Task

When progress stalls, replan the remaining proof from the current theorem state, the already established local facts, and the current outstanding goals.

Use the local file, current diagnostics, visible goals, and existing partial proof as the default source of truth. In non-interactive formalize/repair worker runs, do not ask the user to restate proven steps or stuck goals; continue from the available context.

### Additional Rules

#### 11. Preserve Established Steps

Keep already established proof steps unless there is a clear reason they must be changed.

#### 12. Provide a Complete Updated Plan

Update the local proof plan so it includes retained steps and newly introduced helper steps, then resume implementation from that updated plan.

#### 13. Ensure Logical Continuity

Insert new helper `have` steps in a natural logical order. Prefer smaller intermediate facts over repeating the stuck goal in slightly different words.

### Practical Guidance for Dynamic Replanning

- Do not attack the stuck goal directly if simpler side goals can be isolated first.
- Reuse proven local facts before introducing new ones.
- Prefer narrowing the gap with smaller helper lemmas over discarding the whole plan.
- Treat replanning as a way to continue implementation, not as a stopping point by itself.
- Escalate to the user only in interactive sessions. In non-interactive worker runs, choose the most conservative locally supported continuation instead.

## Notes

- This document is a planning helper, not the repo-wide implementation policy.
- Using `Set.Icc` / `Set.Ioo`, introducing new helper vars/indices/`let` is fine if it matches project API.
- In theorem formalization, a type-checkable `have ... := by sorry` skeleton is the normal first implementation artifact.
