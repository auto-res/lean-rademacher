---
name: lean-review-refactor-policy
description: "Policy for non-semantic refactors that keep math meaning unchanged while making Lean/Mathlib code easier to review and harder to break: minimal imports, scoped assumptions, localized `classical`, proof tidying, lint fixes, perf/typeclass risk control, and PR splitting."
metadata:
  short-description: Best practices for Lean refactors (review-focused)
  audience: Lean/Mathlib contributors
  scope: non-semantic refactor & review hygiene
---

# Lean refactor policy for review (best practices)

This skill is a practical checklist and procedure to make Lean/Mathlib code **keep its mathematical meaning and public API** while becoming:

- easier to read
- easier to review
- less likely to break in the future
- less likely to worsen build/typeclass search

Here, **non-semantic** means at least:

- Do not change statements (types) of public theorems/defs.
- Do not change public names/namespace layout without need.
- Do not change typeclass inference results, simp sets, or the instance environment.
- If removing imports could break downstream, fix downstream or split into another PR.

---

## 0. Scope and terms

### 0.1 In-scope (OK)

- Proof tidying (`have` granularity, `calc`, replacing `simp`/`rw`, etc.).
- Removing/localizing `classical` (`by classical`).
- Cleaning section/namespace/variable blocks **without changing statements**.
- Import cleanup (watch downstream impact).
- Fixing lint/style warnings (`show`→`change`, removing `by exact`, etc.).

### 0.2 Considered non–non-semantic (generally NO; separate PR)

These affect behavior/API even if math is unchanged:

- New global instances or changes to existing ones (including priority).
- Adding/removing `@[simp]` or other simp-affecting attributes.
- Adding/changing coercions/notation (`Coee`/`OfNat`/`Pow`, etc.).
- Renaming/moving/deleting theorems/defs/lemmas or namespaces.
- Changing transparency (`def`→`abbrev`/`opaque`).
- Statement changes via generalization/assumption changes (even “good” ones) — prefer separate PR.
- Introducing heavy automation (`aesop`/`simp_all`/`omega`, etc.) that increases search/uncertainty.
- Committing `set_option` (trace/pp/heartbeats, etc.) that changes behavior.

Exception: if you must bundle, clearly note design changes and impact in the PR and get reviewer buy-in.

---

## 1. Guardrails (most important)

### 1.1 Must-follow

- Do **not** change statements of public theorems/defs.
- Do **not** change public names (if renaming is needed, add deprecated/alias in a separate PR).
- Do **not** add new global instances or simp attributes.
- Do **not** break downstream relying on current imports (if it would, fix downstream or split PR).

### 1.2 Self-check for “non-semantic”

- Could this change typeclass inference results?
- Could it change `simp` results? (attributes/imports/local attributes?)
- Do downstream files rely on this file’s transitive imports?
- Did you touch `def`/`abbrev`/`opaque` transparency?

---

## 2. Base workflow (low risk order)

### 2.1 Stabilize current state first

- Build the target module in the smallest scope: `lake build <Module>`.
- Note existing warnings/lints/timeouts and avoid increasing them (ideally reduce).

### 2.1.1 Interaction default

- Do not ask for routine confirmation during refactors.
- If the change is clearly non-semantic and can be validated from local code, diagnostics, and build results, proceed directly.
- Ask only when semantic intent or review scope cannot be resolved from repository context.
- If one refactor approach stalls, try another safe local validation or smaller edit before requesting input.

### 2.2 Make changes small and separated by intent

- One commit = one intent (e.g., `show`→`change`, import cleanup, `classical` localization…).
- Keep each commit `lake build`-clean to ease review.

### 2.3 Finish with full build

- Before PR: `lake build` (whole project); reproduce CI options/targets if any.

### 2.4 Linter triage during proof construction / repair

- Do not treat every linter warning as an immediate blocker while the proof still has type errors, unsolved goals, or heartbeat failures.
- During proof construction, use the following priority order:
  - `P0` (do not defer casually): warnings that may affect the apparent public API or assumptions, especially `unusedArguments` / `unusedSectionVars` on public declarations.
  - `P1` (can usually wait until the proof skeleton is stable): proof-script cleanup warnings such as `unusedSimpArgs` / `unnecessarySimpa`.
  - `P2` (safe to defer during construction): pure style/formatting warnings such as `longLine` and similar readability-only issues.
- Preferred construction order:
  1. Make the dependency chain type-check.
  2. Remove `sorry`s and heartbeat hotspots.
  3. Revisit deferred `P1` / `P2` warnings with small localized cleanup.
- “Defer” means “non-blocking for the current proof step”, not “ignore forever”. Before finishing a proof-focused edit, either clean the warning up or leave it intentionally localized with minimal scope.

---

## 3. Minimizing imports (mind the API surface)

### 3.1 Principle

- Import precise modules instead of `import Mathlib`.
- Remove unused imports (ensure builds succeed).

### 3.2 Caution: removing imports can break downstream

Imports are transitive. Downstream may rely on this file’s imports implicitly.

- A file can build, yet downstream breaks.
- Best practice:
  - Add required imports explicitly to downstream to fix dependencies.
  - If large, split import minimization into a separate PR.

### 3.3 `#min_imports` usage (recommended way)

- Use `#min_imports` as a temporary hint tool:
  1) Temporarily place `#min_imports`.
  2) Adjust imports per suggestion.
  3) Remove `#min_imports` before committing (avoid noise).

---

## 4. Variable/assumption (typeclass) scoping

### 4.1 Goals

- Reduce typeclass search burden.
- Reduce accidental dependencies on unused assumptions.

### 4.2 Effective steps (priority)

1. Use local `variable` blocks.
2. Split `section` smaller.
3. Use `omit [...] in` sparingly (readability cost).

### 4.3 Style for `omit`

- Raises cognitive load; use only when the reason is clear at that position.
- Avoid chained/multi `omit` blocks.

### 4.4 Do not change statements

- When reorganizing `variable [...]`, keep lemma types unchanged. Generalization/reduction of assumptions should be another PR for review stability.

---

## 5. Handling `classical` (remove or localize)

### 5.1 Principle

- Drop it if unnecessary.
- If needed, localize to minimal scope:
  - `by classical` inside lemmas
  - Minimal `section` scope

### 5.2 Common pitfalls

- Removing `classical` may destabilize `simp`/`by_contra` contexts; if so, mark where classical is required and localize back.

---

## 6. Proof formatting best practices

### 6.1 `show` vs `change`

- Use `change` when altering the goal type.
- `show` is for exhibiting the current type; using it to change goals triggers lint.
- For aligning definitional equalities of `let`/`abbrev`, `dsimp [..]` is often enough (e.g., `dsimp [hA, hA2]`).

### 6.2 Remove `by exact`

- `by exact h` → `exact h`
- `by\n    exact h` → `simpa using h` / `exact h` depending on context.

### 6.3 `have` granularity

- Use `have` for reusable/meaningful steps.
- Inline one-off short facts: `exact ...` / `simpa using ...` / `refine ...`.

### 6.4 `simp` vs `simpa`

- Follow linter preference for `simp`.
- Use `simpa` when you also reshape the goal or want to show what vanished.

### 6.5 `simp` stability

- If you need specific lemmas only: `simp [h1, h2]`; for robustness, consider `simp only [...]` (at the cost of verbosity).
- Good workflow: use `simp?` to see which lemmas are used, then pin them.

### 6.6 `simp` anti-patterns (avoid)

- Overusing `simp [*]` / `simp_all` (explodes search, brittle).
- Stuffing many lemmas into `simp` (hard to review what fired).
- Leaving direction unspecified; prefer `simp [← lemma]` or `rw` to orient.

### 6.7 `rw` / `simp_rw` / `nth_rewrite`

- Single rewrite: `rw`.
- Mix `simp` and rewrites: `simp_rw`.
- Target occurrences: `nth_rewrite`.

### 6.8 When to use `calc`

- When reviewers need to follow equality/inequality flow.
- Use `calc` instead of one-shot `simp` when math steps should remain visible.

### 6.9 Automation (`aesop`, etc.)

- In non-semantic refactors, **do not introduce stronger automation**; risk: search/heartbeats/behavior drift.
- Tuning existing automation is OK if build time does not worsen.

### 6.10 Main theorem reuse preference

- When refactoring a main-theorem-style proof in `Derived.lean`, prefer proof structure that explicitly reuses earlier `Derived.lean` theorems rather than re-deriving the same argument from axioms.
- If a theorem is intended as a structural summary of an existing cluster, its proof should make that reuse visible when possible through `exact`, `simpa`, short `have`s, or targeted rewrites.
- Only keep a direct-from-axioms proof when no stable reuse path exists or the reuse version would be materially more brittle.

---

## 7. `def` / `abbrev` / `opaque` (transparency)

### 7.1 Principle: transparency changes are design changes

- `def`→`abbrev` changes reducibility.
- `def`→`opaque` changes unfolding.

Therefore avoid touching transparency in non-semantic refactors.

### 7.2 When `abbrev` is still acceptable

- As notation/abbreviation for repeated long terms where unfoldability is harmless.
- Be cautious if exposed at API boundaries.

---

## 8. Instance policy (highest risk)

### 8.1 In non-semantic refactors

- **Do not add new global instances.**
- If you must, prefer: separate PR; scoped/local instances or wrapper types to isolate.

### 8.2 If handling instances anyway (design PR guidance)

- State in PR: which type gets which structure, why no conflicts, priorities, and impact on import cycles/build time.

---

## 9. `local attribute` / `open scoped` / `set_option`

### 9.1 Principle

- `local attribute [simp] ...` changes proof behavior; generally avoid adding in non-semantic refactors (if needed, keep minimal scope or separate PR).
- `open scoped ...` can affect notation/simp/instances; add/remove carefully with a reason.
- `set_option` (trace/pp/heartbeats, etc.):
  - Do not commit for debugging.
  - If necessary, minimize scope and explain in PR.
  - For `maxHeartbeats`, first try lighter proofs; if still needed: `set_option maxHeartbeats N in`, use minimal `N`, add a one-line reason, and separate from pure refactor changes.
  - Avoid leaving commented `-- set_option ...`; either localize or remove.

---

## 10. Names/module structure (API practice)

### 10.1 Renames are separate PRs (principle)

- Renames/moves/deletions break downstream; avoid in non-semantic refactors.

### 10.2 If renaming is unavoidable (design PR)

- Keep old names (deprecated/alias).
- Provide migration window.
- Call out the breaking change in PR text.

---

## 11. File deletion/move

- File removal is never non-semantic.
- Even with zero deps, future context can break.
- So: use a separate PR, or move to `Archive/` to separate impact.

---

## 12. Performance/stability checks

Lean changes can slow or destabilize even if they pass.

- Watch for increased typeclass search (new instances/imports).
- Watch for heavier `simp` (more/longer `simp` lines).
- Avoid strong escapes like raising/zeroing `maxHeartbeats`; if used, localize, justify, and separate.

---

## 13. PR management (bundle vs split)

### 13.1 Split recommended

Prefer separate PRs for:

- Pure refactors (format/lint).
- Import cleanup (may need downstream fixes).
- Renames (with deprecated/alias).
- Instance additions/changes.
- File moves/deletions.

### 13.2 PR text template

- Purpose (why now).
- Change categories: lint cleanup / import cleanup / classical removal-localization / assumption scoping / proof tidying.
- Impact: confirm API (names/statements) unchanged; note instance/simp/import changes; build scope checked.

---

## 14. Review output format (expectation)

- Classify changes by intent:
  - lint
  - import cleanup
  - `classical` removal/localization
  - assumption scoping
  - proof formatting
  - naming (should be separate PR)
- For each category:
  - key before/after points
  - why it is safe (non-semantic rationale)
  - Lean side effects (typeclass search, simp, import cycles, build time)
- Merge guidance: take / split / needs design discussion.

---

## 15. Core/generalization/wrapper (design refactor checkpoints)

Generalizing core proofs and wrapping specific cases (e.g., `B(ℋ)`) improves readability/extension but mixes order/instance/simp issues. Fix the process:

### 15.1 Core/Wrapper responsibilities (minimal setup)

- **Core (general `A`)**:
  - Put defs and main theorems (generalized statements).
  - **Do not bake specific orders (e.g., `spectralOrder`) into core**; accept `[PartialOrder A]` externally.
  - Additional classes (e.g., `NonnegSpectrumClass`) should be stated only at the needed layer.
- **Wrapper (concrete `B(ℋ)` etc.)**:
  - `simpa using` to specialize core (no duplicate proofs).
  - Respect existing ecosystem/orders on the concrete type (e.g., Loewner order).
  - If order must change, isolate with `local instance` in the wrapper (next subsection).

### 15.2 Pattern for swapping order (avoid leaking `spectralOrder`)

- Principle: order swaps should be separate PRs (API/simp/lemma applicability can break).
- If you must provide it, confine to a dedicated namespace wrapper.

```lean
namespace FooCore.Spectral

variable {A : Type u} [CStarAlgebra A]
-- Do not require the original order here (avoid conflicts)

section
  -- Important: close instances locally (do not leak globally)
  local instance : PartialOrder A := CStarAlgebra.spectralOrder A
  local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  local instance : NonnegSpectrumClass ℝ A := inferInstance

  theorem main_thm_spectral : ... := by
    simpa using FooCore.main_thm (A := A)
end
```
