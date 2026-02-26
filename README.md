# Lean Formalization of Generalization Error Bound by Rademacher Complexity
[![arXiv](https://img.shields.io/badge/arXiv-2503.19605-b31b1b.svg)](https://arxiv.org/abs/2503.19605)

## Abstract
We formalize a generalization error bound via **Rademacher complexity** in the Lean 4 theorem prover, building on measure-theoretic probability in Mathlib 4.
Generalization error quantifies the gap between a learning machine's performance on a finite training sample and its performance on unseen test data; Rademacher complexity provides sharp, data-dependent uniform deviation bounds for broad classes of real-valued losses.

Our development provides a mechanically checked pipeline that mirrors textbook proofs:
(1) definitions of empirical and expected Rademacher complexity and the uniform deviation functional,
(2) a formal **symmetrization** argument connecting uniform deviations to Rademacher averages, and
(3) a **bounded-differences** analysis culminating in a formally proved **McDiarmid inequality**, yielding high-probability bounds.

A key technical contribution is a reusable mechanism to lift results from **countable** hypothesis classes (where measurability of suprema is straightforward in Mathlib) to **separable** topological index sets via reduction to a countable dense subset under suitable continuity assumptions.

As worked applications, we mechanize standard empirical Rademacher bounds for linear predictors under both **ℓ2** and **ℓ1** regularization, and we also formalize a **Dudley-type entropy integral bound** based on covering numbers and a chaining construction.

### Major updated:
(2026 Jan) We have formalized **Dudley's entropy integral bound** for Rademacher complexity for the first time.

## How to Run
- Open a terminal. Run the following commands.
  ```bash
  git clone https://github.com/auto-res/lean-rademacher.git
  cd lean-rademacher

  # get Mathlib4 cache 
  lake exe cache get
  ```
- Launch VS code,
- open the folder ```lean-rademacher```,
- select the file ```FoML/Main.lean```, and
- push ```Restart File``` button to rebuild the project.

## Contents (selected)
Key theorems (resp. definitions) are gathered in `Main.lean` (resp. `Defs.lean`), e.g.
- `FoML.Main.main_separable`
  - (Main Theorem) High-probability uniform deviation / generalization bound via Rademacher complexity
    for **separable** index sets (countable case is available as an intermediate theorem as well).
- `FoML.Defs.empiricalRademacherComplexity` *et al.*
  - Definitions of (empirical / expected) Rademacher complexity and the uniform deviation functional
- `FoML.Main.uniformDeviation_mcdiarmid`
  - McDiarmid inequality (bounded-differences) specialized to uniform deviation bounds
- `FoML.Main.linear_predictor_l2_bound`
  - Example: generalization-relevant bound for **ℓ2**-regularized linear predictors
- `FoML.Main.linear_predictor_l1_bound`
  - Example: generalization-relevant bound for **ℓ1**-regularized linear predictors
- `FoML.Main.dudley_entropy_integral`
  - Dudley's entropy integral bound for (empirical) Rademacher complexity (covering numbers + chaining)

### Future plans
Contributors are always welcome! (Contact: [Discord](https://discord.gg/wdTpRCR8fW))

- More examples / instantiations
  - RKHS (kernel methods): Rademacher bounds via norm constraints and/or covering-number estimates
  - Neural networks with bounded weights (plugging into Dudley's bound via explicit covering numbers)

- Covering numbers & entropy calculations (to instantiate Dudley’s bound)
  - Unit ball of Lipschitz-continuous functions on a compact set `K ⊂ ℝ^d`
  - Common hypothesis classes used in modern learning theory (e.g. linear classes under different norms)

- Inequalities and “glue” lemmas that broaden applicability
  - Contraction inequalities for Lipschitz losses (e.g. for composing with a 1-Lipschitz loss)
  - Connections to Gaussian complexity / sub-Gaussian process tools (optional but powerful)

- Engineering / Mathlib integration
  - Better automation for routine measurability / integrability goals
  - Refactoring core definitions and proof scripts to improve reuse and readability
