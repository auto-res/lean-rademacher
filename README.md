# Lean Formalization of Generalization Error Bound by Rademacher Complexity and Dudley's Entropy Integral
[![arXiv](https://img.shields.io/badge/arXiv-2503.19605-b31b1b.svg)](https://arxiv.org/abs/2503.19605)

## Abstract
Understanding and certifying the generalization performance of machine learning algorithms---i.e. obtaining *theoretical* estimates of the test error from a finite training sample---is a central theme of statistical learning theory. Among the many complexity measures used to derive such guarantees, *Rademacher complexity* yields sharp, data-dependent bounds that apply well beyond classical $0$--$1$ classification. In this study, we formalize the generalization error bound by *Rademacher complexity* in Lean 4, building on measure-theoretic probability theory available in the Mathlib library. Our development provides a mechanically-checked pipeline from the definitions of empirical and expected Rademacher complexity, through a formal symmetrization argument and a bounded-differences analysis, to high-probability uniform deviation bounds via a formally proved McDiarmid inequality. A key technical contribution is a reusable mechanism for lifting results from *countable* hypothesis classes (where measurability of suprema is straightforward in Mathlib) to *separable* topological index sets via a reduction to a countable dense subset. As worked applications of the abstract theorem, we mechanize standard empirical Rademacher bounds for linear predictors under $\ell_2$ and $\ell_1$ regularization, and we also formalize a Dudley-type entropy integral bound based on covering numbers and a chaining construction.

### Major updated:
(2026 Jan) We have formalized **Dudley's entropy integral bound** for Rademacher complexity for the first time.
(2026 Feb) We have formalized **Lasso, or $L^1$-regularization bound**

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
`Main.lean` imports the public API and gives end-to-end examples.  The
abstract bounds are implemented in `Generalization.lean`,
`SeparableGeneralization.lean`, and `Confidence.lean`; model-specific
corollaries live in the corresponding `*Generalization.lean` files.
Core definitions remain in `Defs.lean`.  Selected declarations include:
- `uniform_deviation_tail_bound_separable`
  - (Main Theorem) Generalization error bound using Rademacher complexity
- `empiricalRademacherComplexity` *et al.*
  - Definition(s) of Rademacher complexity 
- `empiricalRademacherFunctional`
  - Common finite-sign functional specializing to the absolute and one-sided empirical complexities
- `empiricalRademacherComplexity_reindex_le` *et al.*
  - Monotonicity and surjective-invariance API for reindexing a hypothesis class
- `uniform_deviation_mcdiarmid_tail`
  - McDiarmid inequality (for deviations)
- `empiricalRademacherComplexity_lower_tail_countable_of_pos`
  - Lower-tail concentration of empirical Rademacher complexity
- `uniform_deviation_tail_bound_separable_of_empirical_complexity`
  - Data-dependent high-probability uniform-deviation bound using the empirical Rademacher complexity of the observed sample
- `uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta`
  - Confidence-parameter bound from an arbitrary samplewise estimate $\widehat{\mathfrak R}_n(F;S)\le C(S)$
- `linear_predictor_l2_bound`
  - Fixed-sample empirical Rademacher bound for $L^2$-regularized linear predictors
- `linear_predictor_l2_rademacher_complexity_bound`
  - Expected Rademacher bound for the full $L^2$-bounded linear class
- `linear_predictor_l2_uniform_deviation_tail_bound_delta`
  - End-to-end confidence bound for the full $L^2$-bounded linear class
- `linear_predictor_l2_uniform_deviation_tail_bound_of_sample_delta`
  - Data-dependent end-to-end confidence bound retaining the observed sum of squared input norms
- `linear_predictor_l1_bound`
  - Fixed-sample empirical Rademacher bound for $L^1$-regularized linear predictors
- `linear_predictor_l1_rademacher_complexity_bound`
  - Expected Rademacher bound for the full $L^1$-bounded linear class
- `linear_predictor_l1_uniform_deviation_tail_bound_delta`
  - End-to-end confidence bound for the full $L^1$-bounded linear class
- `linear_predictor_l1_uniform_deviation_tail_bound_of_sample_delta`
  - Data-dependent end-to-end confidence bound retaining the observed coordinatewise empirical $L^2$ radius
- `dudley_entropy_integral_bound`
  - Dudley's entropy integral bound for one-sided empirical Rademacher complexity
- `dudley_entropy_integral_bound_abs`
  - Dudley's entropy integral bound for absolute empirical Rademacher complexity via sign symmetrization
- `rademacher_complexity_le_dudley_of_uniform_entropy`
  - Expected Rademacher bound from a sample-uniform Dudley entropy estimate
- `uniform_deviation_tail_bound_separable_of_uniform_dudley`
  - End-to-end high-probability uniform-deviation bound from a sample-uniform Dudley entropy estimate
- `uniform_deviation_tail_bound_separable_of_dudley`
  - Data-dependent high-probability uniform-deviation bound using Dudley's entropy integral on the observed sample
- `uniform_deviation_tail_bound_separable_of_dudley_delta`
  - Confidence-parameter form of the observed-sample Dudley bound

### Future plans
Contributors are always welcome! (Contact: [Discord](https://discord.gg/wdTpRCR8fW))
- Examples of generalization error bounds such as
  - for RKHS
- Examples of *covering numbers* $N$ (of a function sets $H$ w.r.t. sup-norm or empirical-norm to instantiate Dudley's entropy bound) such as
  - the unit ball of Lipschitz-continuous functions on a compact set $K \subset \mathbb{R}^d$
  - neural networks with bounded weights
- Brushing-up key definitions/inequalies such as Rademacher complexity, Dudley's entropy bound, Azuma-Hoeffding, McDiarmid, ...

### Contributors
Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
