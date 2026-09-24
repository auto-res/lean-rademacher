import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
import FoML.ToMathlib.GaussianPi

/-!
# Gaussian integration by parts (Stein's identity) on `Fin M → ℝ`

Prerequisite G4 of the Bernoulli–Sudakov plan (`PLAN.md` §7).

Let `γ = stdGaussianPi M = Measure.pi (fun _ : Fin M => gaussianReal 0 1)` be the standard
Gaussian measure on `ℝ^M`. For `F : (Fin M → ℝ) → ℝ` with partial derivative `∂_i F`
(in the sense `HasDerivAt (fun t => F (Function.update x i t)) (∂_i F x) (x i)` for every `x`),
\[ \int x_i\, F(x)\, d\gamma(x) = \int \partial_i F(x)\, d\gamma(x) \]
(`integral_mul_stdGaussianPi_eq_integral_partial`, `thm:gaussian-ibp`).

**Growth hypotheses.** `F` and `∂_i F` are measurable, `|F(x)| ≤ C (1 + ‖x‖)` (at most linear
growth) and `|∂_i F(x)| ≤ C` (bounded), where `‖x‖ = max_i |x_i|` is the sup norm on `Fin M → ℝ`.
This is enough for the Sudakov–Fernique application (`F` = log-sum-exp or a softmax composed with
a linear map), and keeps the integrability bookkeeping minimal.

**Route.** The one-dimensional identity `∫ t h(t) dγ₁ = ∫ h'(t) dγ₁` for `γ₁ = gaussianReal 0 1`
(`integral_mul_gaussianReal_eq_integral_deriv`) follows from `φ'(t) = −t φ(t)` for the standard
normal density `φ` and Mathlib's integration by parts on `ℝ`
(`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`); then Fubini on
`Measure.pi = γ₁ ⊗ (Measure.pi over the other coordinates)` through
`MeasurableEquiv.piFinSuccAbove` and `MeasureTheory.measurePreserving_piFinSuccAbove`.

The corollary for compositions with a linear map `x ↦ A x` (`cor:gaussian-ibp-linear`,
`integral_mulVec_mul_eq_sum_integral`):
\[ \int (A x)_j\, f(A x)\, d\gamma = \sum_k \Big(\sum_i A_{ji} A_{ki}\Big)
   \int \partial_k f(A x)\, d\gamma, \]
i.e. `E[X_j f(X)] = ∑_k Cov(X_j, X_k) E[∂_k f(X)]` for the centred Gaussian vector `X = A g`.

The measure `γ = stdGaussianPi M` is the one of `FoML.ToMathlib.GaussianPi`; the
auxiliary integrability lemmas `integrable_eval_and_sq_stdGaussianPi` (`x_k` and `x_k^2`) and
`integrable_norm_sq_stdGaussianPi` (`‖x‖_∞^2`) are proved here.

This file depends only on Mathlib and `FoML.ToMathlib.GaussianPi` (and `Architect` for the
blueprint annotations).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

namespace FoML.ToMathlib

section OneDim

/-! ### The one-dimensional identity -/

/- @[blueprint "lem:gaussianPDF-hasDerivAt"
  (statement := /-- The standard normal density $\varphi(t) = (2\pi)^{-1/2} e^{-t^2/2}$ satisfies
    $\varphi'(t) = -t\,\varphi(t)$. -/)] -/
theorem hasDerivAt_gaussianPDFReal_zero_one (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-t * gaussianPDFReal 0 1 t) t := by
  have h : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
      (-(2 * (t - 0) ^ 1 * 1) / (2 * ((1 : ℝ≥0) : ℝ))) t :=
    (((hasDerivAt_id t).sub_const 0).pow 2).neg.div_const _
  have := h.exp.const_mul (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
  refine this.congr_deriv ?_
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, pow_one]
  ring

/- @[blueprint "lem:integrable-gaussianReal-iff"
  (statement := /-- $g$ is integrable for $N(0,1)$ iff $g\varphi$ is Lebesgue integrable. -/)] -/
theorem integrable_gaussianReal_zero_one_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun t => g t * gaussianPDFReal 0 1 t) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]

/- @[blueprint "lem:gaussian-ibp-1d"
  (statement := /-- \textbf{One-dimensional Stein identity.} If $h$ is differentiable on
    $\mathbb R$ with derivative $h'$, and $h$, $h'$, $t\,h(t)$ are integrable for $N(0,1)$, then
    $\int t\,h(t)\,d\gamma_1(t) = \int h'(t)\,d\gamma_1(t)$. -/)] -/
theorem integral_mul_gaussianReal_eq_integral_deriv {h h' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt h (h' t) t)
    (hi : Integrable h (gaussianReal 0 1)) (hi' : Integrable h' (gaussianReal 0 1))
    (hti : Integrable (fun t => t * h t) (gaussianReal 0 1)) :
    ∫ t, t * h t ∂(gaussianReal 0 1) = ∫ t, h' t ∂(gaussianReal 0 1) := by
  set φ := gaussianPDFReal 0 1 with hφdef
  have hφ : ∀ t, HasDerivAt φ (-t * φ t) t := hasDerivAt_gaussianPDFReal_zero_one
  have h1 : Integrable (h * fun t => -t * φ t) := by
    have := ((integrable_gaussianReal_zero_one_iff _).1 hti).neg
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [Pi.neg_apply, Pi.mul_apply]
    ring
  have h2 : Integrable (h' * φ) := (integrable_gaussianReal_zero_one_iff _).1 hi'
  have h3 : Integrable (h * φ) := (integrable_gaussianReal_zero_one_iff _).1 hi
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (v := φ) (u' := h')
    (v' := fun t => -t * φ t) (fun t _ => hd t) (fun t _ => hφ t) h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have e1 : ∫ t, φ t * (t * h t) = -∫ t, h t * (-t * φ t) := by
    rw [← integral_neg]
    congr 1
    funext t
    ring
  rw [e1, key, neg_neg]
  congr 1
  funext t
  ring

/- @[blueprint "lem:integrable-id-gaussianReal"
  (statement := /-- $t$ and $t^2$ are $N(0,1)$-integrable. -/)] -/
theorem integrable_id_and_sq_gaussianReal :
    Integrable (fun t : ℝ => t) (gaussianReal 0 1) ∧
      Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) := by
  have h1 := memLp_id_gaussianReal (μ := 0) (v := 1) 1
  have h2 := memLp_id_gaussianReal (μ := 0) (v := 1) 2
  simp only [ENNReal.coe_one, ENNReal.coe_ofNat] at h1 h2
  exact ⟨memLp_one_iff_integrable.1 h1, h2.integrable_sq⟩

/- @[blueprint "lem:gaussian-ibp-1d-growth"
  (statement := /-- \textbf{One-dimensional Stein identity, growth form.} If $h$ is differentiable
    with $|h(t)| \le C(1 + |t|)$ and $|h'(t)| \le C$, then
    $\int t\,h(t)\,d\gamma_1 = \int h'(t)\,d\gamma_1$. -/)] -/
theorem integral_mul_gaussianReal_eq_integral_deriv_of_bounded {h h' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt h (h' t) t) {C : ℝ}
    (hh : ∀ t, |h t| ≤ C * (1 + |t|)) (hh' : ∀ t, |h' t| ≤ C) :
    ∫ t, t * h t ∂(gaussianReal 0 1) = ∫ t, h' t ∂(gaussianReal 0 1) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hh' 0)
  have hcont : Continuous h := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hh'eq : h' = deriv h := funext fun t => (hd t).deriv.symm
  have hmeas' : Measurable h' := hh'eq ▸ measurable_deriv h
  obtain ⟨hint1, hint2⟩ := integrable_id_and_sq_gaussianReal
  have hbound : Integrable (fun t : ℝ => C * (2 + 2 * t ^ 2)) (gaussianReal 0 1) :=
    ((integrable_const (2 : ℝ)).add (hint2.const_mul 2)).const_mul C
  refine integral_mul_gaussianReal_eq_integral_deriv hd ?_ ?_ ?_
  · refine hbound.mono' hcont.measurable.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs]
    refine (hh t).trans (mul_le_mul_of_nonneg_left ?_ hC)
    nlinarith [abs_nonneg t, sq_abs t]
  · refine (integrable_const C).mono' hmeas'.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs]; exact hh' t
  · refine hbound.mono' (measurable_id.mul hcont.measurable).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |t| * |h t| ≤ |t| * (C * (1 + |t|)) := mul_le_mul_of_nonneg_left (hh t) (abs_nonneg t)
      _ ≤ C * (2 + 2 * t ^ 2) := by nlinarith [abs_nonneg t, sq_abs t, mul_nonneg hC (abs_nonneg t)]

end OneDim

section Pi

/-! ### The standard Gaussian measure on `Fin M → ℝ` -/

variable {M : ℕ}

/- @[blueprint "lem:integrable-eval-std-gaussian-pi"
  (statement := /-- $x_k$ and $x_k^2$ are $\gamma_M$-integrable. -/)] -/
theorem integrable_eval_and_sq_stdGaussianPi (k : Fin M) :
    Integrable (fun x : Fin M → ℝ => x k) (stdGaussianPi M) ∧
      Integrable (fun x : Fin M → ℝ => x k ^ 2) (stdGaussianPi M) := by
  obtain ⟨h1, h2⟩ := integrable_id_and_sq_gaussianReal
  have hmp := measurePreserving_eval_stdGaussianPi k
  exact ⟨(hmp.integrable_comp aestronglyMeasurable_id).2 h1,
    (hmp.integrable_comp (measurable_id.pow_const 2).aestronglyMeasurable).2 h2⟩

/- @[blueprint "lem:norm-sq-le-sum-sq"
  (statement := /-- $\|x\|_\infty^2 \le \sum_k x_k^2$. -/)] -/
theorem norm_sq_le_sum_sq (x : Fin M → ℝ) : ‖x‖ ^ 2 ≤ ∑ k, x k ^ 2 := by
  have hS : 0 ≤ ∑ k, x k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have : ‖x‖ ≤ √(∑ k, x k ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hS, sq_abs]
    exact single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (mem_univ k)
  calc ‖x‖ ^ 2 ≤ (√(∑ k, x k ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = ∑ k, x k ^ 2 := Real.sq_sqrt hS

/- @[blueprint "lem:integrable-norm-sq-std-gaussian-pi"
  (statement := /-- $\|x\|_\infty^2$ is $\gamma_M$-integrable. -/)] -/
theorem integrable_norm_sq_stdGaussianPi :
    Integrable (fun x : Fin M → ℝ => ‖x‖ ^ 2) (stdGaussianPi M) := by
  have hsum : Integrable (fun x : Fin M → ℝ => ∑ k, x k ^ 2) (stdGaussianPi M) :=
    integrable_finsetSum _ fun k _ => (integrable_eval_and_sq_stdGaussianPi k).2
  refine hsum.mono' (continuous_norm.pow 2).measurable.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_sq_le_sum_sq x

/- @[blueprint "lem:norm-insertNth-le"
  (statement := /-- $\|(t, y)\|_\infty \le |t| + \|y\|_\infty$ for the insertion of $t$ at
    coordinate $i$. -/)] -/
theorem norm_insertNth_le {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    ‖Fin.insertNth (α := fun _ => ℝ) i t y‖ ≤ |t| + ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_iff_succAbove i]
  refine ⟨?_, fun j => ?_⟩
  · simp only [Fin.insertNth_apply_same, Real.norm_eq_abs]
    linarith [norm_nonneg y]
  · simp only [Fin.insertNth_apply_succAbove]
    linarith [norm_le_pi_norm y j, abs_nonneg t]

end Pi

section IBP

/-! ### Gaussian integration by parts on `Fin M → ℝ` -/

variable {M : ℕ}

/- @[blueprint "thm:gaussian-ibp"
  (statement := /-- \textbf{Gaussian integration by parts (Stein's identity).} Let
    $\gamma = N(0,1)^{\otimes M}$ and $F : \mathbb R^M \to \mathbb R$ be measurable with a partial
    derivative $\partial_i F$ in the $i$-th coordinate at every point (i.e.\ $t \mapsto
    F(x[i \leftarrow t])$ is differentiable at $t = x_i$ with derivative $\partial_i F(x)$),
    $\partial_i F$ measurable, and suppose the growth conditions
    $|F(x)| \le C(1 + \|x\|_\infty)$ and $|\partial_i F(x)| \le C$. Then
    \[ \int x_i\, F(x)\, d\gamma(x) = \int \partial_i F(x)\, d\gamma(x). \] -/)] -/
theorem integral_mul_stdGaussianPi_eq_integral_partial (i : Fin M) {F F' : (Fin M → ℝ) → ℝ}
    (hFm : Measurable F) (hF'm : Measurable F')
    (hd : ∀ x, HasDerivAt (fun t => F (Function.update x i t)) (F' x) (x i))
    {C : ℝ} (hF : ∀ x, |F x| ≤ C * (1 + ‖x‖)) (hF' : ∀ x, |F' x| ≤ C) :
    ∫ x, x i * F x ∂(stdGaussianPi M) = ∫ x, F' x ∂(stdGaussianPi M) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hF' 0)
  -- integrability under `γ`
  have hint1 : Integrable (fun x => x i * F x) (stdGaussianPi M) := by
    have hb : Integrable (fun x : Fin M → ℝ => C * (2 + 2 * ‖x‖ ^ 2)) (stdGaussianPi M) :=
      ((integrable_const (2 : ℝ)).add (integrable_norm_sq_stdGaussianPi.const_mul 2)).const_mul C
    refine hb.mono' ((measurable_pi_apply i).mul hFm).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hxi : |x i| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i
    calc |x i| * |F x| ≤ ‖x‖ * (C * (1 + ‖x‖)) :=
          mul_le_mul hxi (hF x) (abs_nonneg _) (norm_nonneg _)
      _ ≤ C * (2 + 2 * ‖x‖ ^ 2) := by nlinarith [norm_nonneg x, mul_nonneg hC (norm_nonneg x)]
  have hint2 : Integrable F' (stdGaussianPi M) := by
    refine (integrable_const C).mono' hF'm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]; exact hF' x
  -- split off the `i`-th coordinate
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have hmp : MeasurePreserving e.symm ((gaussianReal 0 1).prod (stdGaussianPi n))
      (stdGaussianPi (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm _
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth (α := fun _ => ℝ) i p.1 p.2 :=
    fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [← hmp.integral_comp' (fun x => x i * F x), ← hmp.integral_comp' F']
  have hi1 : Integrable (fun p => (e.symm p) i * F (e.symm p))
      ((gaussianReal 0 1).prod (stdGaussianPi n)) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hint1
  have hi2 : Integrable (fun p => F' (e.symm p)) ((gaussianReal 0 1).prod (stdGaussianPi n)) :=
    (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hint2
  rw [integral_prod_symm _ hi1, integral_prod_symm _ hi2]
  congr 1
  funext y
  simp only [hsymm, Fin.insertNth_apply_same]
  refine integral_mul_gaussianReal_eq_integral_deriv_of_bounded (C := C * (1 + ‖y‖)) ?_ ?_ ?_
  · intro t
    have := hd (Fin.insertNth (α := fun _ => ℝ) i t y)
    simpa only [Fin.insertNth_apply_same, Fin.update_insertNth] using this
  · intro t
    refine (hF _).trans ?_
    have := norm_insertNth_le i t y
    nlinarith [norm_nonneg y, abs_nonneg t, mul_nonneg hC (norm_nonneg y)]
  · intro t
    refine (hF' _).trans ?_
    nlinarith [norm_nonneg y]

end IBP

section Linear

/-! ### Composition with a linear map -/

variable {M N : ℕ}

/- @[blueprint "lem:norm-mulVec-le"
  (statement := /-- There is $K \ge 0$ with $\|Ax\|_\infty \le K\|x\|_\infty$ for all $x$. -/)] -/
theorem exists_norm_mulVec_le (A : Matrix (Fin M) (Fin N) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖A.mulVec x‖ ≤ K * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap A.mulVecLin‖, norm_nonneg _,
    fun x => (LinearMap.toContinuousLinearMap A.mulVecLin).le_opNorm x⟩

/- @[blueprint "lem:fderiv-mulVec-single"
  (statement := /-- For $v = A e_i$ (the $i$-th column of $A$),
    $Df(y)[v] = \sum_k A_{ki}\, \partial_k f(y)$. -/)] -/
theorem fderiv_apply_col (f : (Fin M → ℝ) → ℝ) (y : Fin M → ℝ)
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin N) :
    fderiv ℝ f y (fun k => A k i) = ∑ k, A k i * fderiv ℝ f y (Pi.single k 1) := by
  have : (fun k => A k i) = ∑ k, A k i • (Pi.single k (1 : ℝ) : Fin M → ℝ) := by
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  simp only [map_smul, smul_eq_mul]

/- @[blueprint "cor:gaussian-ibp-linear"
  (statement := /-- \textbf{Gaussian integration by parts for a linear image.} Let
    $A \in \mathbb R^{M \times N}$, $g \sim N(0,1)^{\otimes N}$ and $X = Ag$ (a centred Gaussian
    vector with covariance $\Sigma = AA^\top$). If $f : \mathbb R^M \to \mathbb R$ is $C^1$ with
    $|f(y)| \le C(1 + \|y\|_\infty)$ and $\|Df(y)\| \le C$, then for every $j$
    \[ \mathbb E[X_j f(X)] = \sum_k \Sigma_{jk}\, \mathbb E[\partial_k f(X)],
      \qquad \Sigma_{jk} = \sum_i A_{ji} A_{ki}. \] -/)] -/
theorem integral_mulVec_mul_eq_sum_integral (A : Matrix (Fin M) (Fin N) ℝ)
    {f : (Fin M → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ}
    (hfC : ∀ y, |f y| ≤ C * (1 + ‖y‖)) (hDf : ∀ y, ‖fderiv ℝ f y‖ ≤ C) (j : Fin M) :
    ∫ x, (A.mulVec x) j * f (A.mulVec x) ∂(stdGaussianPi N)
      = ∑ k, (∑ i, A j i * A k i) *
          ∫ x, fderiv ℝ f (A.mulVec x) (Pi.single k 1) ∂(stdGaussianPi N) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hDf 0)
  set L : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ) := LinearMap.toContinuousLinearMap A.mulVecLin with hL
  have hLapply : ∀ x, L x = A.mulVec x := fun x => rfl
  obtain ⟨K, hK0, hK⟩ := exists_norm_mulVec_le A
  have hfcont : Continuous f := hf.continuous
  have hDfcont : Continuous fun p : (Fin M → ℝ) × (Fin M → ℝ) => fderiv ℝ f p.1 p.2 :=
    hf.continuous_fderiv_apply one_ne_zero
  have hmeasD : ∀ v, Measurable fun x : Fin N → ℝ => fderiv ℝ f (A.mulVec x) v := fun v =>
    (hDfcont.comp (L.continuous.prodMk continuous_const)).measurable
  have hnorm_single : ∀ k : Fin M, ‖(Pi.single k (1 : ℝ) : Fin M → ℝ)‖ ≤ 1 := fun k => by
    rw [Pi.norm_single, norm_one]
  have hboundD : ∀ (v : Fin M → ℝ) (x : Fin N → ℝ), |fderiv ℝ f (A.mulVec x) v| ≤ C * ‖v‖ :=
    fun v x => by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ f (A.mulVec x)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hDf _) (norm_nonneg _))
  -- integrability of the partial derivatives
  have hintD : ∀ k : Fin M,
      Integrable (fun x => fderiv ℝ f (A.mulVec x) (Pi.single k 1)) (stdGaussianPi N) := fun k =>
    (integrable_const C).mono' (hmeasD _).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (hboundD _ x).trans (mul_le_of_le_one_right hC (hnorm_single k)))
  -- the partial IBP identity for each coordinate `i` of `x`
  have hcoord : ∀ i : Fin N,
      ∫ x, x i * f (A.mulVec x) ∂(stdGaussianPi N)
        = ∑ k, A k i * ∫ x, fderiv ℝ f (A.mulVec x) (Pi.single k 1) ∂(stdGaussianPi N) := by
    intro i
    have key := integral_mul_stdGaussianPi_eq_integral_partial i
      (F := fun x => f (A.mulVec x)) (F' := fun x => fderiv ℝ f (A.mulVec x) (fun k => A k i))
      (hfcont.comp L.continuous).measurable (hmeasD _) ?_ (C := C * (1 + K + ‖(fun k => A k i)‖))
      ?_ ?_
    · rw [key]
      simp_rw [fderiv_apply_col]
      rw [integral_finsetSum _ fun k _ => (hintD k).const_mul _]
      simp_rw [integral_const_mul]
    · intro x
      have hu : HasDerivAt (fun t => A.mulVec (Function.update x i t)) (A.mulVec (Pi.single i 1))
          (x i) :=
        L.hasFDerivAt.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
      have hfd : HasFDerivAt f (fderiv ℝ f (A.mulVec x))
          (A.mulVec (Function.update x i (x i))) := by
        rw [Function.update_eq_self]
        exact ((hf.differentiable one_ne_zero) (A.mulVec x)).hasFDerivAt
      have := hfd.comp_hasDerivAt (x i) hu
      rw [Matrix.mulVec_single_one] at this
      exact this
    · intro x
      refine (hfC _).trans ?_
      have := hK x
      have hv : 0 ≤ ‖(fun k => A k i)‖ := norm_nonneg _
      nlinarith [norm_nonneg x, mul_nonneg hC (norm_nonneg x), mul_nonneg hC hK0,
        mul_nonneg (mul_nonneg hC hK0) (norm_nonneg x), mul_nonneg hC hv,
        mul_nonneg (mul_nonneg hC hv) (norm_nonneg x)]
    · intro x
      refine (hboundD _ x).trans ?_
      nlinarith [mul_nonneg hC hK0, norm_nonneg (fun k => A k i)]
  -- assemble
  have hmul : ∀ x, (A.mulVec x) j * f (A.mulVec x) = ∑ i, A j i * (x i * f (A.mulVec x)) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  have hint_i : ∀ i : Fin N, Integrable (fun x => x i * f (A.mulVec x)) (stdGaussianPi N) := by
    intro i
    have hb : Integrable (fun x : Fin N → ℝ => C * (1 + K) * (2 + 2 * ‖x‖ ^ 2))
        (stdGaussianPi N) :=
      ((integrable_const (2 : ℝ)).add (integrable_norm_sq_stdGaussianPi.const_mul 2)).const_mul _
    refine hb.mono' ((measurable_pi_apply i).mul
      (hfcont.comp L.continuous).measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hxi : |x i| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i
    have hAx := hK x
    calc |x i| * |f (A.mulVec x)| ≤ ‖x‖ * (C * (1 + ‖A.mulVec x‖)) :=
          mul_le_mul hxi (hfC _) (abs_nonneg _) (norm_nonneg _)
      _ ≤ ‖x‖ * (C * (1 + K * ‖x‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hC) (norm_nonneg _)
      _ ≤ C * (1 + K) * (2 + 2 * ‖x‖ ^ 2) := by
          nlinarith [norm_nonneg x, mul_nonneg hC (norm_nonneg x), mul_nonneg hC hK0,
            mul_nonneg (mul_nonneg hC hK0) (norm_nonneg x),
            mul_nonneg (mul_nonneg hC hK0) (sq_nonneg ‖x‖), mul_nonneg hC (sq_nonneg ‖x‖)]
  simp_rw [hmul]
  rw [integral_finsetSum _ fun i _ => (hint_i i).const_mul _]
  simp_rw [integral_const_mul, hcoord, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end Linear

end FoML.ToMathlib
