import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
-- `import FoML` (root module) would be cyclic here; the root imports at the time of porting:
import FoML.Generalization.LinearPredictorL2
import FoML.Generalization.LinearPredictorL1
import FoML.Generalization.RKHS
import FoML.Generalization.Dudley
import FoML.Generalization.FiniteClass
import FoML.Generalization.LipschitzParameter
import FoML.Generalization.Learning
import FoML.Generalization.RKHSLearning
import FoML.Learning.Contraction
import FoML.Rademacher.Reindex
import FoML.ToMathlib.GaussianPi
import FoML.ToMathlib.GaussianTail
import FoML.ToMathlib.GaussianMaxLower
import FoML.ToFoML.BernoulliSudakovTools

/-!
# Truncation and symmetrisation lemmas for the Bernoulli–Sudakov minoration (B1, B3, B5, B6)

This file provides the Gaussian-side ingredients of the proof of the Bernoulli–Sudakov
minoration `bernoulli_sudakov` (`FoML.ToFoML.BernoulliSudakov`) that connect the
standard Gaussian measure `γₙ = stdGaussianPi n` with the Bernoulli supremum
`bernoulliSup u` of `FoML.ToFoML.BernoulliSudakovTools`, following the blueprint
the Bernoulli–Sudakov blueprint of lean-deepgen (Talagrand ULB §6.4, steps S5–S8).

* **B1** (`lem:gaussian-sign-symmetrization`, `lem:gaussian-integral-eq-sign-average`): for every
  sign pattern `σ ∈ {±1}ⁿ` the map `x ↦ σ ⊙ x` preserves `γₙ`, hence
  `∫ F dγₙ = ∫ 2^{-n} ∑_σ F(σ ⊙ x) dγₙ` for integrable `F`.
* **B3** (`def:truncation`, `lem:truncation-exp-abs`, `lem:truncation-mgf`): the truncation
  `ξ_c(y) = y 1_{|y| > c}` (tail part) and `ξ'_c = y - ξ_c(y)` (bounded part, `|ξ'_c| ≤ c`); for
  `g ~ N(0,1)`, `B ≥ 1` and `c = 2B + 1`: `∫ e^{B |ξ_c(g)|} ≤ 2` and the MGF bound
  `∫ e^{s ξ_c(g)} ≤ exp(16 s² / B²)` for `|s| ≤ B/2`.
  (The blueprint states `exp(8 s²/B²)`; we use the elementary Taylor bound
  `e^z ≤ 1 + z + z² e^{|z|}` instead of `e^z ≤ 1 + z + z² e^{|z|}/2`, which doubles the constant.)
* **B5** (`lem:tail-part-max-bound`): the tail part of the Gaussian maximum is small:
  `∫ max_j ∑_i ξ_c(x_i) u_{j,i} dγₙ ≤ 16 a √(log M) / B` when `‖u_j‖₂ ≤ 2a`, `‖u_j‖_∞ ≤ b`,
  `√(log M) ≤ a/b`, `B ≥ 1`, `c = 2B + 1` (blueprint: `21 a √(log M)/B`; the sharper form of B4
  without the `+1` and the choice `λ = B √(log M)/(8a)` give `16`).
* **B6** (`lem:bounded-part-max-bound`): the bounded part is controlled by the Bernoulli
  supremum: `∫ max_j ∑_i ξ'_c(x_i) u_{j,i} dγₙ ≤ c · b(u)` (B1 + the deterministic contraction
  principle B2 pointwise in `x`).
* `lem:gaussian-max-split`: `max_j (A_j + B_j) ≤ max_j A_j + max_j B_j`.

This file depends only on Mathlib, FoML, the `ToMathlib` Gaussian files and
`ToFoML/BernoulliSudakovTools`.
-/

open Real MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

open FoML.ToMathlib

namespace FoML.ToFoML

variable {n : ℕ}

/-! ### B1: sign symmetrisation of the Gaussian measure -/

/- @[blueprint "def:sign-smul"
  (statement := /-- For $\sigma \in \{\pm1\}^n$ and $x \in \mathbb R^n$ the coordinatewise
    product $\sigma \odot x := (\sigma_i x_i)_i$. -/)] -/
def signSmul (σ : Signs n) (x : Fin n → ℝ) : Fin n → ℝ := fun i => ((σ i : ℤ) : ℝ) * x i

@[simp]
/- @[blueprint "lem:sign-smul-apply"
  (statement := /-- $(\sigma \odot x)_i = \sigma_i x_i$. -/)] -/
theorem signSmul_apply (σ : Signs n) (x : Fin n → ℝ) (i : Fin n) :
    signSmul σ x i = ((σ i : ℤ) : ℝ) * x i := rfl

/- @[blueprint "lem:sq-coe-sign"
  (statement := /-- $s^2 = 1$ for $s \in \{-1, 1\}$ (as real numbers). -/)] -/
theorem sq_coe_sign (s : ({-1, 1} : Finset ℤ)) : ((s : ℤ) : ℝ) ^ 2 = 1 := by
  rcases coe_sign_eq s with h | h <;> rw [h] <;> norm_num

/- @[blueprint "lem:sign-smul-measurable"
  (statement := /-- $x \mapsto \sigma \odot x$ is measurable. -/)] -/
theorem measurable_signSmul (σ : Signs n) : Measurable (signSmul σ) :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _

/- @[blueprint "lem:gaussian-real-map-sign-mul"
  (statement := /-- For $s \in \{\pm1\}$, the image of $N(0,1)$ under $y \mapsto s y$ is
    $N(0,1)$ (\texttt{gaussianReal\_map\_const\_mul} with $s^2 = 1$). -/)] -/
theorem gaussianReal_map_sign_mul (s : ({-1, 1} : Finset ℤ)) :
    (gaussianReal 0 1).map (fun y : ℝ => ((s : ℤ) : ℝ) * y) = gaussianReal 0 1 := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [sq_coe_sign]

/- @[blueprint "lem:gaussian-sign-symmetrization"
  (statement := /-- \textbf{Sign symmetrisation.} For every $\sigma \in \{\pm1\}^n$ the map
    $x \mapsto \sigma \odot x$ preserves $\gamma_n = \bigotimes_i N(0,1)$: it acts coordinatewise
    by $y \mapsto \sigma_i y$, which preserves $N(0,1)$, and the image of a product measure under
    a product map is the product of the images. -/)] -/
theorem measurePreserving_signSmul (σ : Signs n) :
    MeasurePreserving (signSmul σ) (stdGaussianPi n) (stdGaussianPi n) := by
  refine ⟨measurable_signSmul σ, ?_⟩
  unfold stdGaussianPi
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun i (y : ℝ) => ((σ i : ℤ) : ℝ) * y)
    (fun i => (measurable_const_mul _).aemeasurable)
  simp only [gaussianReal_map_sign_mul] at h
  exact h

/- @[blueprint "lem:gaussian-integral-comp-sign-smul"
  (statement := /-- $\int F(\sigma \odot x)\,d\gamma_n(x) = \int F\,d\gamma_n$ for measurable
    $F$. -/)] -/
theorem integral_signSmul (σ : Signs n) {F : (Fin n → ℝ) → ℝ}
    (hF : AEStronglyMeasurable F (stdGaussianPi n)) :
    ∫ x, F (signSmul σ x) ∂stdGaussianPi n = ∫ x, F x ∂stdGaussianPi n := by
  have h := integral_map (measurable_signSmul σ).aemeasurable (f := F)
    (by rw [(measurePreserving_signSmul σ).map_eq]; exact hF)
  rw [(measurePreserving_signSmul σ).map_eq] at h
  exact h.symm

/- @[blueprint "lem:gaussian-integrable-sign-average"
  (statement := /-- If $F$ is $\gamma_n$-integrable then so is
    $x \mapsto 2^{-n}\sum_\sigma F(\sigma \odot x)$. -/)] -/
theorem integrable_signAverage {F : (Fin n → ℝ) → ℝ} (hF : Integrable F (stdGaussianPi n)) :
    Integrable (fun x => (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, F (signSmul σ x))
      (stdGaussianPi n) :=
  (integrable_finsetSum _ fun σ _ =>
    (measurePreserving_signSmul σ).integrable_comp_of_integrable hF).const_mul _

/- @[blueprint "lem:gaussian-integral-eq-sign-average"
  (statement := /-- \textbf{Symmetrisation identity.} For $\gamma_n$-integrable $F$,
    $$\int F\,d\gamma_n = \int 2^{-n}\sum_{\sigma \in \{\pm1\}^n} F(\sigma \odot x)\,d\gamma_n(x).$$
    Proof: each term satisfies $\int F(\sigma \odot x)\,d\gamma_n = \int F\,d\gamma_n$ by
    \texttt{lem:gaussian-sign-symmetrization}, and there are $2^n$ terms. -/)] -/
theorem integral_eq_integral_signAverage {F : (Fin n → ℝ) → ℝ}
    (hF : Integrable F (stdGaussianPi n)) :
    ∫ x, F x ∂stdGaussianPi n =
      ∫ x, (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, F (signSmul σ x) ∂stdGaussianPi n := by
  have hcard : (Fintype.card (Signs n) : ℝ) ≠ 0 := by
    rw [card_signs]; positivity
  rw [integral_const_mul, integral_finsetSum (f := fun σ x => F (signSmul σ x)) _ fun σ _ =>
    (measurePreserving_signSmul σ).integrable_comp_of_integrable hF]
  simp_rw [integral_signSmul _ hF.aestronglyMeasurable]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard,
    one_mul]

/-! ### B3: truncation of a standard Gaussian -/

/- @[blueprint "def:truncation"
  (statement := /-- \textbf{Truncation.} For a level $c$ the \emph{tail part}
    $\xi_c(y) := y\,1_{\{|y| > c\}}$ and the \emph{bounded part} $\xi'_c(y) := y - \xi_c(y)
    = y\,1_{\{|y| \le c\}}$, so that $y = \xi_c(y) + \xi'_c(y)$, $|\xi'_c| \le c$,
    $|\xi_c| \le |y|$, and both are odd. -/)] -/
noncomputable def gaussTrunc (c y : ℝ) : ℝ := if c < |y| then y else 0

/- @[blueprint "def:truncation-bounded"
  (statement := /-- The bounded part $\xi'_c(y) := y - \xi_c(y)$. -/)] -/
noncomputable def gaussTruncBdd (c y : ℝ) : ℝ := y - gaussTrunc c y

/- @[blueprint "lem:truncation-add"
  (statement := /-- $\xi_c(y) + \xi'_c(y) = y$. -/)] -/
theorem gaussTrunc_add_gaussTruncBdd (c y : ℝ) : gaussTrunc c y + gaussTruncBdd c y = y := by
  simp [gaussTruncBdd]

/- @[blueprint "lem:truncation-abs-le"
  (statement := /-- $|\xi_c(y)| \le |y|$. -/)] -/
theorem abs_gaussTrunc_le (c y : ℝ) : |gaussTrunc c y| ≤ |y| := by
  unfold gaussTrunc
  split_ifs <;> simp

/- @[blueprint "lem:truncation-bounded-abs-le"
  (statement := /-- $|\xi'_c(y)| \le c$ for $c \ge 0$. -/)] -/
theorem abs_gaussTruncBdd_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : |gaussTruncBdd c y| ≤ c := by
  unfold gaussTruncBdd gaussTrunc
  split_ifs with h
  · simpa using hc
  · rw [sub_zero]; exact not_lt.mp h

/- @[blueprint "lem:truncation-odd"
  (statement := /-- $\xi_c(-y) = -\xi_c(y)$. -/)] -/
theorem gaussTrunc_neg (c y : ℝ) : gaussTrunc c (-y) = -gaussTrunc c y := by
  unfold gaussTrunc
  rw [abs_neg]
  split_ifs <;> simp

/- @[blueprint "lem:truncation-bounded-odd"
  (statement := /-- $\xi'_c(-y) = -\xi'_c(y)$. -/)] -/
theorem gaussTruncBdd_neg (c y : ℝ) : gaussTruncBdd c (-y) = -gaussTruncBdd c y := by
  unfold gaussTruncBdd
  rw [gaussTrunc_neg]
  ring

/- @[blueprint "lem:truncation-bounded-sign-mul"
  (statement := /-- $\xi'_c(s y) = s\,\xi'_c(y)$ for $s \in \{\pm1\}$. -/)] -/
theorem gaussTruncBdd_sign_mul (c : ℝ) (s : ({-1, 1} : Finset ℤ)) (y : ℝ) :
    gaussTruncBdd c (((s : ℤ) : ℝ) * y) = ((s : ℤ) : ℝ) * gaussTruncBdd c y := by
  rcases coe_sign_eq s with h | h <;> rw [h]
  · rw [neg_one_mul, neg_one_mul, gaussTruncBdd_neg]
  · rw [one_mul, one_mul]

/- @[blueprint "lem:truncation-measurable"
  (statement := /-- $\xi_c$ is Borel measurable. -/)] -/
theorem measurable_gaussTrunc (c : ℝ) : Measurable (gaussTrunc c) := by
  unfold gaussTrunc
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id.norm) measurable_id
    measurable_const

/- @[blueprint "lem:truncation-bounded-measurable"
  (statement := /-- $\xi'_c$ is Borel measurable. -/)] -/
theorem measurable_gaussTruncBdd (c : ℝ) : Measurable (gaussTruncBdd c) :=
  measurable_id.sub (measurable_gaussTrunc c)

/- @[blueprint "lem:truncation-integrable"
  (statement := /-- $\xi_c$ is $N(0,1)$-integrable ($|\xi_c(y)| \le |y|$). -/)] -/
theorem integrable_gaussTrunc (c : ℝ) : Integrable (gaussTrunc c) (gaussianReal 0 1) := by
  refine Integrable.mono' ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).norm
    (measurable_gaussTrunc c).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  simpa [Real.norm_eq_abs] using abs_gaussTrunc_le c y

/- @[blueprint "lem:truncation-mean-zero"
  (statement := /-- $\int \xi_c\,dN(0,1) = 0$, by oddness of $\xi_c$ and symmetry of $N(0,1)$. -/)] -/
theorem integral_gaussTrunc (c : ℝ) : ∫ y, gaussTrunc c y ∂gaussianReal 0 1 = 0 := by
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun y : ℝ => -y)
    measurable_neg.aemeasurable (f := gaussTrunc c)
    (by rw [hmap]; exact (measurable_gaussTrunc c).aestronglyMeasurable)
  rw [hmap] at h
  simp_rw [gaussTrunc_neg, integral_neg] at h
  linarith

/- @[blueprint "lem:gaussian-mgf-zero-one"
  (statement := /-- $\int e^{t y}\,dN(0,1)(y) = e^{t^2/2}$. -/)] -/
theorem integral_exp_mul_gaussianReal_zero_one (t : ℝ) :
    ∫ y, Real.exp (t * y) ∂gaussianReal 0 1 = Real.exp (t ^ 2 / 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  rw [mgf] at h
  rw [h]
  simp

/- @[blueprint "lem:truncation-exp-integrable"
  (statement := /-- $y \mapsto e^{t \xi_c(y)}$ is $N(0,1)$-integrable: it is bounded by
    $e^{|t||y|} \le e^{ty} + e^{-ty}$. -/)] -/
theorem integrable_exp_mul_gaussTrunc (c t : ℝ) :
    Integrable (fun y => Real.exp (t * gaussTrunc c y)) (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-t)))
    ((measurable_gaussTrunc c).const_mul t).exp.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : t * gaussTrunc c y ≤ |t| * |y| := by
    calc t * gaussTrunc c y ≤ |t * gaussTrunc c y| := le_abs_self _
      _ = |t| * |gaussTrunc c y| := abs_mul _ _
      _ ≤ |t| * |y| := mul_le_mul_of_nonneg_left (abs_gaussTrunc_le c y) (abs_nonneg t)
  have h2 : Real.exp (|t| * |y|) ≤ Real.exp (t * y) + Real.exp (-t * y) := by
    rw [← abs_mul]
    rcases abs_choice (t * y) with h | h
    · rw [h]; linarith [Real.exp_pos (-t * y)]
    · rw [h, neg_mul]; linarith [Real.exp_pos (t * y)]
  exact (Real.exp_le_exp.mpr h1).trans h2

/- @[blueprint "lem:truncation-exp-abs-integrable"
  (statement := /-- $y \mapsto e^{B |\xi_c(y)|}$ is $N(0,1)$-integrable
    ($e^{B|\xi|} \le e^{B\xi} + e^{-B\xi}$). -/)] -/
theorem integrable_exp_mul_abs_gaussTrunc (c B : ℝ) :
    Integrable (fun y => Real.exp (B * |gaussTrunc c y|)) (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_exp_mul_gaussTrunc c B).add
    (integrable_exp_mul_gaussTrunc c (-B)))
    (((measurable_gaussTrunc c).norm.const_mul B).exp.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Pi.add_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases abs_choice (gaussTrunc c y) with h | h
  · rw [h]; linarith [Real.exp_pos (-B * gaussTrunc c y)]
  · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (B * gaussTrunc c y)]

/- @[blueprint "lem:exp-le-one-add-add-sq-mul-exp-abs"
  (statement := /-- \textbf{Elementary Taylor bound.} For every real $z$,
    $e^z \le 1 + z + z^2 e^{|z|}$. Proof from $e^w \ge 1 + w$ only: for $z \ge 0$,
    $e^z - 1 \le z e^z$ (multiply $e^{-z} \ge 1 - z$ by $e^z$), hence
    $e^z - 1 - z \le z(e^z - 1) \le z^2 e^z$; for $z < 0$, $e^z - 1 - z \le (-z)(1 - e^z)
    \le (-z)^2 = z^2 \le z^2 e^{-z}$. -/)] -/
theorem exp_le_one_add_add_sq_mul_exp_abs (z : ℝ) :
    Real.exp z ≤ 1 + z + z ^ 2 * Real.exp |z| := by
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have h1 : 1 - z ≤ Real.exp (-z) := by linarith [Real.add_one_le_exp (-z)]
    have h2 : Real.exp z - z * Real.exp z ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos z).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      linarith
    have h3 : Real.exp z - 1 ≤ z * Real.exp z := by linarith
    have h4 : z * (Real.exp z - 1) ≤ z * (z * Real.exp z) := mul_le_mul_of_nonneg_left h3 hz
    nlinarith
  · rw [abs_of_neg hz]
    have h1 : 1 + z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
    have h1' : 1 - z ≤ Real.exp (-z) := by linarith [Real.add_one_le_exp (-z)]
    have h2 : Real.exp z - z * Real.exp z ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1' (Real.exp_pos z).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
      linarith
    have h3 : Real.exp z - 1 - z ≤ (-z) * (1 - Real.exp z) := by linarith
    have h4 : (-z) * (1 - Real.exp z) ≤ (-z) * (-z) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h5 : 1 ≤ Real.exp (-z) := Real.one_le_exp (by linarith)
    have h6 : z ^ 2 ≤ z ^ 2 * Real.exp (-z) := le_mul_of_one_le_right (sq_nonneg z) h5
    nlinarith

/- @[blueprint "lem:truncation-mgf-pointwise"
  (statement := /-- For $B > 0$, $|s| \le B/2$ and every $y$,
    $$e^{s \xi_c(y)} \le 1 + s\,\xi_c(y) + \frac{8 s^2}{B^2}\, e^{B |\xi_c(y)|}.$$
    Proof: $e^z \le 1 + z + z^2 e^{|z|}$ with $z = s\xi$, $|z| \le B|\xi|/2$, and
    $\xi^2 e^{B|\xi|/2} \le \frac{8}{B^2} e^{B|\xi|}$ since $w^2 \le 2 e^w$ for
    $w = B|\xi|/2 \ge 0$. -/)] -/
theorem exp_mul_gaussTrunc_le {B c s : ℝ} (hB : 0 < B) (hs : |s| ≤ B / 2) (y : ℝ) :
    Real.exp (s * gaussTrunc c y) ≤
      1 + s * gaussTrunc c y + 8 * s ^ 2 / B ^ 2 * Real.exp (B * |gaussTrunc c y|) := by
  set ξ := gaussTrunc c y with hξdef
  have h1 := exp_le_one_add_add_sq_mul_exp_abs (s * ξ)
  have hξ : 0 ≤ |ξ| := abs_nonneg _
  have h2 : |s * ξ| ≤ B / 2 * |ξ| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs hξ
  have h3 : Real.exp |s * ξ| ≤ Real.exp (B / 2 * |ξ|) := Real.exp_le_exp.mpr h2
  have h4 : (B / 2 * |ξ|) ^ 2 ≤ 2 * Real.exp (B / 2 * |ξ|) := by
    have := Real.quadratic_le_exp_of_nonneg (x := B / 2 * |ξ|) (by positivity)
    nlinarith [this, show 0 ≤ B / 2 * |ξ| by positivity]
  have h5 : ξ ^ 2 ≤ 8 / B ^ 2 * Real.exp (B / 2 * |ξ|) := by
    have hsq : (B / 2 * |ξ|) ^ 2 = B ^ 2 / 4 * ξ ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [hsq] at h4
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have h6 : Real.exp (B / 2 * |ξ|) * Real.exp (B / 2 * |ξ|) = Real.exp (B * |ξ|) := by
    rw [← Real.exp_add]; ring_nf
  have hE : 0 ≤ Real.exp (B / 2 * |ξ|) := (Real.exp_pos _).le
  calc Real.exp (s * ξ) ≤ 1 + s * ξ + (s * ξ) ^ 2 * Real.exp |s * ξ| := h1
    _ ≤ 1 + s * ξ + (s * ξ) ^ 2 * Real.exp (B / 2 * |ξ|) := by gcongr
    _ = 1 + s * ξ + s ^ 2 * (ξ ^ 2 * Real.exp (B / 2 * |ξ|)) := by ring
    _ ≤ 1 + s * ξ + s ^ 2 * (8 / B ^ 2 * Real.exp (B / 2 * |ξ|) * Real.exp (B / 2 * |ξ|)) := by
        gcongr
    _ = 1 + s * ξ + 8 * s ^ 2 / B ^ 2 * Real.exp (B * |ξ|) := by
        rw [mul_assoc (8 / B ^ 2), h6]; ring

/- @[blueprint "lem:truncation-exp-abs"
  (statement := /-- \textbf{Exponential moment of the tail part.} For $g \sim N(0,1)$, $B \ge 1$
    and $c := 2B + 1$,
    $$\int e^{B |\xi_c(g)|}\,d\gamma \le 2 .$$
    Proof: pointwise $e^{B|\xi_c(y)|} \le 1 + e^{-Bc}\bigl(e^{2By} + e^{-2By}\bigr)$ (on
    $\{|y| > c\}$ use $B|y| \le -Bc + 2B|y|$), and $\int e^{\pm 2By}\,d\gamma = e^{2B^2}$, so the
    integral is at most $1 + 2 e^{2B^2 - Bc} = 1 + 2e^{-B} \le 1 + 2/e \le 2$. -/)] -/
theorem integral_exp_mul_abs_gaussTrunc_le {B : ℝ} (hB : 1 ≤ B) :
    ∫ y, Real.exp (B * |gaussTrunc (2 * B + 1) y|) ∂gaussianReal 0 1 ≤ 2 := by
  have hB0 : 0 < B := by linarith
  set c := 2 * B + 1 with hc
  have hpt : ∀ y, Real.exp (B * |gaussTrunc c y|) ≤
      1 + Real.exp (-(B * c)) * (Real.exp (2 * B * y) + Real.exp (-(2 * B) * y)) := by
    intro y
    unfold gaussTrunc
    split_ifs with h
    · have h1 : B * |y| ≤ -(B * c) + 2 * B * |y| := by
        have := mul_lt_mul_of_pos_left h hB0
        linarith
      have h2 : Real.exp (2 * B * |y|) ≤ Real.exp (2 * B * y) + Real.exp (-(2 * B) * y) := by
        rcases abs_choice y with hy | hy
        · rw [hy]; linarith [Real.exp_pos (-(2 * B) * y)]
        · rw [hy, mul_neg, ← neg_mul]; linarith [Real.exp_pos (2 * B * y)]
      have h3 : 0 ≤ Real.exp (-(B * c)) := (Real.exp_pos _).le
      calc Real.exp (B * |y|) ≤ Real.exp (-(B * c) + 2 * B * |y|) := Real.exp_le_exp.mpr h1
        _ = Real.exp (-(B * c)) * Real.exp (2 * B * |y|) := Real.exp_add _ _
        _ ≤ Real.exp (-(B * c)) * (Real.exp (2 * B * y) + Real.exp (-(2 * B) * y)) := by
            gcongr
        _ ≤ 1 + Real.exp (-(B * c)) * (Real.exp (2 * B * y) + Real.exp (-(2 * B) * y)) := by
            linarith
    · simp only [abs_zero, mul_zero, Real.exp_zero]
      have := mul_pos (Real.exp_pos (-(B * c)))
        (add_pos (Real.exp_pos (2 * B * y)) (Real.exp_pos (-(2 * B) * y)))
      linarith
  have hint2 : Integrable (fun y => Real.exp (2 * B * y) + Real.exp (-(2 * B) * y))
      (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal _).add (integrable_exp_mul_gaussianReal _)
  have hint : Integrable
      (fun y => 1 + Real.exp (-(B * c)) * (Real.exp (2 * B * y) + Real.exp (-(2 * B) * y)))
      (gaussianReal 0 1) :=
    (integrable_const _).add (hint2.const_mul _)
  have hval : ∫ y, 1 + Real.exp (-(B * c)) * (Real.exp (2 * B * y) + Real.exp (-(2 * B) * y))
      ∂gaussianReal 0 1 = 1 + 2 * Real.exp (-B) := by
    rw [integral_add (integrable_const _) (hint2.const_mul _), integral_const,
      integral_const_mul, integral_add (integrable_exp_mul_gaussianReal _)
        (integrable_exp_mul_gaussianReal _),
      integral_exp_mul_gaussianReal_zero_one, integral_exp_mul_gaussianReal_zero_one]
    have h1 : (-(2 * B)) ^ 2 / 2 = (2 * B) ^ 2 / 2 := by ring
    have h2 : -(B * c) + (2 * B) ^ 2 / 2 = -B := by rw [hc]; ring
    rw [h1, ← two_mul, ← mul_assoc, mul_comm (Real.exp (-(B * c))) 2, mul_assoc, ← Real.exp_add,
      h2]
    simp
  have hexp : Real.exp (-B) ≤ 1 / 2 := by
    have h1 : Real.exp (-B) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h3 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) h2
    exact h1.trans h3
  calc ∫ y, Real.exp (B * |gaussTrunc c y|) ∂gaussianReal 0 1
      ≤ ∫ y, 1 + Real.exp (-(B * c)) * (Real.exp (2 * B * y) + Real.exp (-(2 * B) * y))
          ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le) hint
          (Filter.Eventually.of_forall hpt)
    _ = 1 + 2 * Real.exp (-B) := hval
    _ ≤ 2 := by linarith

/- @[blueprint "lem:truncation-mgf"
  (statement := /-- \textbf{MGF of the tail part.} For $g \sim N(0,1)$, $B \ge 1$,
    $c := 2B + 1$ and $|s| \le B/2$,
    $$\int e^{s \xi_c(g)}\,d\gamma \le \exp\Bigl(\frac{16 s^2}{B^2}\Bigr).$$
    Proof: integrate \texttt{lem:truncation-mgf-pointwise}, use $\int \xi_c = 0$ and
    \texttt{lem:truncation-exp-abs}: $\int e^{s\xi_c} \le 1 + \frac{8s^2}{B^2}\cdot 2 \le
    e^{16 s^2/B^2}$. (The blueprint's constant $8$ becomes $16$ because we use the elementary
    bound $e^z \le 1 + z + z^2 e^{|z|}$ instead of $e^z \le 1 + z + \frac{z^2}{2}e^{|z|}$.) -/)] -/
theorem integral_exp_mul_gaussTrunc_le {B s : ℝ} (hB : 1 ≤ B) (hs : |s| ≤ B / 2) :
    ∫ y, Real.exp (s * gaussTrunc (2 * B + 1) y) ∂gaussianReal 0 1 ≤
      Real.exp (16 * s ^ 2 / B ^ 2) := by
  have hB0 : 0 < B := by linarith
  set c := 2 * B + 1 with hc
  have hi1 : Integrable (fun y => 1 + s * gaussTrunc c y) (gaussianReal 0 1) :=
    (integrable_const _).add ((integrable_gaussTrunc c).const_mul s)
  have hi2 : Integrable (fun y => 8 * s ^ 2 / B ^ 2 * Real.exp (B * |gaussTrunc c y|))
      (gaussianReal 0 1) :=
    (integrable_exp_mul_abs_gaussTrunc c B).const_mul _
  have hint : Integrable
      (fun y => 1 + s * gaussTrunc c y + 8 * s ^ 2 / B ^ 2 * Real.exp (B * |gaussTrunc c y|))
      (gaussianReal 0 1) := hi1.add hi2
  have h8 : 0 ≤ 8 * s ^ 2 / B ^ 2 := by positivity
  calc ∫ y, Real.exp (s * gaussTrunc c y) ∂gaussianReal 0 1
      ≤ ∫ y, 1 + s * gaussTrunc c y + 8 * s ^ 2 / B ^ 2 * Real.exp (B * |gaussTrunc c y|)
          ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le) hint
          (Filter.Eventually.of_forall (exp_mul_gaussTrunc_le hB0 hs))
    _ = 1 + s * ∫ y, gaussTrunc c y ∂gaussianReal 0 1 +
          8 * s ^ 2 / B ^ 2 * ∫ y, Real.exp (B * |gaussTrunc c y|) ∂gaussianReal 0 1 := by
        rw [integral_add hi1 hi2,
          integral_add (integrable_const _) ((integrable_gaussTrunc c).const_mul s),
          integral_const, integral_const_mul, integral_const_mul]
        simp
    _ ≤ 1 + 16 * s ^ 2 / B ^ 2 := by
        rw [integral_gaussTrunc, mul_zero, add_zero]
        have := mul_le_mul_of_nonneg_left (integral_exp_mul_abs_gaussTrunc_le hB) h8
        rw [← hc] at this
        have h16 : 8 * s ^ 2 / B ^ 2 * 2 = 16 * s ^ 2 / B ^ 2 := by ring
        linarith
    _ ≤ Real.exp (16 * s ^ 2 / B ^ 2) := by linarith [Real.add_one_le_exp (16 * s ^ 2 / B ^ 2)]

/-! ### Transfer to the coordinates of `stdGaussianPi` -/

/- @[blueprint "lem:std-gaussian-pi-integral-comp-eval"
  (statement := /-- For measurable $f : \mathbb R \to \mathbb R$,
    $\int f(x_i)\,d\gamma_n(x) = \int f\,dN(0,1)$. -/)] -/
theorem integral_comp_eval_stdGaussianPi (i : Fin n) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f (x i) ∂stdGaussianPi n = ∫ y, f y ∂gaussianReal 0 1 := by
  rw [← stdGaussianPi_map_eval i, integral_map (measurable_pi_apply i).aemeasurable
    (by rw [stdGaussianPi_map_eval]; exact hf.aestronglyMeasurable)]

/- @[blueprint "lem:truncation-mgf-coordinate"
  (statement := /-- Coordinate version of \texttt{lem:truncation-mgf}: for $B \ge 1$,
    $c = 2B+1$, $|s| \le B/2$ and $i < n$,
    $\int e^{s \xi_c(x_i)}\,d\gamma_n(x) \le \exp(16 s^2/B^2)$. -/)] -/
theorem integral_exp_mul_gaussTrunc_eval_le {B s : ℝ} (hB : 1 ≤ B) (hs : |s| ≤ B / 2)
    (i : Fin n) :
    ∫ x, Real.exp (s * gaussTrunc (2 * B + 1) (x i)) ∂stdGaussianPi n ≤
      Real.exp (16 * s ^ 2 / B ^ 2) := by
  rw [integral_comp_eval_stdGaussianPi i ((measurable_gaussTrunc _).const_mul s).exp]
  exact integral_exp_mul_gaussTrunc_le hB hs

/- @[blueprint "lem:truncation-exp-abs-coordinate"
  (statement := /-- Coordinate version of \texttt{lem:truncation-exp-abs}:
    $\int e^{B |\xi_c(x_i)|}\,d\gamma_n(x) \le 2$ for $B \ge 1$, $c = 2B+1$. -/)] -/
theorem integral_exp_mul_abs_gaussTrunc_eval_le {B : ℝ} (hB : 1 ≤ B) (i : Fin n) :
    ∫ x, Real.exp (B * |gaussTrunc (2 * B + 1) (x i)|) ∂stdGaussianPi n ≤ 2 := by
  rw [integral_comp_eval_stdGaussianPi i
    (f := fun y => Real.exp (B * |gaussTrunc (2 * B + 1) y|))
    ((measurable_gaussTrunc _).norm.const_mul B).exp]
  exact integral_exp_mul_abs_gaussTrunc_le hB

/-! ### Splitting a finite maximum -/

/- @[blueprint "lem:gaussian-max-split"
  (statement := /-- For finite nonempty families, $\max_j (A_j + B_j) \le \max_j A_j +
    \max_j B_j$. -/)] -/
theorem iSup_add_le_iSup_add_iSup {ι : Type*} [Finite ι] [Nonempty ι] (A B : ι → ℝ) :
    (⨆ j, (A j + B j)) ≤ (⨆ j, A j) + ⨆ j, B j :=
  ciSup_le fun j => add_le_add (le_ciSup (Finite.bddAbove_range A) j)
    (le_ciSup (Finite.bddAbove_range B) j)

/-! ### B5: the tail part of the Gaussian maximum -/

/- @[blueprint "lem:tail-part-max-bound"
  (statement := /-- \textbf{Tail part} (ULB Cor.~6.4.6; blueprint S7). Let $M \ge 2$,
    $u_1,\dots,u_M \in \mathbb R^n$, $a, b > 0$, $B \ge 1$, $c := 2B+1$, and assume
    $\|u_j\|_2^2 \le 4a^2$, $\|u_j\|_\infty \le b$ for all $j$ and $\sqrt{\log M} \le a/b$. Then
    $$\int \max_{j \le M} \sum_i \xi_c(x_i)\,u_{j,i}\,d\gamma_n(x)
      \ \le\ \frac{16\,a\sqrt{\log M}}{B}.$$
    Proof: \texttt{lem:max-le-log-sum-exp-integral} with $\lambda := B\sqrt{\log M}/(8a)$, so that
    $|\lambda u_{j,i}| \le \lambda b \le B/8 \le B/2$; by independence of the coordinates
    $\int e^{\lambda \sum_i \xi_c(x_i)u_{j,i}} = \prod_i \int e^{\lambda u_{j,i}\xi_c}
    \le \exp(16\lambda^2\|u_j\|_2^2/B^2) \le \exp(64 \lambda^2 a^2/B^2) = e^{\log M} = M$
    (\texttt{lem:truncation-mgf}); hence the bound is $\lambda^{-1}\log(M \cdot M) =
    \lambda^{-1} \cdot 2\log M = 16 a\sqrt{\log M}/B$. (The blueprint's constant is $21$.) -/)] -/
theorem integral_iSup_gaussTrunc_le {M : ℕ} (hM : 2 ≤ M) (u : Fin M → Fin n → ℝ) {a b B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hB : 1 ≤ B)
    (hu2 : ∀ j, ∑ i, u j i ^ 2 ≤ 4 * a ^ 2) (hub : ∀ j i, |u j i| ≤ b)
    (hlog : √(Real.log M) ≤ a / b) :
    ∫ x, (⨆ j, ∑ i, gaussTrunc (2 * B + 1) (x i) * u j i) ∂stdGaussianPi n ≤
      16 * a * √(Real.log M) / B := by
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have hB0 : 0 < B := by linarith
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hlogpos : 0 < Real.log M := Real.log_pos hM1
  set L := √(Real.log M) with hL
  have hLpos : 0 < L := Real.sqrt_pos.mpr hlogpos
  have hLsq : L * L = Real.log M := Real.mul_self_sqrt hlogpos.le
  have hL0 : L ≠ 0 := hLpos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hB0' : B ≠ 0 := hB0.ne'
  set c := 2 * B + 1 with hc
  set l := B * L / (8 * a) with hl
  have hlpos : 0 < l := by positivity
  have hLb : L * b ≤ a := by rwa [le_div_iff₀ hb] at hlog
  -- admissible range for the MGF bound: `|l * u j i| ≤ B / 2`
  have hrange : ∀ j i, |l * u j i| ≤ B / 2 := by
    intro j i
    rw [abs_mul, abs_of_pos hlpos]
    calc l * |u j i| ≤ l * b := by gcongr; exact hub j i
      _ = B * (L * b) / (8 * a) := by rw [hl]; ring
      _ ≤ B * a / (8 * a) := by gcongr
      _ = B / 8 := mul_div_mul_right _ _ ha0
      _ ≤ B / 2 := by linarith
  -- the summands
  set Y : Fin M → (Fin n → ℝ) → ℝ := fun j x => ∑ i, gaussTrunc c (x i) * u j i with hY
  have hYmeas : ∀ j, Measurable (Y j) := fun j =>
    Finset.measurable_sum _ fun i _ =>
      ((measurable_gaussTrunc c).comp (measurable_pi_apply i)).mul_const _
  -- product form of the exponential
  have hprod : ∀ j x, Real.exp (l * Y j x) = ∏ i, Real.exp (l * u j i * gaussTrunc c (x i)) := by
    intro j x
    rw [← Real.exp_sum, hY, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- integrability of each exponential
  have hexp : ∀ j, Integrable (fun x => Real.exp (l * Y j x)) (stdGaussianPi n) := by
    intro j
    simp_rw [hprod]
    unfold stdGaussianPi
    exact Integrable.fintype_prod (f := fun i y => Real.exp (l * u j i * gaussTrunc c y))
      fun i => integrable_exp_mul_gaussTrunc c _
  -- integrability of the maximum
  have hsup : Integrable (fun x => ⨆ j, Y j x) (stdGaussianPi n) := by
    refine Integrable.mono' (g := fun x => ∑ j, ∑ i, |x i| * |u j i|) ?_ ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
        (integrable_eval_stdGaussianPi i).abs.mul_const _
    · exact (Measurable.iSup hYmeas).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_iSup_eval_le (by omega) fun j => Y j x).trans ?_
      refine Finset.sum_le_sum fun j _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_gaussTrunc_le c _) (abs_nonneg _)
  -- each MGF is at most `M`
  have hmgf : ∀ j, ∫ x, Real.exp (l * Y j x) ∂stdGaussianPi n ≤ M := by
    intro j
    simp_rw [hprod]
    unfold stdGaussianPi
    rw [integral_fintype_prod_eq_prod (f := fun i y => Real.exp (l * u j i * gaussTrunc c y))]
    calc ∏ i, ∫ y, Real.exp (l * u j i * gaussTrunc c y) ∂gaussianReal 0 1
        ≤ ∏ i, Real.exp (16 * (l * u j i) ^ 2 / B ^ 2) := by
          refine Finset.prod_le_prod (fun i _ => integral_nonneg fun y => (Real.exp_pos _).le)
            fun i _ => ?_
          exact integral_exp_mul_gaussTrunc_le hB (hrange j i)
      _ = Real.exp (16 * l ^ 2 / B ^ 2 * ∑ i, u j i ^ 2) := by
          rw [← Real.exp_sum, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ Real.exp (16 * l ^ 2 / B ^ 2 * (4 * a ^ 2)) := by
          gcongr
          exact hu2 j
      _ = Real.exp (Real.log M) := by
          congr 1
          rw [hl, ← hLsq]
          field_simp
          ring
      _ = M := Real.exp_log (by linarith)
  -- the sum of the MGFs is positive and at most `M ^ 2`
  have hsumpos : 0 < ∑ j, ∫ x, Real.exp (l * Y j x) ∂stdGaussianPi n :=
    Finset.sum_pos (fun j _ => mgf_pos (hexp j)) Finset.univ_nonempty
  have hsumle : ∑ j, ∫ x, Real.exp (l * Y j x) ∂stdGaussianPi n ≤ (M : ℝ) ^ 2 := by
    calc ∑ j, ∫ x, Real.exp (l * Y j x) ∂stdGaussianPi n
        ≤ ∑ _j : Fin M, (M : ℝ) := Finset.sum_le_sum fun j _ => hmgf j
      _ = (M : ℝ) ^ 2 := by simp [sq]
  -- B4 and the final computation
  calc ∫ x, (⨆ j, Y j x) ∂stdGaussianPi n
      ≤ l⁻¹ * Real.log (∑ j, ∫ x, Real.exp (l * Y j x) ∂stdGaussianPi n) :=
        integral_iSup_le_log_sum_exp _ Y hlpos hsup hexp
    _ ≤ l⁻¹ * Real.log ((M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hsumpos hsumle) (inv_nonneg.mpr hlpos.le)
    _ = 16 * a * L / B := by
        rw [Real.log_pow, Nat.cast_ofNat, hl, ← hLsq]
        field_simp
        ring

/-! ### B6: the bounded part of the Gaussian maximum -/

/- @[blueprint "lem:bounded-part-max-bound"
  (statement := /-- \textbf{Bounded part} (blueprint S8). For $u_1,\dots,u_M \in \mathbb R^n$ and
    $c \ge 0$,
    $$\int \max_{j} \sum_i \xi'_c(x_i)\,u_{j,i}\,d\gamma_n(x) \ \le\ c\, b(u).$$
    Proof: by \texttt{lem:gaussian-integral-eq-sign-average} the integral equals
    $\int 2^{-n}\sum_\sigma \max_j \sum_i \xi'_c(\sigma_i x_i) u_{j,i}\,d\gamma_n$; by oddness
    $\xi'_c(\sigma_i x_i) = \sigma_i \xi'_c(x_i)$, so the inner average is
    $b\bigl((\xi'_c(x_i) u_{j,i})_{j,i}\bigr) \le c\,b(u)$ pointwise in $x$ by the contraction
    principle \texttt{lem:bernoulli-contraction-pointwise} ($|\xi'_c(x_i)| \le c$); integrate the
    constant. -/)] -/
theorem integral_iSup_gaussTruncBdd_le {M : ℕ} (u : Fin M → Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, (⨆ j, ∑ i, gaussTruncBdd c (x i) * u j i) ∂stdGaussianPi n ≤ c * bernoulliSup u := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp [Real.iSup_of_isEmpty, bernoulliSup_of_isEmpty]
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set F : (Fin n → ℝ) → ℝ := fun x => ⨆ j, ∑ i, gaussTruncBdd c (x i) * u j i with hF
  have hFmeas : Measurable F :=
    Measurable.iSup fun j => Finset.measurable_sum _ fun i _ =>
      ((measurable_gaussTruncBdd c).comp (measurable_pi_apply i)).mul_const _
  have hFbound : ∀ x, |F x| ≤ ∑ j, ∑ i, c * |u j i| := by
    intro x
    refine (abs_iSup_eval_le hM fun j => ∑ i, gaussTruncBdd c (x i) * u j i).trans ?_
    refine Finset.sum_le_sum fun j _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_gaussTruncBdd_le hc _) (abs_nonneg _)
  have hFint : Integrable F (stdGaussianPi n) :=
    Integrable.mono' (integrable_const _) hFmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFbound x)
  -- pointwise in `x`: the sign average is the Bernoulli supremum of the contracted family
  have hpt : ∀ x, (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, F (signSmul σ x) ≤
      c * bernoulliSup u := by
    intro x
    have h1 : (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, F (signSmul σ x) =
        bernoulliSup (fun j i => gaussTruncBdd c (x i) * u j i) := by
      unfold bernoulliSup
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [hF, signSmul_apply]
      refine iSup_congr fun j => Finset.sum_congr rfl fun i _ => ?_
      rw [gaussTruncBdd_sign_mul]
      ring
    rw [h1]
    exact bernoulliSup_mul_le u (fun i => gaussTruncBdd c (x i)) hc
      fun i => abs_gaussTruncBdd_le hc _
  calc ∫ x, F x ∂stdGaussianPi n
      = ∫ x, (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, F (signSmul σ x)
          ∂stdGaussianPi n := integral_eq_integral_signAverage hFint
    _ ≤ ∫ _x, c * bernoulliSup u ∂stdGaussianPi n :=
        integral_mono (integrable_signAverage hFint) (integrable_const _) hpt
    _ = c * bernoulliSup u := by simp

end FoML.ToFoML
