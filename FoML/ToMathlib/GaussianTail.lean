import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Tail bounds and elementary moments of the standard Gaussian

For `g ~ N(0,1)` and `t ≥ 0` we prove

* the Chernoff upper tail `P(g > t) ≤ exp (-t ^ 2 / 2)`;
* the Mills-ratio lower tail `P(g > t) ≥ (t / (1 + t ^ 2)) · exp (-t ^ 2 / 2) / √(2π)` for
  `t > 0`, and the simplified form `P(g > t) ≥ exp (-t ^ 2 / 2) / (2 t √(2π))` for `t ≥ 1`;
* the first absolute moment `∫ |x| dN(0,v) = 2v / √(2πv)` and the negative part
  `∫ min x 0 dN(0,1) = -1 / √(2π)`.

The lower tail comes from the identity
`∫_t^∞ e^{-x²/2} (1 + x⁻²) dx = e^{-t²/2} / t` (the integrand is the derivative of
`-x⁻¹ e^{-x²/2}`) and the bound `1 + x⁻² ≤ 1 + t⁻²` for `x ≥ t`.

This file depends only on Mathlib (`Architect` annotations are commented out).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace FoML.ToMathlib

/-! ### The density and set probabilities -/

/- @[blueprint "lem:gaussian-pdf-zero-one"
  (statement := /-- The standard Gaussian density is
    $\varphi(x) = (2\pi)^{-1/2} e^{-x^2/2}$. -/)] -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

/- @[blueprint "lem:gaussian-real-set-integral"
  (statement := /-- For $v \ne 0$ and any set $s$,
    $N(0,v)(s) = \int_s \varphi_{\mu,v}(x)\,dx$ (as a real number). -/)] -/
theorem gaussianReal_real_eq_setIntegral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    (gaussianReal μ v).real s = ∫ x in s, gaussianPDFReal μ v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral μ hv s,
    ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg μ v x)]

/-! ### Upper tail -/

/- @[blueprint "lem:gaussian-tail-upper"
  (statement := /-- For $g \sim N(0,1)$ and $t \ge 0$, $\mathbb P(g > t) \le e^{-t^2/2}$. -/)] -/
theorem gaussianReal_real_Ioi_le (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Ioi t) ≤ exp (-t ^ 2 / 2) := by
  /- Chernoff: $\mathbb P(g \ge t) \le e^{-\lambda t}\, \mathbb E e^{\lambda g}
    = e^{-\lambda t + \lambda^2/2}$; take $\lambda = t$. -/
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun x => x) t ht
    (integrable_exp_mul_gaussianReal t)
  rw [mgf_fun_id_gaussianReal] at h
  calc (gaussianReal 0 1).real (Ioi t)
      ≤ (gaussianReal 0 1).real {x | t ≤ x} :=
        measureReal_mono fun x hx => (le_of_lt (mem_Ioi.mp hx) : t ≤ x)
    _ ≤ exp (-t * t) * exp (0 * t + ((1 : ℝ≥0) : ℝ) * t ^ 2 / 2) := h
    _ = exp (-t ^ 2 / 2) := by rw [← exp_add]; congr 1; simp; ring

/-! ### Lower tail (Mills ratio) -/

/- @[blueprint "lem:gaussian-tail-mills-deriv"
  (statement := /-- For $x > 0$, $\frac{d}{dx}\bigl[-x^{-1} e^{-x^2/2}\bigr]
    = e^{-x^2/2}\,(1 + x^{-2})$. -/)] -/
theorem hasDerivAt_neg_inv_mul_exp_neg_sq_half {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(x⁻¹ * exp (-x ^ 2 / 2)))
      (exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  have h2 : HasDerivAt (fun x : ℝ => exp (-x ^ 2 / 2))
      (exp (-x ^ 2 / 2) * (-(↑(2 : ℕ) * x ^ (2 - 1)) / 2)) x :=
    ((hasDerivAt_pow 2 x).neg.div_const 2).exp
  refine (h1.mul h2).neg.congr_deriv ?_
  norm_num
  field_simp

/- @[blueprint "lem:gaussian-tail-mills-limit"
  (statement := /-- $-x^{-1} e^{-x^2/2} \to 0$ as $x \to \infty$. -/)] -/
theorem tendsto_neg_inv_mul_exp_neg_sq_half :
    Tendsto (fun x : ℝ => -(x⁻¹ * exp (-x ^ 2 / 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h2 : Tendsto (fun x : ℝ => exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_atTop_nhds_zero.comp h1
    refine this.congr fun x => ?_
    simp [neg_div]
  have := (tendsto_inv_atTop_zero.mul h2).neg
  simpa using this

/- @[blueprint "lem:gaussian-tail-mills-identity"
  (statement := /-- For $t > 0$,
    $\int_t^\infty e^{-x^2/2}\,(1 + x^{-2})\,dx = e^{-t^2/2}/t$, since the integrand is the
    derivative of $-x^{-1} e^{-x^2/2}$, which tends to $0$ at $\infty$. -/)] -/
theorem integral_Ioi_exp_neg_sq_half_mul_one_add_inv_sq {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi t, exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹) = exp (-t ^ 2 / 2) / t := by
  have hderiv := fun x (hx : x ∈ Ici t) => hasDerivAt_neg_inv_mul_exp_neg_sq_half (ht.trans_le hx)
  have hpos : ∀ x ∈ Ioi t, 0 ≤ exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹) := fun x _ =>
    mul_nonneg (exp_pos _).le (by positivity)
  have hlim := tendsto_neg_inv_mul_exp_neg_sq_half
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  field_simp
  ring

/- @[blueprint "lem:gaussian-tail-mills-integral"
  (statement := /-- For $t > 0$,
    $\int_t^\infty e^{-x^2/2}\,dx \ge \frac{t}{1+t^2} e^{-t^2/2}$. -/)] -/
theorem integral_Ioi_exp_neg_sq_half_ge {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) * exp (-t ^ 2 / 2) ≤ ∫ x in Ioi t, exp (-x ^ 2 / 2) := by
  /- $e^{-t^2/2}/t = \int_t^\infty e^{-x^2/2}(1 + x^{-2})\,dx
    \le (1 + t^{-2}) \int_t^\infty e^{-x^2/2}\,dx$. -/
  have hint : Integrable (fun x : ℝ => exp (-x ^ 2 / 2)) := by
    have : (fun x : ℝ => exp (-x ^ 2 / 2)) = fun x => exp (-(1 / 2) * x ^ 2) := by
      ext x; ring_nf
    rw [this]; exact integrable_exp_neg_mul_sq one_half_pos
  have hderiv := fun x (hx : x ∈ Ici t) => hasDerivAt_neg_inv_mul_exp_neg_sq_half (ht.trans_le hx)
  have hpos : ∀ x ∈ Ioi t, 0 ≤ exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹) := fun x _ =>
    mul_nonneg (exp_pos _).le (by positivity)
  have hlim := tendsto_neg_inv_mul_exp_neg_sq_half
  have hint' : IntegrableOn (fun x : ℝ => exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)) (Ioi t) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hmono : ∫ x in Ioi t, exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹) ≤
      ∫ x in Ioi t, exp (-x ^ 2 / 2) * (1 + (t ^ 2)⁻¹) := by
    refine setIntegral_mono_on hint' (hint.integrableOn.mul_const _) measurableSet_Ioi
      fun x hx => ?_
    have hx : t < x := hx
    gcongr
  rw [integral_Ioi_exp_neg_sq_half_mul_one_add_inv_sq ht, integral_mul_const] at hmono
  have ht2 : 0 < 1 + (t ^ 2)⁻¹ := by positivity
  rw [div_le_iff₀ ht] at hmono
  have : t / (1 + t ^ 2) * exp (-t ^ 2 / 2) =
      exp (-t ^ 2 / 2) / t / (1 + (t ^ 2)⁻¹) := by
    field_simp
    ring
  rw [this, div_le_iff₀ ht2, div_le_iff₀ ht]
  linarith

/- @[blueprint "lem:gaussian-tail-lower"
  (statement := /-- Mills-ratio lower bound: for $g \sim N(0,1)$ and $t > 0$,
    $\mathbb P(g > t) \ge \frac{t}{1+t^2}\,\frac{e^{-t^2/2}}{\sqrt{2\pi}}$. -/)] -/
theorem gaussianReal_real_Ioi_ge {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) * exp (-t ^ 2 / 2) / √(2 * π) ≤ (gaussianReal 0 1).real (Ioi t) := by
  /- $\mathbb P(g > t) = (2\pi)^{-1/2} \int_t^\infty e^{-x^2/2}\,dx$ and the previous lemma. -/
  rw [gaussianReal_real_eq_setIntegral 0 one_ne_zero]
  simp_rw [gaussianPDFReal_zero_one]
  rw [integral_const_mul, div_eq_inv_mul, mul_comm (√(2 * π))⁻¹]
  rw [mul_comm]
  gcongr
  exact integral_Ioi_exp_neg_sq_half_ge ht

/- @[blueprint "lem:gaussian-tail-lower-simple"
  (statement := /-- For $g \sim N(0,1)$ and $t \ge 1$,
    $\mathbb P(g > t) \ge \frac{1}{2t}\,\frac{e^{-t^2/2}}{\sqrt{2\pi}}$. -/)] -/
theorem gaussianReal_real_Ioi_ge_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    1 / (2 * t) * exp (-t ^ 2 / 2) / √(2 * π) ≤ (gaussianReal 0 1).real (Ioi t) := by
  /- $\frac{1}{2t} \le \frac{t}{1+t^2}$ for $t \ge 1$. -/
  refine le_trans ?_ (gaussianReal_real_Ioi_ge (zero_lt_one.trans_le ht))
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  gcongr ?_ * _ / _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### First absolute moment and negative part -/

/- @[blueprint "lem:gaussian-half-first-moment-integral"
  (statement := /-- For $v > 0$, $\int_0^\infty x\, e^{-x^2/(2v)}\,dx = v$. -/)] -/
theorem integral_Ioi_mul_exp_neg_sq_div {v : ℝ} (hv : 0 < v) :
    ∫ x in Ioi 0, x * exp (-x ^ 2 / (2 * v)) = v := by
  /- The integrand is the derivative of $-v e^{-x^2/(2v)}$, which tends to $0$. -/
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun x : ℝ => -(v * exp (-x ^ 2 / (2 * v)))) (x * exp (-x ^ 2 / (2 * v))) x := by
    intro x _
    have h2 : HasDerivAt (fun x : ℝ => exp (-x ^ 2 / (2 * v)))
        (exp (-x ^ 2 / (2 * v)) * (-(↑(2 : ℕ) * x ^ (2 - 1)) / (2 * v))) x :=
      ((hasDerivAt_pow 2 x).neg.div_const (2 * v)).exp
    refine (h2.const_mul v).neg.congr_deriv ?_
    norm_num
    field_simp
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x * exp (-x ^ 2 / (2 * v)) := fun x hx =>
    mul_nonneg (le_of_lt hx) (exp_pos _).le
  have hlim : Tendsto (fun x : ℝ => -(v * exp (-x ^ 2 / (2 * v)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ 2 / (2 * v)) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by positivity)
    have h2 : Tendsto (fun x : ℝ => exp (-x ^ 2 / (2 * v))) atTop (𝓝 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp h1
      refine this.congr fun x => ?_
      simp [neg_div]
    have := (h2.const_mul v).neg
    simpa using this
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  simp

/- @[blueprint "lem:gaussian-abs-moment"
  (statement := /-- For $v > 0$ and $X \sim N(0,v)$,
    $\mathbb E|X| = \dfrac{2v}{\sqrt{2\pi v}}$ $\bigl(= \sqrt{2v/\pi}\bigr)$. -/)] -/
theorem integral_abs_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, |x| ∂gaussianReal 0 v = 2 * v / √(2 * π * v) := by
  /- Write the density, split $\mathbb R = (-\infty, 0] \cup (0, \infty)$, use evenness of
    $|x| e^{-x^2/(2v)}$ and the previous lemma. -/
  have hv' : (0 : ℝ) < v := by positivity
  set f : ℝ → ℝ := fun x => |x| * exp (-x ^ 2 / (2 * v)) with hf
  have hfint : Integrable f := by
    have h := (integrable_mul_exp_neg_mul_sq (b := 1 / (2 * v)) (by positivity)).abs
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [hf, abs_mul, abs_of_pos (exp_pos _)]
    ring_nf
  have heven : ∀ x, f (-x) = f x := fun x => by simp [hf]
  have hsplit : ∫ x, f x = 2 * ∫ x in Ioi 0, f x := by
    rw [← integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hfint, compl_Ioi]
    have : ∫ x in Iic (0 : ℝ), f x = ∫ x in Ioi (0 : ℝ), f x := by
      have h0 := integral_comp_neg_Iic (0 : ℝ) f
      rw [neg_zero] at h0
      rw [← h0]
      exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
    rw [this]; ring
  have hIoi : ∫ x in Ioi 0, f x = v := by
    rw [← integral_Ioi_mul_exp_neg_sq_div hv']
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [hf, abs_of_pos (show (0 : ℝ) < x from hx)]
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [gaussianPDFReal, sub_zero, smul_eq_mul]
  have : (fun x : ℝ => (√(2 * π * v))⁻¹ * exp (-x ^ 2 / (2 * v)) * |x|) =
      fun x => (√(2 * π * v))⁻¹ * f x := by
    ext x; simp only [hf]; ring
  rw [this, integral_const_mul, hsplit, hIoi]
  field_simp

/- @[blueprint "lem:min-zero-eq-sub-abs"
  (statement := /-- $\min(x, 0) = (x - |x|)/2$. -/)] -/
theorem min_zero_eq_sub_abs_div_two (x : ℝ) : min x 0 = (x - |x|) / 2 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [min_eq_right hx, abs_of_nonneg hx]; ring
  · rw [min_eq_left hx.le, abs_of_neg hx]; ring

/- @[blueprint "lem:gaussian-neg-part-integrable"
  (statement := /-- $x \mapsto \min(x, 0)$ is integrable for $N(\mu, v)$. -/)] -/
theorem integrable_min_zero_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => min x 0) (gaussianReal μ v) := by
  have hint : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  simp_rw [min_zero_eq_sub_abs_div_two]
  exact (hint.sub hint.abs).div_const 2

/- @[blueprint "lem:gaussian-neg-part"
  (statement := /-- For $g \sim N(0,1)$, $\mathbb E \min(g, 0) = -\dfrac{1}{\sqrt{2\pi}}$. -/)] -/
theorem integral_min_zero_gaussianReal :
    ∫ x, min x 0 ∂gaussianReal 0 1 = -1 / √(2 * π) := by
  /- $\min(x, 0) = (x - |x|)/2$, $\mathbb E g = 0$ and $\mathbb E|g| = 2/\sqrt{2\pi}$. -/
  have hint : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  simp_rw [min_zero_eq_sub_abs_div_two]
  rw [integral_div, integral_sub hint hint.abs, integral_id_gaussianReal,
    integral_abs_gaussianReal one_ne_zero]
  simp only [NNReal.coe_one, mul_one]
  ring

end FoML.ToMathlib
