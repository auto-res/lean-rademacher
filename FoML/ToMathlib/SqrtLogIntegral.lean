import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# The integral `∫_0^D √(log (D/ε)) dε = D Γ(3/2)` and subadditivity of `√`

Elementary real-analysis facts missing from Mathlib:

* subadditivity of the square root, `√(a + b) ≤ √a + √b` (with Mathlib's convention
  `√x = 0` for `x ≤ 0`);
* `Γ(3/2) = √π / 2`;
* for `D > 0`, `ε ↦ √(log (D/ε))` is integrable on `(0, D)` and
  `∫_0^D √(log (D/ε)) dε = D Γ(3/2) = (√π/2) D`.

The integral is computed by the change of variables `ε = D e^{-s}` (`s ∈ (0,∞)`), which turns
it into `D ∫_0^∞ e^{-s} s^{1/2} ds = D Γ(3/2)`, using the one-dimensional Jacobian formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`.

This file depends only on Mathlib (`Architect` annotations are commented out).
-/

open scoped Real
open MeasureTheory Set intervalIntegral

namespace FoML.ToMathlib

/-! ### Subadditivity of the square root -/

/- @[blueprint "lem:sqrt-add-le"
  (statement := /-- For all real $a, b$ (with the convention $\sqrt{x} = 0$ for $x \le 0$),
    $\sqrt{a + b} \le \sqrt a + \sqrt b$. -/)] -/
theorem sqrt_add_le (a b : ℝ) : √(a + b) ≤ √a + √b := by
  /- If $a, b \ge 0$, square both sides:
    $(\sqrt a + \sqrt b)^2 = a + b + 2\sqrt a\sqrt b \ge a + b$.
    If one of them is negative, its root vanishes and the claim is monotonicity of
    $\sqrt{\cdot}$. -/
  rcases le_or_gt 0 a with ha | ha
  · rcases le_or_gt 0 b with hb | hb
    · rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
        mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    · rw [Real.sqrt_eq_zero'.2 hb.le, add_zero]
      exact Real.sqrt_le_sqrt (by linarith)
  · rw [Real.sqrt_eq_zero'.2 ha.le, zero_add]
    exact Real.sqrt_le_sqrt (by linarith)

/- @[blueprint "lem:sqrt-add-add-le"
  (statement := /-- $\sqrt{a + b + c} \le \sqrt a + \sqrt b + \sqrt c$ for all real $a, b, c$. -/)] -/
theorem sqrt_add_add_le (a b c : ℝ) : √(a + b + c) ≤ √a + √b + √c := by
  /- Apply the two-term inequality twice. -/
  exact (sqrt_add_le (a + b) c).trans (add_le_add (sqrt_add_le a b) le_rfl)

/-! ### The Gamma integral -/

/- @[blueprint "lem:hasDerivAt-mul-exp-neg"
  (statement := /-- The substitution map $s \mapsto \overline D e^{-s}$ has derivative
    $-\overline D e^{-s}$. -/)] -/
theorem hasDerivAt_mul_exp_neg (D s : ℝ) :
    HasDerivAt (fun s => D * Real.exp (-s)) (-(D * Real.exp (-s))) s := by
  /- Chain rule for $\exp$ and $s \mapsto -s$. -/
  exact (((hasDerivAt_neg s).exp).const_mul D).congr_deriv (by ring)

/- @[blueprint "lem:injOn-mul-exp-neg"
  (statement := /-- $s \mapsto \overline D e^{-s}$ is injective on $(0,\infty)$
    (for $\overline D > 0$). -/)] -/
theorem injOn_mul_exp_neg {D : ℝ} (hD : 0 < D) :
    InjOn (fun s : ℝ => D * Real.exp (-s)) (Ioi 0) := by
  /- Cancel $\overline D$ and use injectivity of $\exp$. -/
  intro x _ y _ hxy
  have := Real.exp_injective (mul_left_cancel₀ hD.ne' hxy)
  linarith

/- @[blueprint "lem:image-mul-exp-neg-Ioi"
  (statement := /-- For $\overline D > 0$, the image of $(0,\infty)$ under
    $s \mapsto \overline D e^{-s}$ is the open interval $(0,\overline D)$. -/)] -/
theorem image_mul_exp_neg_Ioi {D : ℝ} (hD : 0 < D) :
    (fun s : ℝ => D * Real.exp (-s)) '' Ioi 0 = Ioo 0 D := by
  /- $e^{-s} \in (0,1)$ for $s > 0$; conversely $y \in (0,\overline D)$ is the image of
    $s = \log(\overline D / y) > 0$. -/
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨by positivity, ?_⟩
    exact mul_lt_of_lt_one_right hD (Real.exp_lt_one_iff.2 (neg_lt_zero.2 hs))
  · rintro ⟨hy0, hyD⟩
    refine ⟨Real.log (D / y), Real.log_pos ((one_lt_div hy0).2 hyD), ?_⟩
    simp only
    rw [Real.exp_neg, Real.exp_log (div_pos hD hy0)]
    field_simp

/- @[blueprint "lem:sqrt-log-div-substituted"
  (statement := /-- Pointwise form of the substitution $\varepsilon = \overline D e^{-s}$:
    $|{-\overline D e^{-s}}| \sqrt{\log(\overline D / (\overline D e^{-s}))}
      = \overline D\, e^{-s} s^{3/2 - 1}$. -/)] -/
theorem abs_deriv_smul_sqrt_log_div {D : ℝ} (hD : 0 < D) (s : ℝ) :
    |-(D * Real.exp (-s))| • √(Real.log (D / (D * Real.exp (-s)))) =
      D * (Real.exp (-s) * s ^ ((3 : ℝ) / 2 - 1)) := by
  /- $\overline D/(\overline D e^{-s}) = e^{s}$, $\log e^s = s$, and $\sqrt s = s^{1/2}$. -/
  have h1 : D / (D * Real.exp (-s)) = Real.exp s := by
    rw [Real.exp_neg]; field_simp
  have h2 : ((3 : ℝ) / 2 - 1) = 1 / 2 := by norm_num
  rw [h1, Real.log_exp, smul_eq_mul, abs_neg, abs_of_pos (by positivity), Real.sqrt_eq_rpow, h2]
  ring

/- @[blueprint "lem:sqrt-log-integrable-Ioo"
  (statement := /-- For $\overline D > 0$,
    $\varepsilon \mapsto \sqrt{\log(\overline D/\varepsilon)}$ is integrable on
    $(0, \overline D)$. -/)] -/
theorem integrableOn_sqrt_log_div_Ioo {D : ℝ} (hD : 0 < D) :
    IntegrableOn (fun ε => √(Real.log (D / ε))) (Ioo 0 D) := by
  /- Transport through the substitution $\varepsilon = \overline D e^{-s}$; the transformed
    integrand is $\overline D e^{-s} s^{1/2}$, the (convergent) $\Gamma(3/2)$ integrand. -/
  rw [← image_mul_exp_neg_Ioi hD,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun s _ => (hasDerivAt_mul_exp_neg D s).hasDerivWithinAt) (injOn_mul_exp_neg hD)]
  refine IntegrableOn.congr_fun
    ((Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 2)).const_mul D)
    ?_ measurableSet_Ioi
  intro s _
  exact (abs_deriv_smul_sqrt_log_div hD s).symm

/- @[blueprint "lem:sqrt-log-integrable"
  (statement := /-- For $\overline D > 0$,
    $\varepsilon \mapsto \sqrt{\log(\overline D/\varepsilon)}$ is interval-integrable on
    $[0, \overline D]$. -/)] -/
theorem intervalIntegrable_sqrt_log_div {D : ℝ} (hD : 0 < D) :
    IntervalIntegrable (fun ε => √(Real.log (D / ε))) volume 0 D := by
  /- Endpoints are null sets, so this is integrability on $(0,\overline D)$. -/
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hD.le]
  exact integrableOn_sqrt_log_div_Ioo hD

/- @[blueprint "lem:gamma-three-halves"
  (statement := /-- $\Gamma(3/2) = \tfrac12 \Gamma(1/2) = \sqrt\pi/2$. -/)] -/
theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  /- Functional equation $\Gamma(s+1) = s\Gamma(s)$ at $s = 1/2$ and $\Gamma(1/2) = \sqrt\pi$. -/
  have h := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
  rw [Real.Gamma_one_half_eq] at h
  have h' : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [h'] at h
  rw [h]; ring

/- @[blueprint "lem:log-split-integral-Ioo"
  (statement := /-- For $\overline D > 0$,
    $\int_{(0,\overline D)} \sqrt{\log(\overline D/\varepsilon)}\,d\varepsilon
      = \overline D\,\Gamma(3/2)$. -/)] -/
theorem integral_Ioo_sqrt_log_div {D : ℝ} (hD : 0 < D) :
    ∫ ε in Ioo 0 D, √(Real.log (D / ε)) = D * Real.Gamma (3 / 2) := by
  /- Substitute $\varepsilon = \overline D e^{-s}$ (Jacobian $\overline D e^{-s}$) to get
    $\overline D \int_0^\infty e^{-s} s^{1/2}\,ds = \overline D\,\Gamma(3/2)$. -/
  rw [← image_mul_exp_neg_Ioi hD,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun s _ => (hasDerivAt_mul_exp_neg D s).hasDerivWithinAt) (injOn_mul_exp_neg hD),
    Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 3 / 2), ← MeasureTheory.integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => abs_deriv_smul_sqrt_log_div hD s

/- @[blueprint "lem:log-split-integral"
  (statement := /-- For $\overline D > 0$,
    $\int_0^{\overline D} \sqrt{\log(\overline D/\varepsilon)}\,d\varepsilon
      = \overline D\,\Gamma(3/2) = \tfrac{\sqrt\pi}{2}\,\overline D$. -/)] -/
theorem integral_sqrt_log_div {D : ℝ} (hD : 0 < D) :
    ∫ ε in (0 : ℝ)..D, √(Real.log (D / ε)) = √π / 2 * D := by
  /- The interval integral over $[0,\overline D]$ equals the integral over $(0,\overline D)$;
    conclude with the substitution formula and $\Gamma(3/2) = \sqrt\pi/2$. -/
  rw [integral_of_le hD.le, integral_Ioc_eq_integral_Ioo, integral_Ioo_sqrt_log_div hD,
    Gamma_three_halves]
  ring

end FoML.ToMathlib
