import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Elementary interval integrals missing from Mathlib

* layer cake for a finite sum: `∑_ω M(ω) = ∫_0^R #{ω : u < M(ω)} du` when `0 ≤ M ≤ R`
  (`sum_eq_integral_card_lt`, with the helpers `antitone_indicator_Iio`,
  `integral_indicator_Iio`);
* the Gaussian tail integral `∫_a^R e^{-u²/(2τ²)} du ≤ (τ²/a) e^{-a²/(2τ²)}`
  (`integral_exp_neg_sq_le`);
* the lower bound `c (b - a) ≤ ∫_a^b f` when `c ≤ f` on `[a, b)` (`mul_le_integral_of_forall_Ico`).

This file depends only on Mathlib (`Architect` annotations are commented out). The
declarations live in the namespace `FoML.ToMathlib` (they were extracted from
`FoML.ToFoML.DudleySubGaussian`).
-/

open MeasureTheory Real

namespace FoML.ToMathlib

section LayerCake

/- @[blueprint "lem:indicator-Iio-antitone"
  (statement := /-- $u \mapsto \mathbf 1\{u < c\}$ is antitone. -/)] -/
theorem antitone_indicator_Iio (c : ℝ) :
    Antitone fun u : ℝ => (Set.Iio c).indicator (fun _ => (1 : ℝ)) u := by
  intro u v huv
  simp only [Set.indicator_apply, Set.mem_Iio]
  by_cases hv : v < c
  · have hu : u < c := lt_of_le_of_lt huv hv
    simp [hu, hv]
  · simp only [hv, if_false]
    split_ifs <;> norm_num

/- @[blueprint "lem:integral-indicator-Iio"
  (statement := /-- For $0 \le c \le R$: $\int_0^R \mathbf 1\{u < c\}\,du = c$. -/)] -/
theorem integral_indicator_Iio {c R : ℝ} (hc0 : 0 ≤ c) (hcR : c ≤ R) :
    ∫ u in (0 : ℝ)..R, (Set.Iio c).indicator (fun _ => (1 : ℝ)) u = c := by
  rw [intervalIntegral.integral_of_le (hc0.trans hcR),
    MeasureTheory.integral_indicator measurableSet_Iio,
    MeasureTheory.Measure.restrict_restrict measurableSet_Iio, MeasureTheory.setIntegral_const]
  have hset : Set.Iio c ∩ Set.Ioc 0 R = Set.Ioo 0 c := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [hset, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal
    (by linarith), sub_zero]

/- @[blueprint "lem:layer-cake-finite"
  (statement := /-- \textbf{Layer cake for a finite sum.} If $0 \le M(\omega) \le R$ for all
    $\omega$ in a finite set $\Omega$, then
    $\sum_{\omega} M(\omega) = \int_0^R |\{\omega : u < M(\omega)\}|\,du$. -/)] -/
theorem sum_eq_integral_card_lt {Ω : Type*} [Fintype Ω] (Mx : Ω → ℝ) {R : ℝ}
    (h0 : ∀ ω, 0 ≤ Mx ω) (hR : ∀ ω, Mx ω ≤ R) :
    ∑ ω, Mx ω = ∫ u in (0 : ℝ)..R, ((Finset.univ.filter fun ω => u < Mx ω).card : ℝ) := by
  have hind : ∀ u : ℝ, ((Finset.univ.filter fun ω => u < Mx ω).card : ℝ) =
      ∑ ω, (Set.Iio (Mx ω)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [Set.indicator_apply, Set.mem_Iio]
  simp_rw [hind]
  rw [intervalIntegral.integral_finsetSum fun ω _ =>
    (antitone_indicator_Iio (Mx ω)).intervalIntegrable]
  exact Finset.sum_congr rfl fun ω _ => (integral_indicator_Iio (h0 ω) (hR ω)).symm

/- @[blueprint "lem:gaussian-tail-integral"
  (statement := /-- \textbf{Gaussian tail integral.} For $0 < a \le R$ and $\tau > 0$,
    $\int_a^R e^{-u^2/(2\tau^2)}\,du \le \frac{\tau^2}{a} e^{-a^2/(2\tau^2)}$
    (bound the integrand by $\frac ua e^{-u^2/(2\tau^2)}$, whose antiderivative is explicit). -/)] -/
theorem integral_exp_neg_sq_le {a R τ : ℝ} (ha : 0 < a) (haR : a ≤ R) (hτ : 0 < τ) :
    ∫ u in a..R, Real.exp (-(u ^ 2 / (2 * τ ^ 2))) ≤
      τ ^ 2 / a * Real.exp (-(a ^ 2 / (2 * τ ^ 2))) := by
  have hderiv : ∀ u ∈ Set.uIcc a R, HasDerivAt (fun u => -Real.exp (-(u ^ 2 / (2 * τ ^ 2))))
      (u / τ ^ 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2)))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2 / (2 * τ ^ 2)))
        (-(((2 : ℕ) : ℝ) * u ^ 1 / (2 * τ ^ 2))) u :=
      ((hasDerivAt_pow 2 u).div_const (2 * τ ^ 2)).neg
    have h2 := h1.exp.neg
    exact h2.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun u => u / τ ^ 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2))))
      volume a R := by
    apply Continuous.intervalIntegrable; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hle : ∫ u in a..R, Real.exp (-(u ^ 2 / (2 * τ ^ 2))) ≤
      ∫ u in a..R, τ ^ 2 / a * (u / τ ^ 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2)))) := by
    apply intervalIntegral.integral_mono_on haR
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · intro u hu
      have hau : a ≤ u := hu.1
      have heq : τ ^ 2 / a * (u / τ ^ 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2)))) =
          (u / a) * Real.exp (-(u ^ 2 / (2 * τ ^ 2))) := by
        field_simp
      rw [heq]
      have h1 : 1 ≤ u / a := by rw [le_div_iff₀ ha]; linarith
      have h2 := Real.exp_pos (-(u ^ 2 / (2 * τ ^ 2)))
      nlinarith
  rw [intervalIntegral.integral_const_mul, hFTC] at hle
  have h3 := Real.exp_pos (-(R ^ 2 / (2 * τ ^ 2)))
  have h4 : 0 ≤ τ ^ 2 / a := by positivity
  calc _ ≤ _ := hle
    _ ≤ τ ^ 2 / a * Real.exp (-(a ^ 2 / (2 * τ ^ 2))) := by nlinarith

end LayerCake

section IntegralHelper

/- @[blueprint "lem:mul-le-integral-of-forall-Ico"
  (statement := /-- If $f$ is integrable on $[a,b]$ and $c \le f$ on $[a, b)$ then
    $c\,(b - a) \le \int_a^b f$. -/)] -/
theorem mul_le_integral_of_forall_Ico {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h : ∀ x ∈ Set.Ico a b, c ≤ f x) :
    c * (b - a) ≤ ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Ico_eq_integral_Ioc]
  have hfi : IntegrableOn f (Set.Ico a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp hf
  calc c * (b - a) = ∫ _x in Set.Ico a b, c := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ico,
          ENNReal.toReal_ofReal (by linarith), mul_comm]
    _ ≤ ∫ x in Set.Ico a b, f x :=
        MeasureTheory.setIntegral_mono_on
          (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)) hfi
          measurableSet_Ico h

end IntegralHelper

end FoML.ToMathlib
