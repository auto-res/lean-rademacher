import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
import FoML.ToMathlib.GaussianPi
import FoML.ToMathlib.GaussianTail

/-!
# Lower bound on the expected maximum of i.i.d. standard Gaussians

For `M ≥ 2` i.i.d. standard Gaussians `g_1, …, g_M` (the coordinates of `stdGaussianPi M`) we
prove the universal lower bound

  `E max_j g_j ≥ (1/6) √(log M)`.

The argument: for every `t`, `max_j g_j ≥ t · 1{max > t} + min(g_1, 0)` pointwise, so
`E max ≥ t · P(max > t) − 1/√(2π)`. By independence
`P(max ≤ t) = P(g ≤ t)^M ≤ (1 − p)^M ≤ e^{−Mp} ≤ 1/(1 + Mp)` with `p = P(g > t)`, and the
Mills-ratio lower bound (`gaussianReal_real_Ioi_ge_of_one_le`) with `t = √(log M)` gives
`Mp ≥ √M / (2 t √(2π)) ≥ 1` once `M ≥ 4096`; hence `E max ≥ t/2 − 1/√(2π) ≥ t/6`.
For `2 ≤ M ≤ 4096` we use instead `max_j g_j ≥ max(g_1, g_2)` and the exact value
`E max(g_1, g_2) = E|g_1 − g_2| / 2 = 1/√π`, which dominates `(1/6) √(log M)` in that range.

This file depends only on Mathlib (`Architect` annotations are commented out) through
`FoML.ToMathlib.GaussianPi` and `FoML.ToMathlib.GaussianTail`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

namespace FoML.ToMathlib

variable {M : ℕ}

/-! ### The maximum of the coordinates -/

/- @[blueprint "lem:gaussian-max-measurable"
  (statement := /-- $g \mapsto \max_j g_j$ is measurable on $\mathbb R^M$. -/)] -/
theorem measurable_iSup_eval : Measurable (fun g : Fin M → ℝ => ⨆ j, g j) :=
  Measurable.iSup fun j => measurable_pi_apply j

/- @[blueprint "lem:gaussian-max-le"
  (statement := /-- $g_j \le \max_k g_k$ for every $j$. -/)] -/
theorem le_iSup_eval (g : Fin M → ℝ) (j : Fin M) : g j ≤ ⨆ k, g k :=
  le_ciSup (Finite.bddAbove_range g) j

/- @[blueprint "lem:gaussian-max-abs-le-sum"
  (statement := /-- For $M \ge 1$, $|\max_j g_j| \le \sum_j |g_j|$. -/)] -/
theorem abs_iSup_eval_le (hM : 0 < M) (g : Fin M → ℝ) : |⨆ j, g j| ≤ ∑ j, |g j| := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hsum : ∀ j, |g j| ≤ ∑ k, |g k| := fun j =>
    Finset.single_le_sum (fun k _ => abs_nonneg (g k)) (Finset.mem_univ j)
  rw [abs_le]
  constructor
  · have h1 := le_iSup_eval g ⟨0, hM⟩
    have h2 := hsum ⟨0, hM⟩
    have h3 := neg_abs_le (g ⟨0, hM⟩)
    linarith
  · exact ciSup_le fun j => (le_abs_self _).trans (hsum j)

/- @[blueprint "lem:gaussian-max-integrable"
  (statement := /-- For $M \ge 1$, $\max_j g_j$ is $\gamma_M$-integrable. -/)] -/
theorem integrable_iSup_eval (hM : 0 < M) :
    Integrable (fun g : Fin M → ℝ => ⨆ j, g j) (stdGaussianPi M) := by
  /- Dominated by the integrable function $\sum_j |g_j|$. -/
  refine Integrable.mono' (g := fun g : Fin M → ℝ => ∑ j, |g j|) ?_
    measurable_iSup_eval.aestronglyMeasurable (Eventually.of_forall fun g => ?_)
  · exact integrable_finsetSum _ fun j _ => (integrable_eval_stdGaussianPi j).abs
  · rw [Real.norm_eq_abs]; exact abs_iSup_eval_le hM g

/-! ### The distribution of the maximum -/

/- @[blueprint "lem:gaussian-max-cdf"
  (statement := /-- For $M \ge 1$ and $t \in \mathbb R$,
    $\gamma_M(\max_j g_j \le t) = N(0,1)((-\infty, t])^M$ (independence of the coordinates). -/)] -/
theorem stdGaussianPi_real_iSup_le (hM : 0 < M) (t : ℝ) :
    (stdGaussianPi M).real {g | ⨆ j, g j ≤ t} = ((gaussianReal 0 1).real (Iic t)) ^ M := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hset : {g : Fin M → ℝ | ⨆ j, g j ≤ t} = Set.pi univ (fun _ => Iic t) := by
    ext g
    simp only [mem_setOf_eq, Set.mem_pi, mem_univ, true_implies, mem_Iic]
    exact ⟨fun h j => (le_iSup_eval g j).trans h, fun h => ciSup_le h⟩
  rw [hset, measureReal_def, stdGaussianPi, Measure.pi_pi, ENNReal.toReal_prod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

/- @[blueprint "lem:gaussian-max-tail"
  (statement := /-- For $M \ge 1$ and $t \in \mathbb R$, with $p = \mathbb P(g > t)$,
    $\gamma_M(\max_j g_j > t) = 1 - (1 - p)^M$. -/)] -/
theorem stdGaussianPi_real_lt_iSup (hM : 0 < M) (t : ℝ) :
    (stdGaussianPi M).real {g | t < ⨆ j, g j} =
      1 - (1 - (gaussianReal 0 1).real (Ioi t)) ^ M := by
  have hc : {g : Fin M → ℝ | t < ⨆ j, g j} = {g | ⨆ j, g j ≤ t}ᶜ := by
    ext g; simp
  rw [hc, measureReal_compl (measurableSet_le measurable_iSup_eval measurable_const),
    probReal_univ, stdGaussianPi_real_iSup_le hM]
  congr 2
  rw [← compl_Ioi, measureReal_compl measurableSet_Ioi, probReal_univ]

/- @[blueprint "lem:one-sub-pow-le-inv-one-add"
  (statement := /-- For $0 \le p \le 1$ and $M \in \mathbb N$,
    $(1 - p)^M \le e^{-Mp} \le \dfrac{1}{1 + Mp}$. -/)] -/
theorem one_sub_pow_le_inv_one_add_mul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (M : ℕ) :
    (1 - p) ^ M ≤ 1 / (1 + M * p) := by
  calc (1 - p) ^ M ≤ (exp (-p)) ^ M :=
        pow_le_pow_left₀ (sub_nonneg.2 hp1) (one_sub_le_exp_neg p) M
    _ = exp (-(M * p)) := by rw [← exp_nat_mul]; ring_nf
    _ ≤ 1 / (1 + M * p) := by
        rw [exp_neg, one_div]
        exact inv_anti₀ (by positivity) (by linarith [add_one_le_exp (M * p)])

/- @[blueprint "lem:gaussian-max-tail-ge-half"
  (statement := /-- If $M\, \mathbb P(g > t) \ge 1$ then $\gamma_M(\max_j g_j > t) \ge 1/2$. -/)] -/
theorem stdGaussianPi_real_lt_iSup_ge_half (hM : 0 < M) {t : ℝ}
    (h : 1 ≤ M * (gaussianReal 0 1).real (Ioi t)) :
    1 / 2 ≤ (stdGaussianPi M).real {g | t < ⨆ j, g j} := by
  rw [stdGaussianPi_real_lt_iSup hM]
  set p := (gaussianReal 0 1).real (Ioi t) with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have h1 := one_sub_pow_le_inv_one_add_mul hp0 hp1 M
  have h2 : 1 / (1 + M * p) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-! ### Expectation lower bounds -/

/- @[blueprint "lem:gaussian-max-expect-ge-tail"
  (statement := /-- For $M \ge 1$ and $t \in \mathbb R$,
    $\mathbb E \max_j g_j \ge t\, \gamma_M(\max_j g_j > t) - \dfrac{1}{\sqrt{2\pi}}$. -/)] -/
theorem integral_iSup_eval_ge_tail (hM : 0 < M) (t : ℝ) :
    t * (stdGaussianPi M).real {g | t < ⨆ j, g j} - 1 / √(2 * π) ≤
      ∫ g, ⨆ j, g j ∂stdGaussianPi M := by
  /- Pointwise $\max_j g_j \ge t\,\mathbf 1\{\max > t\} + \min(g_1, 0)$, integrate, and use
    $\mathbb E \min(g_1, 0) = -1/\sqrt{2\pi}$. -/
  set A := {g : Fin M → ℝ | t < ⨆ j, g j} with hA_def
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_iSup_eval
  set i : Fin M := ⟨0, hM⟩
  have hpt : ∀ g : Fin M → ℝ, t * A.indicator 1 g + min (g i) 0 ≤ ⨆ j, g j := by
    intro g
    by_cases hg : g ∈ A
    · rw [indicator_of_mem hg, Pi.one_apply, mul_one]
      have : t < ⨆ j, g j := hg
      linarith [min_le_right (g i) 0]
    · rw [indicator_of_notMem hg, mul_zero, zero_add]
      exact (min_le_left _ _).trans (le_iSup_eval g i)
  have h1 : Integrable (fun g : Fin M → ℝ => t * A.indicator 1 g) (stdGaussianPi M) :=
    ((integrable_const (1 : ℝ)).indicator hA).const_mul t
  have h2 : Integrable (fun g : Fin M → ℝ => min (g i) 0) (stdGaussianPi M) :=
    ((memLp_one_iff_integrable.2 (integrable_min_zero_gaussianReal 0 1)).comp_measurePreserving
      (measurePreserving_eval_stdGaussianPi i)).integrable le_rfl
  have hmin : ∫ g, min (g i) 0 ∂stdGaussianPi M = -1 / √(2 * π) := by
    have := (hasLaw_eval_stdGaussianPi (n := M) i).integral_comp (f := fun x => min x 0)
      (measurable_id.min measurable_const).aestronglyMeasurable
    rw [← integral_min_zero_gaussianReal]
    exact this
  calc t * (stdGaussianPi M).real A - 1 / √(2 * π)
      = ∫ g, (t * A.indicator 1 g + min (g i) 0) ∂stdGaussianPi M := by
        rw [integral_add h1 h2, integral_const_mul, integral_indicator_one hA, hmin]
        ring
    _ ≤ ∫ g, ⨆ j, g j ∂stdGaussianPi M :=
        integral_mono (h1.add h2) (integrable_iSup_eval hM) hpt

/- @[blueprint "lem:max-eq-half-add-add-abs-sub"
  (statement := /-- $\max(a, b) = \bigl(a + b + |a - b|\bigr)/2$. -/)] -/
theorem max_eq_add_add_abs_sub_div_two (a b : ℝ) : max a b = (a + b + |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.2 h)]; ring

/- @[blueprint "lem:gaussian-max-expect-ge-two"
  (statement := /-- For $M \ge 2$, $\mathbb E \max_j g_j \ge \mathbb E \max(g_1, g_2)
    = \tfrac12 \mathbb E|g_1 - g_2| = 1/\sqrt{\pi}$. -/)] -/
theorem integral_iSup_eval_ge_two (hM : 2 ≤ M) :
    1 / √π ≤ ∫ g, ⨆ j, g j ∂stdGaussianPi M := by
  /- $g_1 - g_2 \sim N(0, 2)$, so $\mathbb E|g_1 - g_2| = 4/\sqrt{4\pi} = 2/\sqrt\pi$. -/
  set i : Fin M := ⟨0, by omega⟩
  set j : Fin M := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hpt : ∀ g : Fin M → ℝ, (g i + g j + |g i - g j|) / 2 ≤ ⨆ k, g k := fun g => by
    rw [← max_eq_add_add_abs_sub_div_two]
    exact max_le (le_iSup_eval g i) (le_iSup_eval g j)
  have hi := integrable_eval_stdGaussianPi (n := M) i
  have hj := integrable_eval_stdGaussianPi (n := M) j
  have hsqrt : √(2 * π * ((2 : ℝ≥0) : ℝ)) = 2 * √π := by
    rw [show (2 : ℝ) * π * ((2 : ℝ≥0) : ℝ) = 2 ^ 2 * π by push_cast; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have habs : ∫ g, |g i - g j| ∂stdGaussianPi M = 2 / √π := by
    have hl : HasLaw (fun g : Fin M → ℝ => g i - g j) (gaussianReal 0 2) (stdGaussianPi M) :=
      ⟨Measurable.aemeasurable (by fun_prop), stdGaussianPi_map_sub hij⟩
    have h := hl.integral_comp (f := fun x => |x|) measurable_abs.aestronglyMeasurable
    rw [integral_abs_gaussianReal two_ne_zero, hsqrt] at h
    have h' : ∫ g, |g i - g j| ∂stdGaussianPi M = 2 * ((2 : ℝ≥0) : ℝ) / (2 * √π) := h
    rw [h']
    have : (0 : ℝ) < √π := Real.sqrt_pos.2 Real.pi_pos
    push_cast
    field_simp
  have hij_int : Integrable (fun g : Fin M → ℝ => g i + g j) (stdGaussianPi M) := hi.add hj
  have habs_int : Integrable (fun g : Fin M → ℝ => |g i - g j|) (stdGaussianPi M) :=
    (hi.sub hj).abs
  calc 1 / √π = (0 + 0 + 2 / √π) / 2 := by ring
    _ = ∫ g, (g i + g j + |g i - g j|) / 2 ∂stdGaussianPi M := by
        rw [integral_div, integral_add hij_int habs_int, integral_add hi hj,
          integral_eval_stdGaussianPi, integral_eval_stdGaussianPi, habs]
    _ ≤ ∫ g, ⨆ k, g k ∂stdGaussianPi M :=
        integral_mono ((hij_int.add habs_int).div_const 2) (integrable_iSup_eval (by omega)) hpt

/-! ### The main theorem -/

/- @[blueprint "lem:gaussian-max-mp-ge-one"
  (statement := /-- For $M \ge 4096$ and $t = \sqrt{\log M}$,
    $M\,\mathbb P(g > t) \ge 1$. Indeed $t \ge 1$, so by the Mills-ratio bound
    $M\,\mathbb P(g > t) \ge M e^{-t^2/2}/(2t\sqrt{2\pi}) = \sqrt M/(2\sqrt{2\pi \log M})$, and
    $8\pi \log M \le 16\pi\sqrt M \le M$. -/)] -/
theorem one_le_mul_gaussianReal_real_Ioi_sqrt_log (hM : 4096 ≤ M) :
    1 ≤ M * (gaussianReal 0 1).real (Ioi (√(Real.log M))) := by
  have hMpos : (0 : ℝ) < M := by positivity
  have hM' : (4096 : ℝ) ≤ M := by exact_mod_cast hM
  set L := Real.log M with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have h4096 : Real.log 4096 = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
  have hL12 : 12 * Real.log 2 ≤ L := h4096 ▸ Real.log_le_log (by norm_num) hM'
  have hL1 : 1 ≤ L := by linarith [Real.log_two_gt_d9]
  set t := √L with ht_def
  have ht1 : 1 ≤ t := by rw [ht_def, Real.le_sqrt zero_le_one hL0]; simpa using hL1
  have ht0 : 0 < t := by linarith
  have htsq : t ^ 2 = L := Real.sq_sqrt hL0
  -- √M ≥ 64 and log M ≤ 2 √M
  have hsqrtM : 64 ≤ √M := by
    rw [Real.le_sqrt (by norm_num) hMpos.le]; norm_num; exact_mod_cast hM
  have hsqrtM_sq : √(M : ℝ) ^ 2 = M := Real.sq_sqrt hMpos.le
  have hlog_le : L ≤ 2 * √M := by
    have h1 : Real.log (√(M : ℝ)) ≤ √M - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_sqrt hMpos.le] at h1
    linarith
  -- 2 t √(2π) ≤ √M
  have hpi := Real.pi_lt_d2
  have hkey : 2 * t * √(2 * π) ≤ √M := by
    rw [Real.le_sqrt (by positivity) hMpos.le, mul_pow, mul_pow, htsq,
      Real.sq_sqrt (by positivity)]
    nlinarith
  -- M e^{-t²/2} = √M
  have hexp : (M : ℝ) * exp (-t ^ 2 / 2) = √M := by
    rw [htsq, neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hMpos]
    have : (0 : ℝ) < √M := by positivity
    nth_rewrite 1 [← Real.mul_self_sqrt hMpos.le]
    field_simp
  -- conclude
  have hp := gaussianReal_real_Ioi_ge_of_one_le ht1
  calc (1 : ℝ) = (M * exp (-t ^ 2 / 2)) / (2 * t * √(2 * π)) * ((2 * t * √(2 * π)) / √M) := by
        rw [hexp]; field_simp
    _ ≤ (M * exp (-t ^ 2 / 2)) / (2 * t * √(2 * π)) * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; exact hkey
    _ = M * (1 / (2 * t) * exp (-t ^ 2 / 2) / √(2 * π)) := by field_simp
    _ ≤ M * (gaussianReal 0 1).real (Ioi t) := by gcongr

/- @[blueprint "thm:gaussian-max-lower-explicit"
  (statement := /-- For $M \ge 2$ i.i.d. standard Gaussians $g_1, \dots, g_M$,
    $\mathbb E \max_{j \le M} g_j \ge \tfrac16 \sqrt{\log M}$. -/)] -/
theorem gaussian_max_lower_explicit (hM : 2 ≤ M) :
    1 / 6 * √(Real.log M) ≤ ∫ g, ⨆ j, g j ∂stdGaussianPi M := by
  /- Case $M \le 4096$: $\tfrac16\sqrt{\log M} \le \tfrac16\sqrt{12 \log 2} \le 1/\sqrt\pi
    \le \mathbb E \max(g_1, g_2)$. Case $M \ge 4096$: with $t = \sqrt{\log M} \ge 2$,
    $M\,\mathbb P(g > t) \ge 1$ gives $\gamma_M(\max > t) \ge 1/2$, hence
    $\mathbb E \max \ge t/2 - 1/\sqrt{2\pi} \ge t/6$. -/
  have hMpos : (0 : ℝ) < M := by positivity
  have hL0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_three
  rcases le_or_gt M 4096 with hsmall | hlarge
  · refine le_trans ?_ (integral_iSup_eval_ge_two hM)
    have h4096 : Real.log 4096 = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    have hL : Real.log M ≤ 12 * Real.log 2 :=
      h4096 ▸ Real.log_le_log hMpos (by exact_mod_cast hsmall)
    have hl2 := Real.log_two_lt_d9
    set s := √(Real.log M) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hssq : s ^ 2 = Real.log M := Real.sq_sqrt hL0
    set q := √π with hq
    have hq0 : 0 < q := Real.sqrt_pos.2 Real.pi_pos
    have hqsq : q ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
    have hsq : s * q ≤ 6 := by
      have h1 : (s * q) ^ 2 ≤ 36 := by rw [mul_pow, hssq, hqsq]; nlinarith
      nlinarith [mul_nonneg hs0 hq0.le]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by norm_num) hq0]
    linarith
  · have hM' : 4096 ≤ M := hlarge.le
    set t := √(Real.log M) with ht_def
    have h4096 : Real.log 4096 = 12 * Real.log 2 := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num
    have hL12 : 12 * Real.log 2 ≤ Real.log M :=
      h4096 ▸ Real.log_le_log (by norm_num) (by exact_mod_cast hM')
    have hL4 : 4 ≤ Real.log M := by linarith [Real.log_two_gt_d9]
    have ht2 : 2 ≤ t := by rw [ht_def, Real.le_sqrt (by norm_num) hL0]; linarith
    have hhalf := stdGaussianPi_real_lt_iSup_ge_half (by omega)
      (one_le_mul_gaussianReal_real_Ioi_sqrt_log hM')
    have hE := integral_iSup_eval_ge_tail (M := M) (by omega) t
    have hc : 1 / √(2 * π) ≤ 2 / 3 := by
      have h32 : 3 / 2 ≤ √(2 * π) := by
        rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    rw [← ht_def] at hhalf
    have hPle : (stdGaussianPi M).real {g | t < ⨆ j, g j} ≤ 1 := measureReal_le_one
    nlinarith

/- @[blueprint "thm:gaussian-max-lower"
  (statement := /-- There is a universal constant $c > 0$ (one can take $c = 1/6$) such that
    for every $M \ge 2$, if $g_1, \dots, g_M$ are i.i.d. standard Gaussians then
    $\mathbb E \max_{j \le M} g_j \ge c \sqrt{\log M}$. -/)] -/
theorem gaussian_max_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, 2 ≤ M →
      c * √(Real.log M) ≤ ∫ g, ⨆ j, g j ∂stdGaussianPi M :=
  ⟨1 / 6, by norm_num, fun _ hM => gaussian_max_lower_explicit hM⟩

end FoML.ToMathlib
