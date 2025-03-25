import FoML.ForMathlib.Probability.Moments

/-!
# Hoeffding's lemma

This file states Hoeffding's lemma.

## Main results

* `ProbabilityTheory.hoeffding`: Hoeffding's Lemma states that for a random variable `X` with
  `E[X] = 0` (zero mean) and `a ≤ X ≤ b` almost surely, the inequality
  `mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.

## References

We follow [martin2019] and [mehryar2018] for the proof of Hoeffding's lemma.
-/

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac)

theorem cgf_zero_deriv [IsProbabilityMeasure μ] {X : Ω → ℝ} (h0 : μ[X] = 0) :
    let f' := fun t ↦ ∫ (x : Ω), X x ∂Measure.tilted μ fun ω ↦ t * X ω;
  f' 0 = 0 := by
  simp only [zero_mul, tilted_const', measure_univ, inv_one, one_smul]
  exact h0

theorem extracted_1 [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (ht : 0 ≤ t) (hX : AEMeasurable X μ)
  (h : ∀ᵐ (ω : Ω) ∂μ, X ω ∈ Set.Icc a b) (h0 : ∫ (x : Ω), X x ∂μ = 0) (w : ¬t = 0) :
  cgf X μ t ≤ t ^ 2 * (b - a) ^ 2 / 8 := by
  let f := fun t ↦ cgf X μ t
  have hf : f 0 = 0 := cgf_zero
  set f' : ℝ → ℝ := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X]
  have hf' : f' 0 = 0 := cgf_zero_deriv μ h0
  set f'' : ℝ → ℝ := fun t ↦ variance X (μ.tilted (fun ω ↦ t * X ω))
  have q : ∀ x : ℝ, ∃ c ∈ (Set.Ioo 0 t), f t = f 0 + f' 0 * t + f'' c * t ^ 2 / 2 := by
    let A := (f t - f 0 - f' 0 * t) * 2 / t ^ 2
    have q0 : f t = f 0 + f' 0 * t + A * t ^ 2 / 2 := by
      have q0' : A * t ^ 2 = (f t - f 0 - f' 0 * t) * 2 := by
        calc
        _ = (f t - f 0 - f' 0 * t) * 2 * t ^ 2 / t ^ 2 :=
          Eq.symm (mul_div_right_comm ((f t - f 0 - f' 0 * t) * 2) (t ^ 2) (t ^ 2))
        _ = (f t - f 0 - f' 0 * t) * 2 * (t ^ 2 / t ^ 2) := by ring
        _ = (f t - f 0 - f' 0 * t) * 2 := by field_simp only
      rw [q0']
      ring
    set g : ℝ → ℝ := fun x ↦ f t - f x - f' x * (t - x) - A * (t - x) ^ 2 / 2
    have q1 : g 0 = 0 := by
      dsimp only [g, A]
      calc
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * t ^ 2 / t ^ 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * (t ^ 2 / t ^ 2) := by ring
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) := by ring
      _ = 0 := by ring
    have q2 : g t = 0 := by
      dsimp only [g]
      simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div]
    set g' : ℝ → ℝ := fun x ↦ - f'' x * (t - x) + A * (t - x)
    have q3 : ∀ x : ℝ, HasDerivAt g (g' x) x := by
      intro x
      apply HasDerivAt.add
      · rw [← (by ring : 0 - f' x + (f' x - f'' x * (t - x)) = - f'' x * (t - x))]
        apply ((hasDerivAt_const x _).sub (cgf_deriv_one a b hX h x)).add
        convert (cgf_deriv_two a b hX h x).mul ((hasDerivAt_id' x).add_const (-t)) using 1
        · ext; ring
        · dsimp [f', f'']
          have p : variance X (Measure.tilted μ fun ω ↦ x * X ω) =
              (μ.tilted fun ω ↦ x * X ω)[X ^ 2] - ((μ.tilted fun ω ↦ x * X ω)[X]) ^ 2 := by
            have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ x * X ω) :=
              isProbabilityMeasure_tilted (integrable_expt_bound hX h)
            have hμ := tilted_absolutelyContinuous μ fun ω ↦ x * X ω
            apply variance_def' <|
              MeasureTheory.memLp_of_bounded (hμ h) (AEMeasurable.aestronglyMeasurable (hX.mono_ac hμ)) 2
          rw [p]
          simp only [Pi.pow_apply, mul_one]
          ring
      · rw [(by ext x; ring : (fun x ↦ -(A * (t - x) ^ 2 / 2)) =
          (fun x ↦ -A * ((x - t) ^ 2 / 2))),
            (by ring : (A * (t - x)) = -A * (x - t))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2 / 2) = (fun y ↦ (1 / 2) * (y - t) ^ 2)),
            (by ring : x - t = (1 / 2) * (2 * (x - t)))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2) = (fun y ↦ y ^ 2 - 2 * t * y + t ^ 2)),
            (by ring : (2 * (x - t)) = 2 * (x ^ (2 - 1)) - 2 * t + 0)]
        apply HasDerivAt.add
        apply HasDerivAt.add
        apply hasDerivAt_pow
        rw [(by ext x; ring : (fun x ↦ -(2 * t * x)) = (fun x ↦ (x * -(2 * t))))]
        apply hasDerivAt_mul_const
        apply hasDerivAt_const
    have q4 : ∃ c ∈ (Set.Ioo 0 t), g' c = 0 := by
      apply exists_hasDerivAt_eq_zero (lt_of_le_of_ne ht fun a ↦ w (a.symm))
      apply HasDerivAt.continuousOn
      intros x _; exact q3 x
      rw [q1, q2]
      intros x _; exact q3 x
    obtain ⟨c, ⟨cq, cq'⟩⟩ := q4
    intro
    use c; constructor
    · exact cq
    · dsimp only [g'] at cq';
      have cq'' : (A - f'' c) * (t - c) = 0 := by linarith
      have cq''' : A = f'' c := by
        have cr : (A - f'' c) = 0 := by
          simp only [mul_eq_zero] at cq''
          obtain cq''' | cq'''' := cq''
          · exact cq'''
          · dsimp only [Set.Ioo] at cq
            obtain ⟨_, cq2⟩ := cq
            linarith
        linarith
      rw [← cq''']
      exact q0
  rw [hf, hf'] at q
  simp only [Set.mem_Ioo, zero_mul, add_zero, zero_add, forall_const] at q
  obtain ⟨c, ⟨_, cq'⟩⟩ := q
  have s : f t ≤ t^2 * (b - a)^2 / 8 := by
    rw [cq']
    calc
    _ ≤ ((b - a) / 2) ^ 2 * t ^ 2 / 2 := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      dsimp [f'']
      have _ : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
        isProbabilityMeasure_tilted (integrable_expt_bound hX h)
      exact tilt_var_bound a b c h hX
      exact sq_nonneg t; simp only [inv_nonneg, Nat.ofNat_nonneg]
    _ = t ^ 2 * (b - a) ^ 2 / 8 := by ring
  exact s

/-! ### Hoeffding's lemma restricted to t ≥ 0-/

theorem hoeffding_nonneg [IsProbabilityMeasure μ]
    (t a b : ℝ) {X : Ω → ℝ} (ht : 0 ≤ t) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
  dsimp [mgf]
  by_cases w : t = 0;
    · rw [w]; simp only [zero_mul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, le_refl]
  set f : ℝ → ℝ := fun t ↦ cgf X μ t
  suffices f t ≤ t^2 * (b - a)^2 / 8 from by
    rw [<- log_le_iff_le_exp]
    exact this
    apply mgf_pos' (Ne.symm (NeZero.ne' μ))
    apply integrable_expt_bound hX h
  exact ProbabilityTheory.extracted_1 μ t a b ht hX h h0 w

/-! ### Hoeffding's lemma-/

/-- Hoeffding's Lemma states that for a random variable `X` with `E[X] = 0` (zero mean) and
 `a ≤ X ≤ b` almost surely, the inequality
 `μ[exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.-/
theorem hoeffding [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
  by_cases h' : 0 ≤ t
  case pos =>
    exact hoeffding_nonneg μ t a b h' hX h h0
  case neg =>
    simp only [not_le] at h'
    suffices ∫ ω, rexp (- t * - X ω) ∂μ ≤
      rexp ((- t) ^ 2 * ((- a) - (- b)) ^ 2 / 8) from by
      simp only [mul_neg, neg_mul, neg_neg, even_two, Even.neg_pow, sub_neg_eq_add] at this
      rw [<- (by ring : (-a + b) = b - a)]
      exact this
    apply hoeffding_nonneg _ _ _ _ (by linarith : 0 ≤ - t) hX.neg
    · simp only [Set.mem_Icc, neg_le_neg_iff, Filter.eventually_and]
      exact ⟨h.mono fun ω h ↦ h.2, h.mono fun ω h ↦ h.1⟩
    · rw [integral_neg]
      simp only [neg_eq_zero]
      exact h0

end ProbabilityTheory
