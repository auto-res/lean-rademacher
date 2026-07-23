import FoML.Generalization.Confidence
import FoML.Model.LinearPredictorL1

/-!
# Generalization bounds for `ℓ₁/ℓ∞` linear predictors

This module connects the fixed-sample estimates in `FoML.Model.LinearPredictorL1`
to expected and high-probability uniform-deviation bounds.
-/

section

universe u v

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Fixed-sample empirical Rademacher bound for `ℓ₁` predictors:

`R̂ₙ ≤ (X∞ W / √n) * √(2 log(2d))`.
-/
theorem linear_predictor_l1_bound
    [Nonempty ι]
    (d : ℕ) (Xinf W : ℝ)
    (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (S : Fin n → LinftyBall (d := d) Xinf)
    (w : ι → L1Ball (d := d) W) :
    empiricalRademacherComplexity n
      (fun i x ↦ ∑ j : Fin d, (w i).1 j * x j)
      (Subtype.val ∘ S) ≤
      (Xinf * W / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * d)) := by
  exact linear_predictor_l1_bound'
    (d := d) (n := n) (Xinf := Xinf) (W := W)
    hX hW d_pos n_pos S w

/--
Expected Rademacher-complexity bound for the full `ℓ₁`-bounded class:

`Rₙ(F₁,W; μ) ≤ (X∞ W / √n) * √(2 log(2d))`.
-/
theorem linear_predictor_l1_rademacher_complexity_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z) :
    rademacherComplexity n
        (linearPredictorL1 :
          L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
        μ Z
      ≤ (Xinf * W / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * d)) := by
  letI : Nonempty (L1Ball (d := d) W) := nonempty_L1Ball hW
  apply rademacherComplexity_le_of_empirical_le_separable
    (F := linearPredictorL1) (X := Z)
  · intro w
    exact (continuous_linearPredictorL1_input w).measurable.comp hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le hX w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W hX hW d_pos n_pos

/--
Expected uniform-deviation bound for the full `ℓ₁`-bounded class:

`𝔼[UDₙ] ≤ 2 (X∞ W / √n) √(2 log(2d))`.
-/
theorem linear_predictor_l1_uniform_deviation_expectation_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z) :
    μⁿ[fun S : Fin n → Ω ↦
      uniformDeviation n
        (linearPredictorL1 :
          L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
        μ Z (Z ∘ S)]
      ≤ 2 * ((Xinf * W / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * d))) := by
  letI : Nonempty (L1Ball (d := d) W) := nonempty_L1Ball hW
  letI : Nonempty (LinftyBall (d := d) Xinf) := nonempty_LinftyBall hX
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (F := linearPredictorL1) n_pos
  · exact fun w ↦ (continuous_linearPredictorL1_input w).measurable
  · exact hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le hX w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W hX hW d_pos n_pos

/--
High-probability `ε`-form bound for the full `ℓ₁` class:

`Pr{UDₙ ≥ 2 (X∞ W / √n) √(2 log(2d)) + ε}
  ≤ exp (-n ε² / (2 (X∞ W)²))`.
-/
theorem linear_predictor_l1_uniform_deviation_tail_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 < Xinf) (hW : 0 < W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * ((Xinf * W / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * d))) + ε ≤
        uniformDeviation n
          (linearPredictorL1 :
            L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
          μ Z (Z ∘ S)}).toReal
      ≤ (-ε ^ 2 * n / (2 * (Xinf * W) ^ 2)).exp := by
  letI : Nonempty (L1Ball (d := d) W) := nonempty_L1Ball hW.le
  letI : Nonempty (LinftyBall (d := d) Xinf) := nonempty_LinftyBall hX.le
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (F := linearPredictorL1)
  · exact fun w ↦ (continuous_linearPredictorL1_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le hX.le w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W hX.le hW.le d_pos n_pos
  · exact hε

/--
End-to-end confidence bound for the full `ℓ₁`-bounded linear class:

`Pr{UDₙ ≥ 2 (X∞ W / √n) √(2 log(2d))
    + X∞ W √(2 log(1/δ)/n)} ≤ δ`.

The first term is the complexity contribution; the second is the
concentration contribution.
-/
theorem linear_predictor_l1_uniform_deviation_tail_bound_delta
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 < Xinf) (hW : 0 < W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          ((Xinf * W / Real.sqrt (n : ℝ)) *
            Real.sqrt (2 * Real.log (2 * d))) +
        (Xinf * W) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
          uniformDeviation n
            (linearPredictorL1 :
              L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (L1Ball (d := d) W) := nonempty_L1Ball hW.le
  letI : Nonempty (LinftyBall (d := d) Xinf) := nonempty_LinftyBall hX.le
  apply uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) n_pos (F := linearPredictorL1)
  · exact fun w ↦ (continuous_linearPredictorL1_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le hX.le w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W hX.le hW.le d_pos n_pos
  · exact hδ
  · exact hδ_one

/--
Sample-dependent end-to-end confidence bound for the full `ℓ₁` class:

`Pr{UDₙ ≥ 2 W Q∞(S) √(2 log(2d))
    + 3 X∞ W √(2 log(2/δ)/n)} ≤ δ`,

where `Q∞(S) = n⁻¹ supⱼ √(∑ₖ |Sₖⱼ|²)`.
-/
theorem linear_predictor_l1_uniform_deviation_tail_bound_of_sample_delta
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 < Xinf) (hW : 0 < W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (W * linearPredictorL1SampleRadius (Z ∘ S) *
            Real.sqrt (2 * Real.log (2 * d))) +
        3 * ((Xinf * W) * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n
            (linearPredictorL1 :
              L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (L1Ball (d := d) W) := nonempty_L1Ball hW.le
  letI : Nonempty (LinftyBall (d := d) Xinf) := nonempty_LinftyBall hX.le
  exact
    uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
      (μ := μ) (n := n) n_pos
      (linearPredictorL1 :
        L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
      (fun w ↦ (continuous_linearPredictorL1_input w).measurable)
      Z hZ
      (fun S ↦
        W * linearPredictorL1SampleRadius S *
          Real.sqrt (2 * Real.log (2 * d)))
      (mul_pos hX hW)
      (fun w x ↦ abs_linearPredictorL1_le hX.le w x)
      continuous_linearPredictorL1_weight
      (linear_predictor_l1_empirical_bound_of_sample
        d n Xinf W hW.le d_pos n_pos)
      hδ hδ_one

end
