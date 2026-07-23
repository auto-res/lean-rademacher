import FoML.Confidence
import FoML.LinearPredictorL2

/-!
# Generalization bounds for `ℓ₂` linear predictors

This module connects the fixed-sample estimates in `FoML.LinearPredictorL2`
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
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/--
Fixed-sample empirical Rademacher bound for `ℓ₂` linear predictors:

`R̂ₙ ≤ X * W / √n`.
-/
theorem linear_predictor_l2_bound
    [Nonempty ι]
    (d : ℕ) (W X : ℝ)
    (hX : 0 ≤ X) (hW : 0 ≤ W)
    (S : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (w : ι → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :
    empiricalRademacherComplexity
      n (fun i x ↦ ⟪((Subtype.val ∘ w) i), x⟫) (Subtype.val ∘ S) ≤
        X * W / √(n : ℝ) := by
  exact linear_predictor_l2_bound'
    (d := d) (n := n) (W := W) (X := X) hX hW S w

/--
Expected Rademacher-complexity bound for the full `ℓ₂`-bounded linear class:

`Rₙ(F₂,W; μ) ≤ X * W / √n`.
-/
theorem linear_predictor_l2_rademacher_complexity_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) :
    rademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
        μ Z
      ≤ X * W / Real.sqrt (n : ℝ) := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  apply rademacherComplexity_le_of_empirical_le_separable
    (F := linearPredictorL2) (X := Z)
  · intro w
    exact (continuous_linearPredictorL2_input w).measurable.comp hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX hW

/--
Expected uniform-deviation bound for the full `ℓ₂`-bounded linear class:

`𝔼[UDₙ] ≤ 2 * X * W / √n`.
-/
theorem linear_predictor_l2_uniform_deviation_expectation_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) :
    μⁿ[fun S : Fin n → Ω ↦
      uniformDeviation n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
        μ Z (Z ∘ S)]
      ≤ 2 * (X * W / Real.sqrt (n : ℝ)) := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX).to_subtype
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (F := linearPredictorL2) hn
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX hW

/--
High-probability `ε`-form bound for the full `ℓ₂` linear class:

`Pr{UDₙ ≥ 2 X W / √n + ε} ≤ exp (-n ε² / (2 (X W)²))`.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (_hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * (X * W / Real.sqrt (n : ℝ)) + ε ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ S)}).toReal
      ≤ (-ε ^ 2 * n / (2 * (X * W) ^ 2)).exp := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW.le).to_subtype
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX.le).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (F := linearPredictorL2)
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW.le w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX.le hW.le
  · exact hε

/--
End-to-end confidence bound for the full `ℓ₂`-bounded linear class:

`Pr{UDₙ ≥ 2 X W / √n + X W √(2 log(1/δ)/n)} ≤ δ`.

The first term is the Rademacher-complexity contribution and the second is
the concentration contribution.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound_delta
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (X * W / Real.sqrt (n : ℝ)) +
          (X * W) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW.le).to_subtype
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX.le).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) hn (F := linearPredictorL2)
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW.le w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX.le hW.le
  · exact hδ
  · exact hδ_one

/--
Sample-dependent end-to-end confidence bound for the full `ℓ₂` class:

`Pr{UDₙ ≥ (2W/n) √(∑ₖ ‖Zₖ‖²)
    + 3 X W √(2 log(2/δ)/n)} ≤ δ`.

The empirical norm sum is retained instead of being replaced by `n X²`.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound_of_sample_delta
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (W * (n : ℝ)⁻¹ *
            Real.sqrt
              (∑ k : Fin n,
                ‖(Z (S k) : EuclideanSpace ℝ (Fin d))‖ ^ 2)) +
        3 * ((X * W) * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n
            (linearPredictorL2 :
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW.le).to_subtype
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX.le).to_subtype
  have htail :=
    uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
      (μ := μ) (n := n) hn
      (linearPredictorL2 :
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
      (fun w ↦ (continuous_linearPredictorL2_input w).measurable)
      Z hZ
      (fun S ↦
        W * (n : ℝ)⁻¹ *
          Real.sqrt
            (∑ k : Fin n, ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2))
      (mul_pos hX hW)
      (fun w x ↦ abs_linearPredictorL2_le hW.le w x)
      continuous_linearPredictorL2_weight
      (linear_predictor_l2_empirical_bound_of_sample d n W X hW.le)
      hδ hδ_one
  simpa only [Function.comp_apply] using htail

end
