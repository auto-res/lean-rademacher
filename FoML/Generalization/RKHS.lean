import FoML.Generalization.Confidence
import FoML.Model.RKHS

/-!
# Generalization bounds for feature-map RKHS classes

This module connects the fixed-sample kernel-trace estimate to the separable
generalization bridges.  The two high-probability endpoints retain either the
observed kernel trace or only the uniform diagonal radius.
-/

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω]
variable {𝒳 : Type v} [MeasurableSpace 𝒳]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SeparableSpace H]
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Expected Rademacher estimate for the bounded feature-map class:

`Rₙ ≤ r Λ / √n`.
-/
theorem rkhs_rademacherComplexity_le
    [IsProbabilityMeasure μ]
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X) :
    rademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) μ X ≤
      r * Λ / Real.sqrt (n : ℝ) := by
  letI : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ).to_subtype
  apply rademacherComplexity_le_of_empirical_le_separable
    (F := rkhsPredictor Φ) (X := X)
  · intro w
    exact (measurable_rkhsPredictor_input Φ hΦ w).comp hX
  · exact mul_nonneg hr hΛ
  · exact fun w x ↦ abs_rkhsPredictor_le Φ hΛ hr hdiag w x
  · exact continuous_rkhsPredictor_weight Φ
  · exact rkhs_empiricalRademacherComplexity_le Φ Λ r hΛ hr hdiag

/--
Expected uniform-deviation estimate:

`E[UDₙ] ≤ 2 r Λ / √n`.
-/
theorem rkhs_uniformDeviation_expectation_le
    [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X) :
    μⁿ[fun S : Fin n → Ω ↦
      uniformDeviation n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
        μ X (X ∘ S)] ≤
      2 * (r * Λ / Real.sqrt (n : ℝ)) := by
  letI : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ).to_subtype
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (F := rkhsPredictor Φ) hn
  · exact fun w ↦ measurable_rkhsPredictor_input Φ hΦ w
  · exact hX
  · exact mul_nonneg hr hΛ
  · exact fun w x ↦ abs_rkhsPredictor_le Φ hΛ hr hdiag w x
  · exact continuous_rkhsPredictor_weight Φ
  · exact rkhs_empiricalRademacherComplexity_le Φ Λ r hΛ hr hdiag

/--
Deterministic confidence bound obtained from the diagonal estimate:

`Pr{UDₙ ≥ 2 rΛ/√n + rΛ sqrt(2 log(1/δ)/n)} ≤ δ`.

In the notation of Mohri et al., Theorem 6.12, Lean's `Λ` is the RKHS weight
radius and `r²` bounds `K(x,x)`.  `CompleteSpace H` records that the feature
space is Hilbert, `SeparableSpace H` is needed only for the uncountable-class
generalization bridge, `hΦ` supplies measurability of every predictor, and
`hdiag` supplies both the Rademacher and concentration radii.
-/
theorem rkhs_uniformDeviation_tail_bound_delta
    [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (r * Λ / Real.sqrt (n : ℝ)) +
          (r * Λ) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (rkhsPredictor Φ :
            Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
          μ X (X ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ.le).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) hn (F := rkhsPredictor Φ)
  · exact fun w ↦ measurable_rkhsPredictor_input Φ hΦ w
  · exact hX
  · exact mul_pos hr hΛ
  · exact fun w x ↦ abs_rkhsPredictor_le Φ hΛ.le hr.le hdiag w x
  · exact continuous_rkhsPredictor_weight Φ
  · exact rkhs_empiricalRademacherComplexity_le
      Φ Λ r hΛ.le hr.le hdiag
  · exact hδ
  · exact hδ_one

/--
Sample-dependent confidence bound retaining the observed kernel trace:

`Pr{UDₙ ≥ 2Λ/n sqrt(trace K_S)
    + 3rΛ sqrt(2 log(2/δ)/n)} ≤ δ`.
-/
theorem rkhs_uniformDeviation_tail_bound_kernelTrace_delta
    [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → H) (hΦ : Measurable Φ)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (X : Ω → 𝒳) (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ (X ∘ S))) +
          3 * ((r * Λ) *
            Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
        uniformDeviation n
          (rkhsPredictor Φ :
            Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
          μ X (X ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ.le).to_subtype
  exact uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
    (μ := μ) hn
    (rkhsPredictor Φ :
      Metric.closedBall (0 : H) Λ → 𝒳 → ℝ)
    (fun w ↦ measurable_rkhsPredictor_input Φ hΦ w)
    X hX
    (fun S ↦ Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S))
    (mul_pos hr hΛ)
    (fun w x ↦ abs_rkhsPredictor_le Φ hΛ.le hr.le hdiag w x)
    (continuous_rkhsPredictor_weight Φ)
    (rkhs_empiricalRademacherComplexity_le_kernelTrace Φ Λ hΛ.le)
    hδ hδ_one

end
