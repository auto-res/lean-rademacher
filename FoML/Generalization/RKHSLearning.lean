import FoML.Generalization.Learning
import FoML.Learning.Contraction
import FoML.Model.RKHS
import FoML.Rademacher.Reindex

/-!
# Finite RKHS model selection with a Lipschitz loss

The contraction theorem currently proved in this repository treats finite
hypothesis types.  This module combines it with the feature-map RKHS trace
estimate and the approximate-ERM oracle inequality.  Thus it provides a fully
proved loss-to-excess-risk endpoint while leaving the extension of contraction
to an arbitrary separable Hilbert ball as a separate task.
-/

noncomputable section

universe u v w x y

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω]
variable {𝒳 : Type v} {𝒴 : Type w}
variable {E : Type x} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {G : Type y} [Fintype G] [Nonempty G]
  [TopologicalSpace G] [DiscreteTopology G]
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Sample-dependent excess-risk bound for an approximate ERM over a finite
collection of RKHS weights.

The loss must vanish at prediction zero and be `L`-Lipschitz.  The resulting
threshold contains

`4 * (2 L Λ / n * sqrt(trace K_S))`,

where the factor `2` is the contraction constant for this repository's
absolute empirical Rademacher complexity.
-/
theorem finite_rkhs_approxERM_excessRisk_tail_bound_delta
    [MeasurableSpace (𝒳 × 𝒴)] [Nonempty (𝒳 × 𝒴)]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (Φ : 𝒳 → E)
    (Λ r : ℝ) (hΛ : 0 < Λ) (hr : 0 < r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (weights : G → Metric.closedBall (0 : E) Λ)
    (loss : ℝ → 𝒴 → ℝ)
    {L b η : ℝ} (hL : 0 ≤ L)
    (hloss_zero : ∀ y, loss 0 y = 0)
    (hloss_lip : ∀ y u v, |loss u y - loss v y| ≤ L * |u - v|)
    (hclass_meas :
      ∀ g, Measurable
        (supervisedLossClass
          (fun g x ↦ rkhsPredictor Φ (weights g) x) loss g))
    (hb : 0 < b)
    (hclass_bound :
      ∀ g z,
        |supervisedLossClass
          (fun g x ↦ rkhsPredictor Φ (weights g) x) loss g z| ≤ b)
    (Z : Ω → 𝒳 × 𝒴) (hZ : Measurable Z)
    (A : (Fin n → 𝒳 × 𝒴) → G)
    (hA : ∀ S,
      IsApproxERM η n
        (supervisedLossClass
          (fun g x ↦ rkhsPredictor Φ (weights g) x) loss)
        S (A S))
    (gstar : G) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      4 *
          (2 * L *
            (Λ * (n : ℝ)⁻¹ *
              Real.sqrt
                (kernelTrace Φ (fun k ↦ (Z (S k)).1)))) +
          6 * sampleConfidenceRadius b δ n + η ≤
        excessRisk
          (supervisedLossClass
            (fun g x ↦ rkhsPredictor Φ (weights g) x) loss)
          μ Z (A (Z ∘ S)) gstar}).toReal ≤ δ := by
  let predictor : G → 𝒳 → ℝ :=
    fun g x ↦ rkhsPredictor Φ (weights g) x
  let lossClass : G → (𝒳 × 𝒴) → ℝ :=
    supervisedLossClass predictor loss
  let C : (Fin n → 𝒳 × 𝒴) → ℝ :=
    fun S ↦
      2 * L *
        (Λ * (n : ℝ)⁻¹ *
          Real.sqrt (kernelTrace Φ (fun k ↦ (S k).1)))
  have hC : ∀ S,
      empiricalRademacherComplexity n lossClass S ≤ C S := by
    intro S
    have hcontract :
        empiricalRademacherComplexity n lossClass S ≤
          2 * L *
            empiricalRademacherComplexity n
              (fun (g : G) (z : 𝒳 × 𝒴) ↦ predictor g z.1) S := by
      apply empiricalRademacherComplexity_contraction_finite
        n (fun (g : G) (z : 𝒳 × 𝒴) ↦ predictor g z.1)
          (fun z u ↦ loss u z.2) S hL
      · exact fun z ↦ hloss_zero z.2
      · exact fun z u v ↦ hloss_lip z.2 u v
    have hsubclass :
        empiricalRademacherComplexity n
            (fun (g : G) (z : 𝒳 × 𝒴) ↦ predictor g z.1) S ≤
          empiricalRademacherComplexity n
            (fun (w : Metric.closedBall (0 : E) Λ) (z : 𝒳 × 𝒴) ↦
              rkhsPredictor Φ w z.1) S := by
      exact empiricalRademacherComplexity_reindex_le
        (fun (w : Metric.closedBall (0 : E) Λ) (z : 𝒳 × 𝒴) ↦
          rkhsPredictor Φ w z.1)
        weights S
        (mul_nonneg hr.le hΛ.le)
        (fun w z ↦ abs_rkhsPredictor_le
          Φ hΛ.le hr.le hdiag w z.1)
    have htrace :
        empiricalRademacherComplexity n
            (fun (w : Metric.closedBall (0 : E) Λ) (z : 𝒳 × 𝒴) ↦
              rkhsPredictor Φ w z.1) S ≤
          Λ * (n : ℝ)⁻¹ *
            Real.sqrt (kernelTrace Φ (fun k ↦ (S k).1)) := by
      exact rkhs_empiricalRademacherComplexity_le_kernelTrace
        (Φ := fun z : 𝒳 × 𝒴 ↦ Φ z.1) Λ hΛ.le S
    calc
      empiricalRademacherComplexity n lossClass S ≤
          2 * L *
            empiricalRademacherComplexity n
              (fun (g : G) (z : 𝒳 × 𝒴) ↦ predictor g z.1) S :=
        hcontract
      _ ≤ 2 * L *
          (Λ * (n : ℝ)⁻¹ *
            Real.sqrt (kernelTrace Φ (fun k ↦ (S k).1))) := by
        gcongr
        exact hsubclass.trans htrace
      _ = C S := rfl
  have htail :=
    approxERM_excessRisk_tail_bound_separable_of_sample_empirical_le_delta
      (μ := μ) hn lossClass
      (by simpa only [lossClass, predictor] using hclass_meas)
      Z hZ C hb
      (by simpa only [lossClass, predictor] using hclass_bound)
      (fun _ ↦ continuous_of_discreteTopology)
      A
      (by simpa only [lossClass, predictor] using hA)
      hC gstar hδ hδ_one
  simpa only [lossClass, predictor, C, Function.comp_apply] using htail

end
