import FoML.Entropy.FiniteClass
import FoML.Generalization.Confidence

/-!
# Generalization bounds from explicit finite-class entropy

These corollaries insert the finite-class Dudley estimate into the countable
generalization bridge.  The resulting probability thresholds contain only
`card H`, never an unevaluated covering number.
-/

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒳 : Type w}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Finite-class Dudley confidence bound with arbitrary truncation `α`.
-/
theorem uniform_deviation_tail_bound_finite_of_dudley_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Fintype H] [Nonempty H] [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (hNorm : ∀ (S : Fin n → 𝒳) h, empiricalNorm S (F h) ≤ c)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * finiteClassDudleyEstimate n (Fintype.card H) α c +
          3 * sampleConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  apply uniform_deviation_tail_bound_countable_of_sample_empirical_le_delta
    (μ := μ) hn F hF_meas X hX
    (fun _ ↦ finiteClassDudleyEstimate n (Fintype.card H) α c)
    hb hF_bound
  · intro S
    exact empiricalRademacherComplexity_le_finiteClassDudleyEstimate
      F S hn hα hαc (hNorm S)
  · exact hδ
  · exact hδ_one

/--
Concrete finite-class confidence bound obtained by setting `α = c/4`:

`Pr{UDₙ ≥ 2(c + 3c/√n √log(2|H|)) + 3r₂} ≤ δ`.
-/
theorem uniform_deviation_tail_bound_finite_of_dudley_quarter_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Fintype H] [Nonempty H] [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hn : 0 < n) (hc : 0 < c)
    (hNorm : ∀ (S : Fin n → 𝒳) h, empiricalNorm S (F h) ≤ c)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (c + (3 * c / Real.sqrt n) *
            Real.sqrt (Real.log (2 * Fintype.card H))) +
          3 * sampleConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  apply uniform_deviation_tail_bound_countable_of_sample_empirical_le_delta
    (μ := μ) hn F hF_meas X hX
    (fun _ ↦
      c + (3 * c / Real.sqrt n) *
        Real.sqrt (Real.log (2 * Fintype.card H)))
    hb hF_bound
  · intro S
    exact empiricalRademacherComplexity_le_finiteClassDudleyEstimate_quarter
      F S hn hc (hNorm S)
  · exact hδ
  · exact hδ_one

end
