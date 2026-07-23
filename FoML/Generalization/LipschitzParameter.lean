import FoML.Entropy.LipschitzParameter
import FoML.Generalization.Confidence

/-!
# Generalization bounds for one-dimensional Lipschitz families

The explicit interval grid and Dudley estimate are inserted into the
sample-dependent separable-class bridge.  The final threshold contains only
`ceil (2 W L / α)`, not a covering number or a total-boundedness proof.
-/

noncomputable section

universe u v

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {𝒳 : Type v}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Confidence bound for a family indexed by `t ∈ [-W,W]` and Lipschitz in `t`.
-/
theorem uniform_deviation_tail_bound_lipschitzParameter_dudley_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF_meas : ∀ t, Measurable (F t))
    (hF_lip : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α δ : ℝ} (hb : 0 < b) (hF_bound : ∀ t x, |F t x| ≤ b)
    (hα : 0 < α) (hαc : α < c / 2)
    (hNorm : ∀ (S : Fin n → 𝒳) t, empiricalNorm S (F t) ≤ c)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * lipschitzParameterDudleyEstimate n W L α c +
          3 * sampleConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  letI : Nonempty (Set.Icc (-W) W) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  have hF_cont : ∀ x : 𝒳, Continuous fun t ↦ F t x := by
    intro x
    apply (LipschitzWith.of_dist_le_mul (K := ⟨L, hL.le⟩) ?_).continuous
    intro t s
    rw [Subtype.dist_eq, Real.dist_eq]
    exact hF_lip t s x
  apply uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
    (μ := μ) hn F hF_meas X hX
    (fun _ ↦ lipschitzParameterDudleyEstimate n W L α c)
    hb hF_bound hF_cont
  · intro S
    exact empiricalRademacherComplexity_le_lipschitzParameterDudleyEstimate
      hn hW hL hα hαc F hF_lip S (hNorm S)
  · exact hδ
  · exact hδ_one

end
