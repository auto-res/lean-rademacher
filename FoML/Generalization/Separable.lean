import FoML.Generalization.Countable
import FoML.ForMathlib.Topology.SeparableSpace

/-!
# Rademacher generalization bounds for separable classes

For a family `F : H → 𝒳 → ℝ` that is continuous in `h`, all suprema relevant
to Rademacher complexity and uniform deviation can be computed on
`denseRestriction F : ℕ → 𝒳 → ℝ`. This file packages those equalities and
derives the separable-class API from the countable core.
-/

section

universe u v w

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒳 : Type w}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Empirical Rademacher complexity is unchanged after restricting a continuous
family to the chosen countable dense sequence.
-/
lemma empiricalRademacherComplexity_denseRestriction
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    (n : ℕ) {F : H → 𝒳 → ℝ}
    (hF : ∀ x : 𝒳, Continuous fun h ↦ F h x) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S =
      empiricalRademacherComplexity n (denseRestriction F) S := by
  dsimp [empiricalRademacherComplexity]
  congr
  ext σ
  apply separableSpaceSup_eq_real
  continuity

/-- Compatibility alias for `empiricalRademacherComplexity_denseRestriction`. -/
@[deprecated empiricalRademacherComplexity_denseRestriction (since := "2026-07-24")]
lemma empiricalRademacherComplexity_eq
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    (n : ℕ) {F : H → 𝒳 → ℝ}
    (hF : ∀ x : 𝒳, Continuous fun h ↦ F h x) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S =
      empiricalRademacherComplexity n (F ∘ denseSeq H) S :=
  empiricalRademacherComplexity_denseRestriction n hF S

/--
Expected Rademacher complexity is unchanged after restriction to
`denseRestriction F`.
-/
lemma rademacherComplexity_denseRestriction
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    (n : ℕ) (F : H → 𝒳 → ℝ)
    (hF : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity n F μ X =
      rademacherComplexity n (denseRestriction F) μ X := by
  dsimp [rademacherComplexity]
  congr
  ext S
  exact empiricalRademacherComplexity_denseRestriction n hF (X ∘ S)

/-- Compatibility alias with the former non-conventional capitalization. -/
@[deprecated rademacherComplexity_denseRestriction (since := "2026-07-24")]
lemma RademacherComplexity_eq
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    (n : ℕ) (F : H → 𝒳 → ℝ)
    (hF : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity n F μ X =
      rademacherComplexity n (F ∘ denseSeq H) μ X :=
  rademacherComplexity_denseRestriction n F hF μ X

/--
A uniform fixed-sample bound for a separable class lifts to expected
Rademacher complexity through `denseRestriction`.
-/
theorem rademacherComplexity_le_of_empirical_le_separable
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (X : Ω → 𝒳)
    (hF_meas : ∀ h, Measurable (F h ∘ X))
    {b C : ℝ} (hb : 0 ≤ b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C) :
    rademacherComplexity n F μ X ≤ C := by
  rw [rademacherComplexity_denseRestriction n F hF_cont μ X]
  apply rademacherComplexity_le_of_empirical_le_countable
    (f := denseRestriction F) (μ := μ)
  · exact fun i ↦ hF_meas (denseSeq H i)
  · exact hb
  · exact abs_denseRestriction_le hF_bound
  · intro S
    rw [← empiricalRademacherComplexity_denseRestriction n hF_cont S]
    exact hC S

/--
Uniform deviation is unchanged after restricting a continuous and uniformly
bounded family to `denseRestriction F`.
-/
lemma uniformDeviation_denseRestriction
    [MeasurableSpace 𝒳]
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    [FirstCountableTopology H]
    (n : ℕ) (F : H → 𝒳 → ℝ)
    (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    uniformDeviation n F μ X =
      uniformDeviation n (denseRestriction F) μ X := by
  ext S
  dsimp [uniformDeviation]
  apply separableSpaceSup_eq_real
  apply Continuous.abs
  apply Continuous.sub
  · continuity
  · have hdominated :
        ∀ h : H, ∀ᵐ ω : Ω ∂μ, ‖F h (X ω)‖ ≤ b := by
      intro h
      filter_upwards with ω
      exact hF_bound h (X ω)
    apply MeasureTheory.continuous_of_dominated _ hdominated
    · exact MeasureTheory.integrable_const _
    · filter_upwards with ω
      continuity
    · intro h
      exact (hF_meas h).comp hX |>.aestronglyMeasurable

/-- Compatibility alias for `uniformDeviation_denseRestriction`. -/
@[deprecated uniformDeviation_denseRestriction (since := "2026-07-24")]
lemma uniformDeviation_eq
    [MeasurableSpace 𝒳]
    [Nonempty H] [TopologicalSpace H] [SeparableSpace H]
    [FirstCountableTopology H]
    (n : ℕ) (F : H → 𝒳 → ℝ)
    (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    uniformDeviation n F μ X =
      uniformDeviation n (F ∘ denseSeq H) μ X :=
  uniformDeviation_denseRestriction
    n F hF_meas X hX hF_bound hF_cont μ

/--
Expected uniform-deviation bound for a separable class from a deterministic
fixed-sample empirical Rademacher bound.
-/
theorem uniform_deviation_expectation_le_of_empirical_le_separable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 ≤ b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C) :
    μⁿ[fun S : Fin n → Ω ↦ uniformDeviation n F μ X (X ∘ S)] ≤
      2 * C := by
  calc
    μⁿ[fun S : Fin n → Ω ↦ uniformDeviation n F μ X (X ∘ S)] =
        μⁿ[fun S : Fin n → Ω ↦
          uniformDeviation n (denseRestriction F) μ X (X ∘ S)] := by
      apply integral_congr_ae
      filter_upwards with S
      exact congrFun
        (uniformDeviation_denseRestriction
          n F hF_meas X hX hF_bound hF_cont μ) (X ∘ S)
    _ ≤ 2 * C := by
      apply uniform_deviation_expectation_le_of_empirical_le_countable
        (f := denseRestriction F) (μ := μ) hn X
      · exact fun i ↦ (hF_meas (denseSeq H i)).comp hX
      · exact hb
      · exact abs_denseRestriction_le hF_bound
      · intro S
        rw [← empiricalRademacherComplexity_denseRestriction n hF_cont S]
        exact hC S

/--
Separable-class tail bound obtained from the countable core by
`denseRestriction`.
-/
theorem uniform_deviation_tail_bound_separable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    {t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * rademacherComplexity n F μ X + ε ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      (-ε ^ 2 * t * n).exp := by
  calc
    _ = (μⁿ {S |
        2 * rademacherComplexity n (denseRestriction F) μ X + ε ≤
          uniformDeviation n (denseRestriction F) μ X (X ∘ S)}).toReal := by
      congr
      ext S
      rw [rademacherComplexity_denseRestriction n F hF_cont μ X]
      rw [uniformDeviation_denseRestriction
        n F hF_meas X hX hF_bound hF_cont μ]
    _ ≤ _ := by
      apply uniform_deviation_tail_bound_countable
        (denseRestriction F) _ X hX hb _ ht hε
      · exact measurable_denseRestriction_apply hF_meas
      · exact abs_denseRestriction_le hF_bound

/-- Optimized separable-class tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_separable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * rademacherComplexity n F μ X + ε ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by
    dsimp only [t]
    field_simp)
  calc
    _ ≤ (-ε ^ 2 * t * n).exp :=
      uniform_deviation_tail_bound_separable
        (μ := μ) F hF_meas X hX hb.le hF_bound hF_cont ht hε
    _ = _ := by
      dsimp only [t]
      field_simp

/--
Replace expected Rademacher complexity in the separable-class tail bound by
any deterministic upper bound `C`.
-/
theorem uniform_deviation_tail_bound_separable_of_rademacher_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : rademacherComplexity n F μ X ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * C + ε ≤ uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ ≤ (μⁿ {S |
        2 * rademacherComplexity n F μ X + ε ≤
          uniformDeviation n F μ X (X ∘ S)}).toReal := by
      apply measureReal_superlevel_mono
      intro S
      gcongr
    _ ≤ _ :=
      uniform_deviation_tail_bound_separable_of_pos
        (μ := μ) F hF_meas X hX hb hF_bound hF_cont hε

/--
Separable-class tail bound with a deterministic fixed-sample upper bound on
empirical Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_separable_of_empirical_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * C + ε ≤ uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  apply uniform_deviation_tail_bound_separable_of_rademacher_le
    (μ := μ) F hF_meas X hX hb hF_bound hF_cont _ hε
  exact rademacherComplexity_le_of_empirical_le_separable
    F X (fun h ↦ (hF_meas h).comp hX) hb.le hF_bound hF_cont hC

/--
Sample-dependent separable-class tail bound retaining the observed empirical
Rademacher complexity in the threshold.
-/
theorem uniform_deviation_tail_bound_separable_of_empirical_complexity
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      2 * empiricalRademacherComplexity n F (X ∘ S) + 3 * ε ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ = (μⁿ {S : Fin n → Ω |
        2 * empiricalRademacherComplexity n (denseRestriction F) (X ∘ S) +
            3 * ε ≤
          uniformDeviation n (denseRestriction F) μ X (X ∘ S)}).toReal := by
      congr
      ext S
      rw [empiricalRademacherComplexity_denseRestriction n hF_cont (X ∘ S)]
      rw [uniformDeviation_denseRestriction
        n F hF_meas X hX hF_bound hF_cont μ]
    _ ≤ _ :=
      uniform_deviation_tail_bound_countable_of_empirical_complexity
        (μ := μ) (denseRestriction F)
        (measurable_denseRestriction_apply hF_meas)
        X hX hb (abs_denseRestriction_le hF_bound) hε

/--
Sample-dependent separable-class tail bound with a pointwise upper bound
`C S` on empirical Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_separable_of_sample_empirical_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    (C : (Fin n → 𝒳) → ℝ)
    {b : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C S)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      2 * C (X ∘ S) + 3 * ε ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ ≤ (μⁿ {S : Fin n → Ω |
        2 * empiricalRademacherComplexity n F (X ∘ S) + 3 * ε ≤
          uniformDeviation n F μ X (X ∘ S)}).toReal := by
      apply measureReal_superlevel_mono
      intro S
      gcongr
      exact hC (X ∘ S)
    _ ≤ _ :=
      uniform_deviation_tail_bound_separable_of_empirical_complexity
        (μ := μ) F hF_meas X hX hb hF_bound hF_cont hε

end
