import FoML.Rademacher
import FoML.McDiarmid
import FoML.BoundedDifference
import FoML.ForMathlib.MeasureTheory.Measure.Real

/-!
# Rademacher generalization bounds for countable classes

This file contains the countable-class core of the generalization theory.
The main bridge combines

* symmetrization: `𝔼[UDₙ] ≤ 2 * Rₙ`;
* concentration of `UDₙ - 𝔼[UDₙ]`;
* monotonicity of superlevel events when `Rₙ` is replaced by a known upper
  bound.

Separable classes and confidence-parameter forms are developed in
`FoML.SeparableGeneralization` and `FoML.Confidence`.
-/

section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}
variable {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

private lemma normalized_two_mul_bound_mcdiarmid_scale
    (hn : 0 < n) {b t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2) :
    ((n : ℝ) * t / 2) * (n : ℝ) * ((n : ℝ)⁻¹ * 2 * b) ^ 2 ≤ 1 := by
  calc
    ((n : ℝ) * t / 2) * (n : ℝ) * ((n : ℝ)⁻¹ * 2 * b) ^ 2 =
        2 * (t * b ^ 2) := by
          field_simp
    _ ≤ 2 * (1 / 2 : ℝ) := by gcongr
    _ = 1 := by norm_num

/--
The expected empirical uniform deviation is bounded by twice the expected
Rademacher complexity:

`𝔼[UDₙ(F; S)] ≤ 2 * Rₙ(F; μ)`.
-/
theorem uniform_deviation_expectation_le_two_smul_rademacher_complexity
    [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤
      2 * rademacherComplexity n f μ X := by
  apply le_of_mul_le_mul_left _ (Nat.cast_pos.mpr hn)
  convert expectation_le_rademacher (μ := μ) (n := n) hf hb hf' using 1
  · rw [← integral_const_mul]
    apply integral_congr_ae (Filter.EventuallyEq.of_eq _)
    ext ω
    rw [uniformDeviation, Real.mul_iSup_of_nonneg (by norm_num)]
    apply congr_arg _ (funext (fun i ↦ ?_))
    rw [← show |(n : ℝ)| = n from abs_of_nonneg (by norm_num), ← abs_mul]
    apply congr_arg
    simp only [Nat.abs_cast, Function.comp_apply, nsmul_eq_mul]
    field_simp
  · ring

/--
Bridge from an upper bound on expected Rademacher complexity to an expected
uniform-deviation bound.
-/
theorem uniform_deviation_expectation_le_of_rademacher_le
    [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b C : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hC : rademacherComplexity n f μ X ≤ C) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤
      2 * C := by
  calc
    _ ≤ 2 * rademacherComplexity n f μ X :=
      uniform_deviation_expectation_le_two_smul_rademacher_complexity
        hn X hf hb hf'
    _ ≤ 2 * C := by
      simpa only [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_left hC (show (0 : ℝ) ≤ 2 by norm_num)

/--
A uniform fixed-sample upper bound on empirical Rademacher complexity bounds
the expected uniform deviation.
-/
theorem uniform_deviation_expectation_le_of_empirical_le_countable
    [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b C : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤
      2 * C := by
  apply uniform_deviation_expectation_le_of_rademacher_le hn X hf hb hf'
  exact rademacherComplexity_le_of_empirical_le_countable hf hb hf' hC

/-- McDiarmid tail bound for the centered empirical uniform deviation. -/
theorem uniform_deviation_mcdiarmid_tail
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    {X : Ω → 𝒳} (hX : Measurable X)
    (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hf' : ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω |
      uniformDeviation n f μ X (X ∘ ω) -
        μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≥ ε}).toReal ≤
      (-ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have hfX : ∀ i, Measurable (f i ∘ X) := fun i ↦ (hf i).comp hX
  calc
    _ ≤ (-2 * ε ^ 2 * (n * t / 2)).exp :=
      mcdiarmid_inequality_pos_iid_of_const hX
        (uniformDeviation_bounded_difference hn X hfX hf')
        (uniformDeviation_measurable X hf) hε
        (by simpa using normalized_two_mul_bound_mcdiarmid_scale hn ht)
    _ = _ := congr_arg _ (by ring)

/--
Lower-tail concentration of empirical Rademacher complexity around its
expectation.
-/
theorem empiricalRademacherComplexity_lower_tail_countable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hf' : ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω |
      empiricalRademacherComplexity n f (X ∘ ω) -
        rademacherComplexity n f μ X ≤ -ε}).toReal ≤
      (-ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  calc
    _ ≤ (-2 * ε ^ 2 * ((n : ℝ) * t / 2)).exp := by
      simpa only [rademacherComplexity] using
        (mcdiarmid_inequality_neg_iid_of_const
          (μ := μ) (ι := Fin n) (X' := X)
          (f' := fun S : Fin n → 𝒳 ↦ empiricalRademacherComplexity n f S)
          (c := (n : ℝ)⁻¹ * 2 * b) hX
          (empiricalRademacherComplexity_bounded_difference
            (n := n) (f := f) hn hf')
          (measurable_empiricalRademacherComplexity_comp
            (Ω := 𝒳) (Z := 𝒳) (n := n) (f := f) (X := id)
            (fun i ↦ by simpa using hf i))
          hε (by simpa using normalized_two_mul_bound_mcdiarmid_scale hn ht))
    _ = _ := congr_arg _ (by ring)

/-- Optimized empirical-complexity lower tail with `t = 1 / (2 * b^2)`. -/
theorem empiricalRademacherComplexity_lower_tail_countable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω |
      empiricalRademacherComplexity n f (X ∘ ω) -
        rademacherComplexity n f μ X ≤ -ε}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by
    dsimp only [t]
    field_simp)
  calc
    _ ≤ (-ε ^ 2 * t * n).exp :=
      empiricalRademacherComplexity_lower_tail_countable
        (μ := μ) f hf X hX hf' ht hε
    _ = _ := by
      dsimp only [t]
      field_simp

/--
Countable-class tail bound obtained by combining the centered McDiarmid
estimate with `𝔼[UDₙ] ≤ 2 * Rₙ`.
-/
theorem uniform_deviation_tail_bound_countable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω |
      2 * rademacherComplexity n f μ X + ε ≤
        uniformDeviation n f μ X (X ∘ ω)}).toReal ≤
      (-ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  apply measureReal_superlevel_le_of_centered
  · exact uniform_deviation_expectation_le_two_smul_rademacher_complexity
      hn X (fun i ↦ (hf i).comp hX) hb hf'
  · exact uniform_deviation_mcdiarmid_tail (μ := μ) hX hf hf' ht hε

/-- Optimized countable-class tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_countable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω |
      2 * rademacherComplexity n f μ X + ε ≤
        uniformDeviation n f μ X (X ∘ ω)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by
    dsimp only [t]
    field_simp)
  calc
    _ ≤ (-ε ^ 2 * t * n).exp :=
      uniform_deviation_tail_bound_countable
        (μ := μ) f hf X hX hb.le hf' ht hε
    _ = _ := by
      dsimp only [t]
      field_simp

/--
Replace expected Rademacher complexity in the countable-class tail bound by
any deterministic upper bound `C`.
-/
theorem uniform_deviation_tail_bound_countable_of_rademacher_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    (hC : rademacherComplexity n f μ X ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω |
      2 * C + ε ≤ uniformDeviation n f μ X (X ∘ ω)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ ≤ (μⁿ {ω |
        2 * rademacherComplexity n f μ X + ε ≤
          uniformDeviation n f μ X (X ∘ ω)}).toReal := by
      apply measureReal_superlevel_mono
      intro ω
      gcongr
    _ ≤ _ :=
      uniform_deviation_tail_bound_countable_of_pos
        (μ := μ) f hf X hX hb hf' hε

/--
Optimized countable-class tail bound with a uniform fixed-sample upper bound
on empirical Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_countable_of_empirical_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω |
      2 * C + ε ≤ uniformDeviation n f μ X (X ∘ ω)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  apply uniform_deviation_tail_bound_countable_of_rademacher_le
    (μ := μ) f hf X hX hb hf' _ hε
  exact rademacherComplexity_le_of_empirical_le_countable
    (fun i ↦ (hf i).comp hX) hb.le hf' hC

/--
Sample-dependent countable-class tail bound. The threshold contains the
empirical Rademacher complexity of the observed sample. The factor `3` is
obtained by combining two concentration events with a union bound.
-/
theorem uniform_deviation_tail_bound_countable_of_empirical_complexity
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω |
      2 * empiricalRademacherComplexity n f (X ∘ ω) + 3 * ε ≤
        uniformDeviation n f μ X (X ∘ ω)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let A : Set (Fin n → Ω) :=
    {ω | 2 * rademacherComplexity n f μ X + ε ≤
      uniformDeviation n f μ X (X ∘ ω)}
  let B : Set (Fin n → Ω) :=
    {ω | empiricalRademacherComplexity n f (X ∘ ω) -
      rademacherComplexity n f μ X ≤ -ε}
  have hsubset :
      {ω : Fin n → Ω |
        2 * empiricalRademacherComplexity n f (X ∘ ω) + 3 * ε ≤
          uniformDeviation n f μ X (X ∘ ω)} ⊆ A ∪ B := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, A, B]
    by_cases hA :
        2 * rademacherComplexity n f μ X + ε ≤
          uniformDeviation n f μ X (X ∘ ω)
    · exact Or.inl hA
    · right
      simp only [not_le] at hA
      norm_num at hω hA ⊢
      linarith
  calc
    _ ≤ (μⁿ).real (A ∪ B) := measureReal_mono hsubset
    _ ≤ (μⁿ).real A + (μⁿ).real B := measureReal_union_le A B
    _ ≤ (-ε ^ 2 * n / (2 * b ^ 2)).exp +
          (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
      apply add_le_add
      · exact uniform_deviation_tail_bound_countable_of_pos
          (μ := μ) f hf X hX hb hf' hε
      · exact empiricalRademacherComplexity_lower_tail_countable_of_pos
          (μ := μ) f hf X hX hb hf' hε
    _ ≤ 2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
      have h :
          (-ε ^ 2 * n / (2 * b ^ 2)).exp +
              (-ε ^ 2 * n / (2 * b ^ 2)).exp =
            2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
        ring
      exact h.le
  all_goals exact le_rfl

/--
Sample-dependent countable-class tail bound with an arbitrary pointwise upper
bound `C S` on empirical Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_countable_of_sample_empirical_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    (C : (Fin n → 𝒳) → ℝ)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C S)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω |
      2 * C (X ∘ ω) + 3 * ε ≤
        uniformDeviation n f μ X (X ∘ ω)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc
    _ ≤ (μⁿ {ω : Fin n → Ω |
        2 * empiricalRademacherComplexity n f (X ∘ ω) + 3 * ε ≤
          uniformDeviation n f μ X (X ∘ ω)}).toReal := by
      apply measureReal_superlevel_mono
      intro ω
      gcongr
      exact hC (X ∘ ω)
    _ ≤ _ :=
      uniform_deviation_tail_bound_countable_of_empirical_complexity
        (μ := μ) f hf X hX hb hf' hε

end
