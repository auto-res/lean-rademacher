import FoML.Rademacher
import FoML.McDiarmid
import FoML.BoundedDifference
import FoML.SeparableSpaceSup
import FoML.LinearPredictorL2
import FoML.LinearPredictorL1
import FoML.DudleyEntropy

section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}
variable {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/-- The expected empirical uniform deviation is bounded by twice the Rademacher complexity. -/
theorem uniform_deviation_expectation_le_two_smul_rademacher_complexity
    [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • rademacherComplexity n f μ X := by
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
The expected uniform deviation is bounded by twice any uniform fixed-sample
upper bound on empirical Rademacher complexity.
-/
theorem uniform_deviation_expectation_le_of_empirical_le_countable
    [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b C : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • C := by
  have hRC : rademacherComplexity n f μ X ≤ C :=
    rademacherComplexity_le_of_empirical_le_countable hf hb hf' hC
  calc
    _ ≤ 2 • rademacherComplexity n f μ X :=
      uniform_deviation_expectation_le_two_smul_rademacher_complexity
        hn X hf hb hf'
    _ ≤ 2 • C := by
      simpa only [nsmul_eq_mul] using
        mul_le_mul_of_nonneg_left hRC (show (0 : ℝ) ≤ 2 by norm_num)

/-- McDiarmid tail bound for the centered empirical uniform deviation. -/
theorem uniform_deviation_mcdiarmid_tail
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ]
    {X : Ω → 𝒳} (hX : Measurable X)
    (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hb : 0 ≤ b) (hf': ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω) -
      μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≥ ε)).toReal ≤
        (- ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let c : Fin n → ℝ := fun i ↦ (n : ℝ)⁻¹ * 2 * b
  have ht' : (n : ℝ) * t / 2 * ∑ i, (c i) ^ 2 ≤ 1 := by
    apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 1 / 2 from by linarith)
    calc
      _ = t * b ^ 2 := by
        simp only [c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      _ ≤ _ := by linarith
  have hfX : ∀ i, Measurable (f i ∘ X) := fun i => (hf i).comp hX
  calc
    _ ≤ (-2 * ε ^ 2 * (n * t / 2)).exp :=
      mcdiarmid_inequality_pos' hX (uniformDeviation_bounded_difference hn X hfX hb hf')
        (uniformDeviation_measurable X hf) hε ht'
    _ = _ := congr_arg _ (by ring)

/-- (Main Theorem) Countable-class tail bound via symmetrization and McDiarmid's inequality. -/
theorem uniform_deviation_tail_bound_countable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simpa [hn] using measureReal_le_one
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  apply le_trans _ (uniform_deviation_mcdiarmid_tail (μ := μ) hX hf hb hf' ht' hε)
  simp only [ge_iff_le, ne_eq, measure_ne_top, not_false_eq_true, ENNReal.toReal_le_toReal]
  apply measure_mono
  intro ω h
  have : 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω) := h
  have : μⁿ[fun ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • rademacherComplexity n f μ X :=
    uniform_deviation_expectation_le_two_smul_rademacher_complexity hn X (fun i ↦ (hf i).comp hX) hb hf'
  show ε ≤ uniformDeviation n f μ X (X ∘ ω) - μⁿ[fun ω ↦ uniformDeviation n f μ X (X ∘ ω)]
  linarith

/-- (Main Theorem) Optimized countable-class tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_countable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : 0 ≤ t := div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg b))
  have ht' : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by dsimp only [t]; field_simp)
  calc
    _ ≤ (- ε ^ 2 * t * n).exp :=
      uniform_deviation_tail_bound_countable (μ := μ) f hf X hX (le_of_lt hb) hf' ht' hε
    _ = _ := by dsimp only [t]; field_simp

/--
Optimized countable-class tail bound with a deterministic uniform upper bound
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
    (μⁿ (fun ω ↦ 2 • C + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := by
  have hRC : rademacherComplexity n f μ X ≤ C :=
    rademacherComplexity_le_of_empirical_le_countable
      (fun i ↦ (hf i).comp hX) (le_of_lt hb) hf' hC
  apply le_trans _
    (uniform_deviation_tail_bound_countable_of_pos
      (μ := μ) f hf X hX hb hf' hε)
  simp only [ne_eq, measure_ne_top, not_false_eq_true, ENNReal.toReal_le_toReal]
  apply measure_mono
  intro ω hω
  change 2 • C + ε ≤ uniformDeviation n f μ X (X ∘ ω) at hω
  change
    2 • rademacherComplexity n f μ X + ε ≤
      uniformDeviation n f μ X (X ∘ ω)
  simp only [nsmul_eq_mul] at hω ⊢
  have htwo :
      2 * rademacherComplexity n f μ X ≤ 2 * C :=
    mul_le_mul_of_nonneg_left hRC (by norm_num)
  norm_num at hω htwo ⊢
  linarith

open TopologicalSpace

lemma empiricalRademacherComplexity_eq
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    (n : ℕ) {f : ι → (𝒳 → ℝ)} (hf : ∀ x : 𝒳, Continuous fun i ↦ f i x) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n f S = empiricalRademacherComplexity n (f ∘ denseSeq ι) S := by
  dsimp [empiricalRademacherComplexity]
  congr
  ext i
  apply separableSpaceSup_eq_real
  continuity

lemma RademacherComplexity_eq
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    (n : ℕ) (f : ι → (𝒳 → ℝ)) (hf : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity n f μ X = rademacherComplexity n (f ∘ denseSeq ι) μ X := by
  dsimp [rademacherComplexity]
  congr
  ext i
  exact empiricalRademacherComplexity_eq n hf (X ∘ i)

/--
A uniform fixed-sample bound for a separable class lifts to expected
Rademacher complexity through a countable dense subclass.
-/
theorem rademacherComplexity_le_of_empirical_le_separable
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b C : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C) :
    rademacherComplexity n f μ X ≤ C := by
  let f' := f ∘ denseSeq ι
  rw [RademacherComplexity_eq n f hf'' μ X]
  apply rademacherComplexity_le_of_empirical_le_countable
    (f := f') (μ := μ)
  · exact fun i ↦ hf (denseSeq ι i)
  · exact hb
  · exact fun i x ↦ hf' (denseSeq ι i) x
  · intro S
    rw [← empiricalRademacherComplexity_eq n hf'' S]
    exact hC S

lemma uniformDeviation_eq
    [MeasurableSpace 𝒳]
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    (n : ℕ) (f : ι → 𝒳 → ℝ)
    (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    uniformDeviation n f μ X = uniformDeviation n (f ∘ denseSeq ι) μ X := by
  ext y
  dsimp [uniformDeviation]
  apply separableSpaceSup_eq_real
  apply Continuous.abs
  apply Continuous.sub
  · continuity
  · have : ∀ (x : ι), ∀ᵐ (a : Ω) ∂μ, ‖f x (X a)‖ ≤ b := by
      intro i
      filter_upwards with ω
      exact hf' i (X ω)
    apply MeasureTheory.continuous_of_dominated _ this
    · apply MeasureTheory.integrable_const
    · filter_upwards with ω
      continuity
    · intro i
      apply Measurable.aestronglyMeasurable
      measurability

/--
Separable-class version of the expected uniform-deviation bound with a
deterministic uniform upper bound on empirical Rademacher complexity.
-/
theorem uniform_deviation_expectation_le_of_empirical_le_separable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C) :
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • C := by
  let f' := f ∘ denseSeq ι
  calc
    μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f μ X (X ∘ ω)] =
        μⁿ[fun ω : Fin n → Ω ↦ uniformDeviation n f' μ X (X ∘ ω)] := by
      apply integral_congr_ae
      filter_upwards with ω
      exact congrFun (uniformDeviation_eq n f hf X hX hf' hf'' μ) (X ∘ ω)
    _ ≤ 2 • C := by
      apply uniform_deviation_expectation_le_of_empirical_le_countable
        (f := f') (μ := μ) hn X
      · intro i
        exact (hf (denseSeq ι i)).comp hX
      · exact hb
      · exact fun i x ↦ hf' (denseSeq ι i) x
      · intro S
        rw [← empiricalRademacherComplexity_eq n hf'' S]
        exact hC S

/-- (Main Theorem) Separable-class tail bound obtained via reduction to a countable dense subclass. -/
theorem uniform_deviation_tail_bound_separable
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι]  [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * t * n).exp := by
  let f' := f ∘ denseSeq ι
  calc
    _ = (μⁿ (fun ω ↦ 2 • rademacherComplexity n f' μ X + ε ≤ uniformDeviation n f' μ X (X ∘ ω))).toReal := by
      congr
      ext ω
      rw [RademacherComplexity_eq n f hf'' μ X]
      rw [uniformDeviation_eq n f hf X hX hf' hf'' μ]
    _ ≤ (- ε ^ 2 * t * n).exp := by
      apply uniform_deviation_tail_bound_countable f' _ X hX hb _ ht' hε
      · intro i
        measurability
      · exact fun i x ↦ hf' (denseSeq ι i) x

/-- (Main Theorem) Optimized separable-class tail bound with `t = 1 / (2 * b^2)`. -/
theorem uniform_deviation_tail_bound_separable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let t := 1 / (2 * b ^ 2)
  have ht : 0 ≤ t := div_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg b))
  have ht' : t * b ^ 2 ≤ 1 / 2 := le_of_eq (by dsimp only [t]; field_simp)
  calc
    _ ≤ (- ε ^ 2 * t * n).exp :=
      uniform_deviation_tail_bound_separable (μ := μ) f hf X hX (le_of_lt hb) hf' hf'' ht' hε
    _ = _ := by dsimp only [t]; field_simp

/--
Optimized separable-class tail bound with a deterministic uniform upper bound
on empirical Rademacher complexity.
-/
theorem uniform_deviation_tail_bound_separable_of_empirical_le
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f S ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦ 2 • C + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (- ε ^ 2 * n / (2 * b ^ 2)).exp := by
  let f' := f ∘ denseSeq ι
  have hC' : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n f' S ≤ C := by
    intro S
    rw [← empiricalRademacherComplexity_eq n hf'' S]
    exact hC S
  have hRC' : rademacherComplexity n f' μ X ≤ C :=
    rademacherComplexity_le_of_empirical_le_countable
      (fun i ↦ (hf (denseSeq ι i)).comp hX) (le_of_lt hb)
      (fun i x ↦ hf' (denseSeq ι i) x) hC'
  have hRC : rademacherComplexity n f μ X ≤ C := by
    rw [RademacherComplexity_eq n f hf'' μ X]
    exact hRC'
  apply le_trans _
    (uniform_deviation_tail_bound_separable_of_pos
      (μ := μ) f hf X hX hb hf' hf'' hε)
  simp only [ne_eq, measure_ne_top, not_false_eq_true, ENNReal.toReal_le_toReal]
  apply measure_mono
  intro ω hω
  change 2 • C + ε ≤ uniformDeviation n f μ X (X ∘ ω) at hω
  change
    2 • rademacherComplexity n f μ X + ε ≤
      uniformDeviation n f μ X (X ∘ ω)
  simp only [nsmul_eq_mul] at hω ⊢
  have htwo :
      2 * rademacherComplexity n f μ X ≤ 2 * C :=
    mul_le_mul_of_nonneg_left hRC (by norm_num)
  norm_num at hω htwo ⊢
  linarith

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/--
Fixed-sample empirical Rademacher-complexity bound for `ℓ₂` linear
predictors. See the following theorems for expected and tail bounds.
-/
theorem linear_predictor_l2_bound
    [Nonempty ι]
    (d : ℕ)
    (W X : ℝ)
    (hx : 0 ≤ X) (hw : 0 ≤ W)
    (Y' : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (w' : ι → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W):
    empiricalRademacherComplexity
      n (fun (i : ι) a ↦ ⟪((Subtype.val ∘ w') i), a⟫) (Subtype.val ∘ Y') ≤
    X * W / √(n : ℝ) := by
  exact linear_predictor_l2_bound' (d := d) (n := n) (W := W) (X := X) hx hw Y' w'

/--
Fixed-sample empirical Rademacher-complexity bound for `ℓ₁` predictors on
coordinatewise bounded inputs. See the following theorems for expected and
tail bounds.
-/
theorem linear_predictor_l1_bound
    [Nonempty ι]
    (d : ℕ)
    (Xinf W : ℝ)
    (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Y' : Fin n → LinftyBall (d := d) Xinf)
    (w' : ι → L1Ball (d := d) W) :
    empiricalRademacherComplexity n
      (fun i a => (∑ j : Fin d, (w' i).1 j * a j))
      (Subtype.val ∘ Y') ≤
      (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
  exact linear_predictor_l1_bound' (d := d) (n := n) (Xinf := Xinf) (W := W) hX hW d_pos n_pos Y' w'

/--
Expected Rademacher-complexity bound for the full `ℓ₂`-bounded linear class
on an `ℓ₂`-bounded input space.
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
    (f := linearPredictorL2) (X := Z)
  · intro w
    exact (continuous_linearPredictorL2_input w).measurable.comp hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX hW

/--
Expected uniform-deviation bound for the full `ℓ₂`-bounded linear class.
-/
theorem linear_predictor_l2_uniform_deviation_expectation_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) :
    μⁿ[fun ω : Fin n → Ω ↦
      uniformDeviation n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
        μ Z (Z ∘ ω)]
      ≤ 2 • (X * W / Real.sqrt (n : ℝ)) := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr hX).to_subtype
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (f := linearPredictorL2) hn
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le hW w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound d n W X hX hW

/--
High-probability uniform-deviation bound for the full `ℓ₂`-bounded linear class.
-/
theorem linear_predictor_l2_uniform_deviation_tail_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (_hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦
      2 • (X * W / Real.sqrt (n : ℝ)) + ε ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ ω))).toReal
      ≤ (-ε ^ 2 * n / (2 * (X * W) ^ 2)).exp := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr (le_of_lt hW)).to_subtype
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :=
    (Metric.nonempty_closedBall.mpr (le_of_lt hX)).to_subtype
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (f := linearPredictorL2)
  · exact fun w ↦ (continuous_linearPredictorL2_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL2_le (le_of_lt hW) w x
  · exact continuous_linearPredictorL2_weight
  · exact linear_predictor_l2_empirical_bound
      d n W X (le_of_lt hX) (le_of_lt hW)
  · exact hε

/--
Expected Rademacher-complexity bound for the full `ℓ₁`-bounded linear class
on a coordinatewise bounded input space.
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
    (f := linearPredictorL1) (X := Z)
  · intro w
    exact (continuous_linearPredictorL1_input w).measurable.comp hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le hX w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W hX hW d_pos n_pos

/--
Expected uniform-deviation bound for the full `ℓ₁`-bounded linear class.
-/
theorem linear_predictor_l1_uniform_deviation_expectation_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 ≤ Xinf) (hW : 0 ≤ W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z) :
    μⁿ[fun ω : Fin n → Ω ↦
      uniformDeviation n
        (linearPredictorL1 :
          L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
        μ Z (Z ∘ ω)]
      ≤ 2 • ((Xinf * W / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * d))) := by
  letI : Nonempty (L1Ball (d := d) W) := nonempty_L1Ball hW
  letI : Nonempty (LinftyBall (d := d) Xinf) := nonempty_LinftyBall hX
  apply uniform_deviation_expectation_le_of_empirical_le_separable
    (f := linearPredictorL1) n_pos
  · exact fun w ↦ (continuous_linearPredictorL1_input w).measurable
  · exact hZ
  · exact mul_nonneg hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le hX w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W hX hW d_pos n_pos

/--
High-probability uniform-deviation bound for the full `ℓ₁`-bounded linear class.
-/
theorem linear_predictor_l1_uniform_deviation_tail_bound
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 < Xinf) (hW : 0 < W)
    (d_pos : 0 < d) (n_pos : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦
      2 • ((Xinf * W / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * d))) + ε ≤
        uniformDeviation n
          (linearPredictorL1 :
            L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
          μ Z (Z ∘ ω))).toReal
      ≤ (-ε ^ 2 * n / (2 * (Xinf * W) ^ 2)).exp := by
  letI : Nonempty (L1Ball (d := d) W) :=
    nonempty_L1Ball (le_of_lt hW)
  letI : Nonempty (LinftyBall (d := d) Xinf) :=
    nonempty_LinftyBall (le_of_lt hX)
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (f := linearPredictorL1)
  · exact fun w ↦ (continuous_linearPredictorL1_input w).measurable
  · exact hZ
  · exact mul_pos hX hW
  · exact fun w x ↦ abs_linearPredictorL1_le (le_of_lt hX) w x
  · exact continuous_linearPredictorL1_weight
  · exact linear_predictor_l1_empirical_bound
      d n Xinf W (le_of_lt hX) (le_of_lt hW) d_pos n_pos
  · exact hε

/--
Dudley entropy-integral upper bound for the one-sided empirical Rademacher
complexity of a fixed sample.
-/
theorem dudley_entropy_integral_bound
  {𝒳 : Type v} {n : ℕ} {ι : Type u} [Nonempty ι] {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
  (ε_pos : 0 < ε) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (m_pos : 0 < n) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
  (ε_le_c_div_2 : ε < c/2) :
    empiricalRademacherComplexity_without_abs n F S ≤
    (4 * ε + (12 / Real.sqrt n) *
    (∫ (x : ℝ) in ε..(c/2),√(Real.log (coveringNumber h' x)))) := by
  exact dudley_entropy_integral' ε_pos h' m_pos cs ε_le_c_div_2

/--
Dudley entropy-integral upper bound for the absolute empirical Rademacher
complexity of a fixed sample. The entropy is that of the class enlarged by
its pointwise negatives.
-/
theorem dudley_entropy_integral_bound_abs
    {𝒳 : Type v} {n : ℕ} {ι : Type u} [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
    (ε_pos : 0 < ε)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (n_pos : 0 < n) (cs : ∀ i : ι, empiricalNorm S (F i) ≤ c)
    (ε_lt_c_div_2 : ε < c / 2) :
    empiricalRademacherComplexity n F S ≤
      4 * ε + (12 / Real.sqrt n) *
        (∫ (x : ℝ) in ε..(c / 2),
          √(Real.log (coveringNumber
            (signSymmetrization_totallyBounded (F := F) (S := S) h') x))) := by
  exact dudley_entropy_integral_abs ε_pos h' n_pos cs ε_lt_c_div_2

/--
For a class closed under pointwise negation, Dudley's entropy integral for
the original class bounds its absolute empirical Rademacher complexity.
-/
theorem dudley_entropy_integral_bound_abs_of_neg_closed
    {𝒳 : Type v} {n : ℕ} {ι : Type u} [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
    (ε_pos : 0 < ε)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (n_pos : 0 < n) (cs : ∀ i : ι, empiricalNorm S (F i) ≤ c)
    (ε_lt_c_div_2 : ε < c / 2) (hneg : IsNegClosed F) :
    empiricalRademacherComplexity n F S ≤
      4 * ε + (12 / Real.sqrt n) *
        (∫ (x : ℝ) in ε..(c / 2),
          √(Real.log (coveringNumber h' x))) := by
  exact dudley_entropy_integral_abs_of_neg_closed
    ε_pos h' n_pos cs ε_lt_c_div_2 hneg

/--
A sample-uniform Dudley entropy estimate bounds expected Rademacher
complexity for a separable class.
-/
theorem rademacher_complexity_le_dudley_of_uniform_entropy
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b c α C : ℝ} (hb : 0 ≤ b) (hf_bound : ∀ i x, |f i x| ≤ b)
    (hf_cont : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (n_pos : 0 < n) (α_pos : 0 < α) (α_lt_c_div_2 : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace f S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (i : ι), empiricalNorm S (f i) ≤ c)
    (hentropy : ∀ S : Fin n → 𝒳,
      4 * α + (12 / Real.sqrt n) *
          (∫ (x : ℝ) in α..(c / 2),
            √(Real.log (coveringNumber
              (signSymmetrization_totallyBounded
                (F := f) (S := S) (htb S)) x)))
        ≤ C) :
    rademacherComplexity n f μ X ≤ C := by
  apply rademacherComplexity_le_of_empirical_le_separable
    f X hf hb hf_bound hf_cont
  intro S
  exact (dudley_entropy_integral_bound_abs
    α_pos (htb S) n_pos (hnorm S) α_lt_c_div_2).trans (hentropy S)

/--
A sample-uniform Dudley entropy estimate gives a deterministic-threshold
high-probability uniform-deviation bound for a separable class.
-/
theorem uniform_deviation_tail_bound_separable_of_uniform_dudley
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α C : ℝ} (hb : 0 < b) (hf_bound : ∀ i x, |f i x| ≤ b)
    (hf_cont : ∀ x : 𝒳, Continuous fun i ↦ f i x)
    (n_pos : 0 < n) (α_pos : 0 < α) (α_lt_c_div_2 : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace f S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (i : ι), empiricalNorm S (f i) ≤ c)
    (hentropy : ∀ S : Fin n → 𝒳,
      4 * α + (12 / Real.sqrt n) *
          (∫ (x : ℝ) in α..(c / 2),
            √(Real.log (coveringNumber
              (signSymmetrization_totallyBounded
                (F := f) (S := S) (htb S)) x)))
        ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ (fun ω ↦
      2 • C + ε ≤ uniformDeviation n f μ X (X ∘ ω))).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (f := f) hf X hX hb hf_bound hf_cont
  · intro S
    exact (dudley_entropy_integral_bound_abs
      α_pos (htb S) n_pos (hnorm S) α_lt_c_div_2).trans (hentropy S)
  · exact hε

end
