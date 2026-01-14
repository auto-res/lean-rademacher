import FoML.Rademacher
import FoML.McDiarmid
import FoML.BoundedDifference
import FoML.SeparableSpaceSup
import FoML.LinearPredictorL2
import FoML.DudleyEntropy

section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}
variable {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

theorem le_two_smul_rademacher [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
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

theorem uniformDeviation_mcdiarmid
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

theorem main_countable [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
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
  apply le_trans _ (uniformDeviation_mcdiarmid (μ := μ) hX hf hb hf' ht' hε)
  simp only [ge_iff_le, ne_eq, measure_ne_top, not_false_eq_true, ENNReal.toReal_le_toReal]
  apply measure_mono
  intro ω h
  have : 2 • rademacherComplexity n f μ X + ε ≤ uniformDeviation n f μ X (X ∘ ω) := h
  have : μⁿ[fun ω ↦ uniformDeviation n f μ X (X ∘ ω)] ≤ 2 • rademacherComplexity n f μ X :=
    le_two_smul_rademacher hn X (fun i ↦ (hf i).comp hX) hb hf'
  show ε ≤ uniformDeviation n f μ X (X ∘ ω) - μⁿ[fun ω ↦ uniformDeviation n f μ X (X ∘ ω)]
  linarith

theorem main' [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] [IsProbabilityMeasure μ]
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
    _ ≤ (- ε ^ 2 * t * n).exp := main_countable (μ := μ) f hf X hX (le_of_lt hb) hf' ht' hε
    _ = _ := by dsimp only [t]; field_simp

open TopologicalSpace

lemma empiricalRademacherComplexity_eq
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    (n : ℕ) {f : ι → (𝒳 → ℝ)} (hf : ∀ x : 𝒳, Continuous fun i ↦ f i x) (x : Fin n → 𝒳) :
    empiricalRademacherComplexity n f x = empiricalRademacherComplexity n (f ∘ denseSeq ι) x := by
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

theorem main_separable [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
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
      apply main_countable f' _ X hX hb _ ht' hε
      · intro i
        measurability
      · exact fun i x ↦ hf' (denseSeq ι i) x

theorem separableSpace_main' [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
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
    _ ≤ (- ε ^ 2 * t * n).exp := main_separable (μ := μ) f hf X hX (le_of_lt hb) hf' hf'' ht' hε
    _ = _ := by dsimp only [t]; field_simp

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

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

theorem dudley_entropy_integral
  {Z : Type v} {m : ℕ} {ι : Type u} [Nonempty ι] {F : ι → Z → ℝ} {S : Fin m → Z} {c ε : ℝ}
  (ε_pos : 0 < ε) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
  (ε_le_c_div_2 : ε < c/2) :
    empiricalRademacherComplexity_without_abs m F S ≤
    (4 * ε + (12 / Real.sqrt m) *
    (∫ (x : ℝ) in ε..(c/2),√(Real.log (coveringNumber h' x)))) := by
  exact dudley_entropy_integral' ε_pos h' m_pos cs ε_le_c_div_2

end
