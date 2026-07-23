import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Notation
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.MeasureTheory.Order.Group.Lattice
import FoML.Symmetrization
import FoML.MeasurePiLemmas
import FoML.RademacherVariableProperty

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

universe u v w

/- `n`-variable version -/

section

variable {Ω : Type u} [MeasurableSpace Ω] {Z : Type w}
variable {n : ℕ} {ι : Type*} {f : ι → Z → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ciSup_add_le_add_ciSup' {ι : Type*} [Nonempty ι] {g : ι → ℝ} {h : ι → ℝ}
    (hg : BddAbove (Set.range g))
    (hh : BddAbove (Set.range h)) :
    ⨆ i, g i + h i ≤ ⨆ i, ⨆ j, g i + h j := by
  apply ciSup_mono
  · conv in fun i ↦ _ =>
      ext i
      rw [← add_ciSup hh]
    apply BddAbove.range_add hg
    simp
  · intro i
    rw [← add_ciSup hh]
    simp only [add_le_add_iff_left]
    exact le_ciSup hh i

lemma ciSup_add_le_add_ciSup {ι : Type*} [Nonempty ι] {g : ι → ℝ} {h : ι → ℝ}
    (hg : BddAbove (Set.range g))
    (hh : BddAbove (Set.range h)) :
    ⨆ i, g i + h i ≤ (⨆ i, g i) + ⨆ i, h i := by
  convert ciSup_add_le_add_ciSup' hg hh
  rw [ciSup_add hg]
  congr
  ext i
  apply add_ciSup hh

omit [MeasurableSpace Ω] in
theorem abs_signed_sum_le_card_mul_bound [Nonempty ι] {X : Ω → Z}
  {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b)
  (i : ι) (ω : Fin n → Ω) (σ : Signs n) :
    |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))| ≤ ↑n * b := by
  calc
  _ ≤ ∑ k : Fin n, (|↑↑(σ k) * f i (X (ω k))|) := Finset.univ.abs_sum_le_sum_abs (fun k ↦ ↑↑(σ k) * f i (X (ω k)))
  _ = ∑ k : Fin n, |f i (X (ω k))| := by congr; ext k; simp only [Int.reduceNeg, abs_mul,
    Signs.apply_abs', one_mul]
  _ ≤ ∑ k : Fin n, b := Finset.sum_le_sum fun k _ ↦ hf' i (X (ω k))
  _ ≤ _ := by simp

omit [MeasurableSpace Ω] in
theorem bddAbove_range_abs_signed_sum [Nonempty ι] {X : Ω → Z}
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b)
    (ω : Fin n → Ω) (σ : Signs n) :
      BddAbove (Set.range fun i ↦ |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))|) := by
  rw [bddAbove_def]
  exists n * b
  intro y hy
  simp only [Int.reduceNeg, Set.mem_range] at hy
  have ⟨i, hi⟩ := hy
  rw [← hi]
  apply abs_signed_sum_le_card_mul_bound hf'

omit [MeasurableSpace Ω] in
lemma symmetrization_signed_sup_le_add
  [Nonempty ι] {X : Ω → Z} {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
  (fun ω : Fin n → Ω × Ω ↦
      (↑(Fintype.card (Signs n)))⁻¹ *
        ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * (f i (X (ω k).1) - f i (X (ω k).2))|) ≤
    fun ω ↦
    ((↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).1)|) +
      (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).2)| := by
  intro ω
  dsimp
  rw [←mul_add]
  apply mul_le_mul_of_nonneg_left
  . rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro σ _
    calc
       _ ≤ ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).1)|
          + |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).2)| := by
        apply ciSup_mono
        · refine BddAbove.range_add ?B.hf ?B.hg
          rw [bddAbove_def]
          use n * b
          intro y hy
          simp only [Int.reduceNeg, Set.mem_range] at hy
          obtain ⟨y_1, hy'⟩ := hy
          rw [<- hy']
          · apply abs_signed_sum_le_card_mul_bound hf'
          · rw [bddAbove_def]
            use n * b
            intro y hy
            simp only [Int.reduceNeg, Set.mem_range] at hy
            obtain ⟨i, hi⟩ := hy
            rw [← hi]
            apply abs_signed_sum_le_card_mul_bound hf'
        intro i
        convert abs_sub _ _
        rw [←Finset.sum_sub_distrib]
        congr
        ext k
        exact mul_sub_left_distrib ((σ k : ℝ)) (f i (X (ω k).1)) (f i (X (ω k).2))
        exact instIsOrderedAddMonoid
       _ ≤ _ := by
        apply ciSup_add_le_add_ciSup
        · apply bddAbove_range_abs_signed_sum hf'
        · apply bddAbove_range_abs_signed_sum hf'
  · apply inv_nonneg_of_nonneg
    exact Nat.cast_nonneg' (Fintype.card (Signs n))

theorem iSup_integral_toReal_le_integral_iSup_toReal {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {ι : Sort*} [Countable ι] (f : ι → α → ℝ≥0∞)
    (hfm : ∀ i, Measurable (f i)) {b : ℝ≥0∞} (hb : b ≠ ⊤) (hf : ∀ i, ∀ x, f i x ≤ b) :
    ⨆ i, ∫ a, (f i a).toReal ∂μ ≤ ∫ a, ⨆ i, (f i a).toReal ∂μ := by
  have hf_le : ∀ i, ∀ x, f i x < ⊤ := by
    intro i x
    calc
      _ ≤ b := hf i x
      _ < ⊤ := Ne.lt_top hb
  have hfle : ∀ i, ∀ᵐ (x : α) ∂μ, f i x < ⊤ := by
    intro i
    filter_upwards with x
    exact lt_top_of_lt (hf_le i x)
  have hfne : ∀ᵐ (x : α) ∂μ, ∀ i, f i x ≠ ⊤ := by
    filter_upwards with x i using LT.lt.ne_top (hf_le i x)
  have hb' : b * μ Set.univ < ⊤ := ENNReal.mul_lt_top (Ne.lt_top hb) (measure_lt_top μ Set.univ)
  have hf_nebot : ⨆ i, ∫⁻ (a : α), f i a ∂μ ≠ ⊤ := by
    rw [← lt_top_iff_ne_top]
    rw [iSup_lt_iff]
    refine ⟨b * μ Set.univ, hb', fun i ↦ ?_⟩
    calc
      _ ≤ ∫⁻ (a : α), b ∂μ := lintegral_mono fun a ↦ hf i a
      _ ≤ _ := by
        simp only [lintegral_const]
        apply le_refl
  have hf' : ∫⁻ (a : α), ⨆ i, f i a ∂μ ≠ ⊤ := by
    rw [← lt_top_iff_ne_top]
    calc
      _ ≤ ∫⁻ (a : α), b ∂μ := by
        apply lintegral_mono
        intro a
        simp only [iSup_le_iff]
        intro i
        exact hf i a
      _ ≤ b * μ Set.univ := by
        simp only [lintegral_const]
        apply le_refl
      _ < ⊤ := hb'
  have hf'' : ∀ (i : ι), ∫⁻ (a : α), f i a ∂μ ≠ ⊤ := by
    intro i
    suffices ∫⁻ (a : α), f i a ∂μ ≤ ∫⁻ (a : α), ⨆ i, f i a ∂μ from
      ne_top_of_le_ne_top hf' this
    apply lintegral_mono
    intro x
    exact le_iSup_iff.mpr fun b hb ↦ hb i
  have hfle' : ∀ᵐ (x : α) ∂μ, ⨆ i, f i x < ⊤ := by
    filter_upwards with x
    rw [iSup_lt_iff]
    exact ⟨b, Ne.lt_top hb, fun i ↦ hf i x⟩
  conv =>
    lhs
    congr
    ext i
    rw [MeasureTheory.integral_toReal (hfm i).aemeasurable (hfle i)]
  rw [← ENNReal.toReal_iSup hf'']
  have : ∫ (a : α), ⨆ i, (f i a).toReal ∂μ = ∫ (ω : α), (⨆ i, f i ω).toReal ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hfne] with ω hω using (ENNReal.toReal_iSup hω).symm
  rw [this]
  rw [MeasureTheory.integral_toReal (Measurable.iSup hfm).aemeasurable hfle']
  rw [ENNReal.toReal_le_toReal hf_nebot hf']
  apply iSup_lintegral_le

-- TODO: add appropriate integrability assumptions for `f`
theorem iSup_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {ι : Sort*} [Countable ι]
    (f : ι → α → ℝ)
    (hf : ∀ (i : ι), Measurable fun a ↦ f i a)
    {b : ℝ}
    (hf' : ∀ i, ∀ x, |f i x| ≤ b) :
    ⨆ i, ∫ a, |(f i a)| ∂μ ≤ ∫ a, ⨆ i, |(f i a)| ∂μ := by
  conv =>
    lhs
    congr
    ext i
    conv in fun ω ↦ |f i ω| =>
      ext ω
      rw [← ENNReal.toReal_ofReal (abs_nonneg (f i ω))]
  conv in fun ω ↦ ⨆ i, |f i ω| =>
    ext ω
    congr
    ext i
    rw [← ENNReal.toReal_ofReal (abs_nonneg (f i ω))]
  apply iSup_integral_toReal_le_integral_iSup_toReal μ (fun i a ↦ .ofReal |f i a|)
    (fun i ↦ (hf i).norm.ennreal_ofReal)
    (ENNReal.ofReal_ne_top : .ofReal (b + 1) ≠ ⊤)
    (fun i x ↦ ENNReal.ofReal_le_ofReal (le_of_lt ?_))
  have hf' := hf' i x
  linarith

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

theorem measurable_eval_comp {X : Ω → Z}
    (hf : ∀ (i : ι), Measurable (f i ∘ X)) (i : ι) (k : Fin n) :
    Measurable (fun ω : Fin n → Ω ↦ f i (X (ω k))) :=
  (hf i).comp (measurable_pi_apply k)

theorem integrable_eval_comp {X : Ω → Z}
    (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (i : ι) (k : Fin n) :
    Integrable (fun ω ↦ f i (X (ω k))) μⁿ := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_eval_comp hf i k).aestronglyMeasurable b
  filter_upwards with ω
  simp only [norm_eq_abs]
  exact hf' i (X (ω k))

theorem measurable_sum_sub_right {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    (i : ι) (ω : Fin n → Ω) :
    Measurable fun ω' : Fin n → Ω ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k))) := by
  apply Finset.univ.measurable_sum
  intro k _
  apply ((hf i).comp measurable_const).sub ((hf i).comp (measurable_pi_apply k))

theorem measurable_signed_sup_sum_fst_core [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable (fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|) := by
  apply Finset.univ.measurable_sum
  intro σ _
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply measurable_const.mul
  apply (hf i).comp measurable_fst.eval

theorem measurable_signed_sup_sum_fst [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable (fun ω : (Fin n → Ω) × (Fin n → Ω) ↦
      (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|) := by
  apply measurable_const.mul
  apply measurable_signed_sup_sum_fst_core hf

omit [MeasurableSpace Ω] in
theorem sum_abs_le_card_mul_bound {X : Ω → Z}
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (i : ι) (ω : Fin n → Ω) :
    ∑ k : Fin n, |f i (X (ω k))| ≤ ↑n * b := by
  suffices  ∑ k : Fin n, |f i (X (ω k))| ≤ ∑ k : Fin n, b from by
    apply le_trans this _
    apply le_of_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact Finset.sum_le_sum fun k _ ↦ hf' i (X (ω k))

omit [MeasurableSpace Ω] in
theorem sum_abs_signed_le_card_mul_bound (X : Ω → Z)
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (σ : Signs n) (i : ι) (ω : Fin n → Ω) :
    ∑ k : Fin n, |↑↑(σ k) * f i (X (ω k))| ≤ ↑n * b := by
  conv =>
    congr
    · congr
      · skip
      · ext σ
        rw [abs_mul]
        simp
  apply sum_abs_le_card_mul_bound hf'

omit [MeasurableSpace Ω] in
theorem abs_sum_signed_le_card_mul_bound {X : Ω → Z}
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (σ : Signs n) (i : ι) (ω : Fin n → Ω) :
    |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))| ≤ ↑n * b := by
  apply le_trans _ (sum_abs_signed_le_card_mul_bound X hf' σ i ω)
  apply Finset.abs_sum_le_sum_abs

omit [MeasurableSpace Ω] in
theorem bddAbove_range_sum_abs_signed {X : Ω → Z}
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (σ : Signs n) (ω : Fin n → Ω) :
    BddAbove (Set.range fun i ↦ ∑ k : Fin n, |↑↑(σ k) * f i (X (ω k))|) := by
  rw [bddAbove_def]
  exists n * b
  intro y hy
  simp only [Int.reduceNeg, Set.mem_range] at hy
  have ⟨i, hi⟩ := hy
  rw [← hi]
  apply sum_abs_signed_le_card_mul_bound X hf'

omit [MeasurableSpace Ω] in
theorem bddAbove_range_abs_sum_signed {X : Ω → Z}
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (σ : Signs n) (ω : Fin n → Ω) :
    BddAbove (Set.range fun i ↦ |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))|) := by
  rw [bddAbove_def]
  exists n * b
  intro y hy
  simp only [Int.reduceNeg, Set.mem_range] at hy
  have ⟨i, hi⟩ := hy
  rw [← hi]
  apply abs_sum_signed_le_card_mul_bound hf'

omit [MeasurableSpace Ω] in
theorem abs_sum_sup_signed_le_pow_mul_bound {X : Ω → Z}
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (ω : Fin n → Ω) :
    |(∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))|)| ≤ (2 : ℝ) ^ n * (n * b) := by
  calc
    _ ≤ ∑ σ : Signs n, |⨆ i, (|∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))|)| := by
      apply Finset.abs_sum_le_sum_abs
    _ ≤ ∑ σ : Signs n, ⨆ i, |(|∑ k : Fin n, ↑↑(σ k) * f i (X (ω k))|)| := by
      apply Finset.sum_le_sum
      intro σ _
      simp only [Int.reduceNeg, abs_abs]
      apply Eq.le
      simp only [Int.reduceNeg, abs_eq_self]
      by_cases h : Nonempty ι
      · apply le_ciSup_of_le _ (Classical.choice h)
        · simp
        · apply bddAbove_range_abs_sum_signed hf' σ ω
      · simp only [not_nonempty_iff] at h
        simp
    _ ≤ ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, |↑↑(σ k) * f i (X (ω k))| := by
      apply Finset.sum_le_sum
      intro σ _
      apply ciSup_mono
      · apply bddAbove_range_sum_abs_signed hf'
      · intro i
        simp only [Int.reduceNeg, abs_abs]
        apply Finset.abs_sum_le_sum_abs
    _ ≤ _ := by
      conv in fun σ : Signs n ↦ _ =>
        ext σ
        conv in fun i ↦ _ =>
          ext i
          conv in fun k ↦ _ =>
            ext k
            rw [abs_mul]
            simp
      simp only [Finset.sum_const, Finset.card_univ, Signs.card, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.ofNat_pos, pow_pos, mul_le_mul_iff_right₀]
      by_cases h : Nonempty ι
      · apply ciSup_le
        intro i
        suffices  ∑ k : Fin n, |f i (X (ω k))| ≤ ∑ k : Fin n, b from by
          apply le_trans this _
          apply le_of_eq
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Finset.sum_le_sum fun k _ ↦ hf' i (X (ω k))
      · simp only [not_nonempty_iff] at h
        simp only [iSup_of_isEmpty]
        exact mul_nonneg (Nat.cast_nonneg n) hb

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- A uniformly bounded class has empirical Rademacher complexity at most the same bound. -/
theorem empiricalRademacherComplexity_le_of_bounded
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b)
    (S : Fin n → Z) :
    empiricalRademacherComplexity n f S ≤ b := by
  by_cases hn : n = 0
  · subst n
    simpa [empiricalRademacherComplexity] using hb
  dsimp [empiricalRademacherComplexity]
  calc
    (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)|
        ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ _σ : Signs n, b := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro σ _
            apply Real.iSup_le
            · intro i
              rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
              calc
                (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * f i (S k)|
                    ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, |(σ k : ℝ) * f i (S k)| := by
                      gcongr
                      exact Finset.abs_sum_le_sum_abs
                        (fun k : Fin n ↦ (σ k : ℝ) * f i (S k)) Finset.univ
                _ = (n : ℝ)⁻¹ * ∑ k : Fin n, |f i (S k)| := by
                      congr 1
                      apply Finset.sum_congr rfl
                      intro k _
                      rw [abs_mul, abs_sigma, one_mul]
                _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b := by
                      gcongr with k
                      exact hf' i (S k)
                _ = b := by
                      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                        nsmul_eq_mul]
                      field_simp
            · exact hb
          · positivity
    _ = b := by
      simp [Signs.card]

/-- Measurability of empirical Rademacher complexity evaluated on a random sample. -/
theorem measurable_empiricalRademacherComplexity_comp
    [Countable ι] {X : Ω → Z} (hf : ∀ i, Measurable (f i ∘ X)) :
    Measurable fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω) := by
  dsimp only [empiricalRademacherComplexity]
  apply Measurable.const_mul
  apply Finset.univ.measurable_sum
  intro σ _
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Measurable.const_mul
  apply Finset.univ.measurable_sum
  intro k _
  apply measurable_const.mul
  simpa only [Function.comp_apply] using (hf i).comp (measurable_pi_apply k)

/-- Integrability of empirical Rademacher complexity for a measurable uniformly bounded class. -/
theorem integrable_empiricalRademacherComplexity_comp
    [Countable ι] {X : Ω → Z} (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω)) μⁿ := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_empiricalRademacherComplexity_comp hf).aestronglyMeasurable b
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (empiricalRademacherComplexity_nonneg n f (X ∘ ω))]
  exact empiricalRademacherComplexity_le_of_bounded hb hf' (X ∘ ω)

/-- An almost-everywhere empirical bound lifts to expected Rademacher complexity. -/
theorem rademacherComplexity_le_of_ae_empirical_le
    {X : Ω → Z} {C : ℝ}
    (hint :
      Integrable (fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω)) μⁿ)
    (hC : ∀ᵐ ω : Fin n → Ω ∂μⁿ, empiricalRademacherComplexity n f (X ∘ ω) ≤ C) :
    rademacherComplexity n f μ X ≤ C := by
  rw [rademacherComplexity]
  calc
    μⁿ[fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω)]
        ≤ μⁿ[fun _ω : Fin n → Ω ↦ C] :=
      integral_mono_ae
        (μ := μⁿ)
        (f := fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω))
        (g := fun _ω : Fin n → Ω ↦ C)
        hint (integrable_const C) hC
    _ = C := by simp

/-- A bound valid for every fixed sample lifts to expected Rademacher complexity. -/
theorem rademacherComplexity_le_of_empirical_le
    {X : Ω → Z} {C : ℝ}
    (hint :
      Integrable (fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω)) μⁿ)
    (hC : ∀ S : Fin n → Z, empiricalRademacherComplexity n f S ≤ C) :
    rademacherComplexity n f μ X ≤ C :=
  rademacherComplexity_le_of_ae_empirical_le hint
    (Filter.Eventually.of_forall fun ω ↦ hC (X ∘ ω))

/-- Countable measurable uniformly bounded classes need no separate integrability hypothesis. -/
theorem rademacherComplexity_le_of_empirical_le_countable
    [Countable ι] {X : Ω → Z} (hf : ∀ i, Measurable (f i ∘ X))
    {b C : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b)
    (hC : ∀ S : Fin n → Z, empiricalRademacherComplexity n f S ≤ C) :
    rademacherComplexity n f μ X ≤ C :=
  rademacherComplexity_le_of_empirical_le
    (integrable_empiricalRademacherComplexity_comp hf hb hf') hC

theorem integrable_signed_sup_sum_fst [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω : (Fin n → Ω) × (Fin n → Ω) ↦
      (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|)
    (μⁿ.prod μⁿ) := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_signed_sup_sum_fst hf).aestronglyMeasurable (n * b)
  filter_upwards with ω
  simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, norm_mul, norm_inv, norm_pow,
    norm_ofNat, norm_eq_abs]
  rw [inv_mul_le_iff₀' (by simp)]
  apply le_trans (abs_sum_sup_signed_le_pow_mul_bound hb hf' _)
  apply le_of_eq
  ring

theorem measurable_sup_abs_integral_sum_sub
    {X : Ω → Z} [inst_3 : Countable ι] (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable fun ω : Fin n → Ω ↦ ⨆ i, |∫ (x : Fin n → Ω), ∑ k : Fin n, (f i (X (ω k)) - f i (X (x k))) ∂μⁿ| := by
  apply Measurable.iSup
  intro i
  refine Measurable.max ?hf.left.hf.hf.hf ?hf.left.hf.hf.hg
  apply MeasureTheory.StronglyMeasurable.measurable
  apply MeasureTheory.StronglyMeasurable.integral_prod_left
  apply Measurable.stronglyMeasurable
  dsimp [Function.uncurry_def]
  refine Finset.measurable_sum Finset.univ ?hf.left.hf.hf.hf.hf.hf.hf.hf
  intro i' hi
  apply Measurable.sub
  apply (hf i).comp
  refine Measurable.eval ?hf.left.hf.hf.hf.hf.hf.hf.hf.hf.hg
  exact measurable_snd
  apply (hf i).comp
  refine Measurable.eval ?hf.left.hf.hf.hf.hf.hf.hf.hf.hf.hg.hg
  exact measurable_fst
  apply Measurable.neg
  apply MeasureTheory.StronglyMeasurable.measurable
  apply MeasureTheory.StronglyMeasurable.integral_prod_left
  apply Measurable.stronglyMeasurable
  dsimp [Function.uncurry_def]
  apply Finset.measurable_sum Finset.univ
  intro i' hi
  apply Measurable.sub
  apply (hf i).comp measurable_snd.eval
  apply (hf i).comp measurable_fst.eval

theorem measurable_pi_sum [AddCommMonoid Z] [MeasurableSpace Z][MeasurableAdd₂ Z]
    {X : Ω → Z} (hX : Measurable X) (s : Finset ι) :
    Measurable fun ω : ι → Ω ↦ ∑ k ∈ s, X (ω k) := by
  apply s.measurable_sum
  intro k _
  apply hX.comp (measurable_pi_apply k)

theorem measurable_signed_sup_sum_sub [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable
    (fun ω : Fin n → (Ω × Ω) ↦
      (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))|) := by
  apply Measurable.mul measurable_const
  apply Finset.univ.measurable_sum
  intro σ _
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply measurable_const.mul
  apply Measurable.sub
  · apply (hf i).comp (measurable_pi_apply k).fst
  · apply (hf i).comp (measurable_pi_apply k).snd

omit [MeasurableSpace Ω] in
theorem bddAbove_range_sum_abs_add_abs [Countable ι] (X : Ω → Z)
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (ω : Fin n → (Ω × Ω)) :
    BddAbove (Set.range fun i ↦ ∑ k : Fin n, (|f i (X (ω k).1)| + |f i (X (ω k).2)|)) := by
  rw [bddAbove_def]
  exists (n * (b + b))
  intro y hy
  simp only [Set.mem_range] at hy
  have ⟨i, hi⟩ := hy
  rw [← hi]
  simp only [ge_iff_le]
  calc
    _ ≤ ∑ k : Fin n, (b + b) := by
      apply Finset.sum_le_sum
      intro k _
      exact add_le_add (hf' i (X (ω k).1)) (hf' i (X (ω k).2))
    _ ≤ (↑n * (b + b)) := by
      apply le_of_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul]
      ring

omit [MeasurableSpace Ω] in
theorem bddAbove_range_sum_abs_signed_sub [Countable ι] (X : Ω → Z)
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (ω : Fin n → (Ω × Ω)) (σ : Signs n) :
    BddAbove (Set.range fun i ↦ ∑ k : Fin n, |↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))|) := by
  rw [bddAbove_def]
  exists (n * (b + b))
  intro y hy
  simp only [Int.reduceNeg, Set.mem_range] at hy
  have ⟨i, hi⟩ := hy
  rw [← hi]
  simp only [Int.reduceNeg, ge_iff_le]
  calc
    _ = ∑ k : Fin n, |(f i (X (ω k).1) - f i (X (ω k).2))| := by
      congr
      ext k
      simp only [Int.reduceNeg, abs_mul, Signs.apply_abs', one_mul]
    _ ≤ ∑ k : Fin n, (|f i (X (ω k).1)| + |f i (X (ω k).2)|) := by
      apply Finset.sum_le_sum
      intro k _
      exact abs_sub (f i (X (ω k).1)) (f i (X (ω k).2))
    _ ≤ ∑ k : Fin n, (b + b) := by
      apply Finset.sum_le_sum
      intro k _
      exact add_le_add (hf' i (X (ω k).1)) (hf' i (X (ω k).2))
    _ ≤ (↑n * (b + b)) := by
      apply le_of_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul]
      ring

omit [MeasurableSpace Ω] in
theorem bddAbove_range_abs_sum_signed_sub [Countable ι] {X : Ω → Z}
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (ω : Fin n → (Ω × Ω)) (σ : Signs n) :
    BddAbove (Set.range fun i ↦ |∑ k : Fin n, ↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))|) := by
  have := bddAbove_range_sum_abs_signed_sub X hf' ω σ
  rw [bddAbove_def] at this
  have ⟨z, hz⟩ := this
  rw [bddAbove_def]
  exists z
  intro y hy
  simp only [Int.reduceNeg, Set.mem_range] at hy
  have ⟨i, hi⟩ := hy
  rw [← hi]
  simp only [Int.reduceNeg, ge_iff_le]
  calc
    _ ≤ ∑ k : Fin n, |↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))| := by
      apply Finset.abs_sum_le_sum_abs
    _ ≤ z := by
      apply hz
      simp

theorem integrable_signed_sup_sum_sub [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable
    (fun ω : Fin n → (Ω × Ω) ↦
      (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))|)
      (Measure.pi fun _ ↦ μ.prod μ) := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_signed_sup_sum_sub hf).aestronglyMeasurable (n * (b + b))
  filter_upwards with ω
  simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, norm_mul, norm_inv, norm_pow,
    norm_ofNat, norm_eq_abs]
  let ω₁ : Fin n → Ω := fun k ↦ (ω k).1
  let ω₂ : Fin n → Ω := fun k ↦ (ω k).2
  rw [inv_mul_le_iff₀' (by simp)]
  rw [mul_comm (↑n * (b + b))]
  calc
    _ ≤ ∑ σ : Signs n, |⨆ i, (|∑ k : Fin n, ↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))|)| := by
      apply Finset.abs_sum_le_sum_abs
    _ ≤ ∑ σ : Signs n, ⨆ i, |(|∑ k : Fin n, ↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))|)| := by
      apply Finset.sum_le_sum
      intro σ _
      simp only [Int.reduceNeg, abs_abs]
      apply Eq.le
      simp only [Int.reduceNeg, abs_eq_self]
      by_cases h : Nonempty ι
      · apply le_ciSup_of_le _ (Classical.choice h)
        · simp
        · apply bddAbove_range_abs_sum_signed_sub hf'
      · simp only [not_nonempty_iff] at h
        simp
    _ ≤ ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, |↑↑(σ k) * (f i (X (ω k).1) - f i (X (ω k).2))| := by
      apply Finset.sum_le_sum
      intro σ _
      apply ciSup_mono
      · apply bddAbove_range_sum_abs_signed_sub X hf' ω σ
      · intro i
        simp only [Int.reduceNeg, abs_abs]
        apply Finset.abs_sum_le_sum_abs
    _ ≤ ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, |(f i (X (ω k).1) - f i (X (ω k).2))| := by
      conv in fun σ : Signs n ↦ _ =>
        ext σ
        conv in fun i ↦ _ =>
          ext i
          conv in fun k ↦ _ =>
            ext k
            rw [abs_mul]
            simp
    _ ≤ ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (|f i (X (ω k).1)| + |f i (X (ω k).2)|) := by
      apply Finset.sum_le_sum
      intro σ _
      apply ciSup_mono
      · apply bddAbove_range_sum_abs_add_abs X hf' ω
      · intro i
        apply Finset.sum_le_sum
        intro k _
        exact abs_sub (f i (X (ω k).1)) (f i (X (ω k).2))
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Signs.card, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.ofNat_pos, pow_pos, mul_le_mul_iff_right₀]
      by_cases h : Nonempty ι
      · apply ciSup_le
        intro i
        suffices  ∑ k : Fin n, (|f i (X (ω k).1)| + |f i (X (ω k).2)|) ≤ ∑ k : Fin n, (b + b) from by
          apply le_trans this _
          apply le_of_eq
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul]
          ring
        apply Finset.sum_le_sum fun k _ ↦ add_le_add (hf' i (X (ω k).1)) (hf' i (X (ω k).2))
      · simp only [not_nonempty_iff] at h
        simp only [iSup_of_isEmpty]
        apply mul_nonneg (Nat.cast_nonneg n)
        exact Left.add_nonneg hb hb

theorem measurable_signed_sup_sum_pair_fst [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable (fun ω : Fin n → Ω × Ω ↦ (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k).1)|) := by
  apply Measurable.mul measurable_const
  apply Finset.univ.measurable_sum
  intro σ _
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply measurable_const.mul
  apply (hf i).comp (measurable_pi_apply k).fst

theorem integrable_signed_sup_sum_pair_fst [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω ↦ (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k).1)|)
    (Measure.pi fun _ ↦ μ.prod μ) := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_signed_sup_sum_pair_fst hf).aestronglyMeasurable (n * b)
  filter_upwards with ω
  simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, norm_mul, norm_inv, norm_pow,
    norm_ofNat, norm_eq_abs]
  rw [inv_mul_le_iff₀' (by simp)]
  rw [mul_comm (↑n * b)]
  apply abs_sum_sup_signed_le_pow_mul_bound hb hf'

theorem measurable_signed_sup_sum_pair_snd [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable (fun ω : Fin n → Ω × Ω ↦ (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k).2)|) := by
  apply Measurable.mul measurable_const
  apply Finset.univ.measurable_sum
  intro σ _
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply measurable_const.mul
  apply (hf i).comp (measurable_pi_apply k).snd

theorem integrable_signed_sup_sum_pair_snd [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω ↦ (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω k).2)|)
    (Measure.pi fun _ ↦ μ.prod μ) := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_signed_sup_sum_pair_snd hf).aestronglyMeasurable (n * b)
  filter_upwards with ω
  simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, norm_mul, norm_inv, norm_pow,
    norm_ofNat, norm_eq_abs]
  rw [inv_mul_le_iff₀' (by simp)]
  rw [mul_comm (↑n * b)]
  apply abs_sum_sup_signed_le_pow_mul_bound hb hf'

theorem integrable_sup_abs_integral_sum_sub {X : Ω → Z} [inst_2 : Nonempty ι] [inst_3 : Countable ι]
  (hf : ∀ (i : ι), Measurable (f i ∘ X)) {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
  Integrable (fun a ↦ ⨆ i, |∫ (x : Fin n → Ω), ∑ k : Fin n, (f i (X (a k)) - f i (X (x k))) ∂μⁿ|) μⁿ := by
        constructor
        · apply Measurable.aestronglyMeasurable
          apply measurable_sup_abs_integral_sum_sub hf
        · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*(b+b))
          filter_upwards with ω'
          refine abs_iSup_le ?hf.right.h.hf
          intro i
          simp only [Finset.sum_sub_distrib, abs_abs]
          rw [abs_le]
          constructor
          · suffices ∀ (x : Fin n → Ω), (-(↑n * (b + b)) ≤ ∑ x : Fin n, f i (X (ω' x)) - ∑ x_1 : Fin n, f i (X (x x_1))) from by
              calc
              _ = ∫ (x : Fin n → Ω), -(↑n * (b + b)) ∂μⁿ := by simp
              _ ≤ ∫ (x : Fin n → Ω), ∑ x : Fin n, f i (X (ω' x)) - ∑ x_1 : Fin n, f i (X (x x_1)) ∂μⁿ := by
                apply MeasureTheory.integral_mono
                · exact integrable_const _
                · constructor
                  · refine AEStronglyMeasurable.const_add ?hg.left.hf (∑ x : Fin n, f i (X (ω' x)))
                    refine aestronglyMeasurable_iff_aemeasurable.mpr ?hg.left.hf.a
                    refine AEMeasurable.neg ?hg.left.hf.a.hf
                    have w : ∀ (x_1 : Fin n), (AEMeasurable (fun a ↦ f i (X (a x_1))) μⁿ) := by
                      intro x_1
                      exact Integrable.aemeasurable (integrable_eval_comp hf hf' i x_1)
                    apply Measurable.aemeasurable
                    apply measurable_pi_sum (hf i)
                  · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*(b+b))
                    filter_upwards
                    intro a
                    simp only [norm_eq_abs]
                    calc
                    _ ≤ |∑ x : Fin n, f i (X (ω' x))| + |∑ x_1 : Fin n, f i (X (a x_1))| := by
                      exact abs_sub (∑ x : Fin n, f i (X (ω' x))) (∑ x_1 : Fin n, f i (X (a x_1)))
                    _ ≤ (↑n * b) + (↑n * b) := by
                      apply add_le_add
                      · calc
                        _ ≤ ∑ x : Fin n, |f i (X (ω' x))| := by
                          exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ f i (X (ω' i_1))) Finset.univ
                        _ ≤ ∑ x : Fin n, b := by
                          exact Finset.sum_le_sum fun i_1 a ↦ hf' i (X (ω' i_1))
                        _ = ↑n * b := by simp
                      · calc
                        _ ≤ ∑ x : Fin n, |f i (X (a x))| := by
                          exact Finset.abs_sum_le_sum_abs (fun x ↦ f i (X (a x))) Finset.univ
                        _ ≤ ∑ x : Fin n, b := by
                          exact Finset.sum_le_sum fun i_1 _ ↦ hf' i (X (a i_1))
                        _ = ↑n * b := by simp
                    _ = ↑n * (b + b) := by ring
                · exact this
            intro x
            have t : -↑n * b ≤ ∑ x : Fin n, f i (X (ω' x)) := by
              calc
              _ = ∑ x : Fin n, (-b) := by simp
              _ ≤ ∑ x : Fin n, f i (X (ω' x)) := by
                have u : ∀ (x : Fin n), -b ≤ f i (X (ω' x)) := by
                  intro x
                  exact neg_le_of_abs_le (hf' i (X (ω' x)))
                exact Finset.sum_le_sum fun i a ↦ u i
            have t' : -↑n * b ≤ - ∑ x_1 : Fin n, f i (X (x x_1)) := by
              simp only [neg_mul, neg_le_neg_iff]
              calc
              _ ≤ ∑ x_1 : Fin n, b := by
                apply Finset.sum_le_sum
                exact fun i_1 a ↦ le_of_max_le_left (hf' i (X (x i_1)))
              _ = ↑n * b := by simp
            linarith
          · have p : (∫ (x : Fin n → Ω), ∑ x : Fin n, f i (X (ω' x)) - ∑ x_1 : Fin n, f i (X (x x_1)) ∂μⁿ) ≤ (∫ (x : Fin n → Ω), ↑n * (b + b) ∂μⁿ) := by
              apply integral_mono
              apply Integrable.sub
              constructor
              exact aestronglyMeasurable_const
              exact hasFiniteIntegral_const (∑ x : Fin n, f i (X (ω' x)))
              constructor
              · apply Measurable.aestronglyMeasurable
                apply measurable_pi_sum (hf i)
              · apply HasFiniteIntegral.of_mem_Icc
                filter_upwards
                intro a
                constructor
                · have p : (∑ x_1 : Fin n, (-b)) ≤ ∑ x_1 : Fin n, f i (X (a x_1)) := by
                    refine Finset.sum_le_sum ?_
                    intro i_1 hi_1
                    exact neg_le_of_abs_le (hf' i (X (a i_1)))
                  exact p
                · have p : ∑ x_1 : Fin n, f i (X (a x_1)) ≤ (∑ x_1 : Fin n, b) := by
                    refine Finset.sum_le_sum ?_
                    intro i_1 hi_1
                    exact le_of_max_le_left (hf' i (X (a i_1)))
                  exact p
              apply integrable_const
              refine Pi.le_def.mpr ?_
              intro i_1
              have q : ∑ x : Fin n, f i (X (ω' x)) ≤ ∑ x : Fin n, b := by
                refine Finset.sum_le_sum ?_
                exact fun i_2 a ↦ le_of_max_le_left (hf' i (X (ω' i_2)))
              have q' : ∑ x : Fin n, -b ≤ ∑ x_1 : Fin n, f i (X (i_1 x_1)) := by
                refine Finset.sum_le_sum ?_
                exact fun i_2 a ↦ neg_le_of_abs_le (hf' i (X (i_1 i_2)))
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at q
              simp only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul] at q'
              linarith
            rw [<- (by simp : (∫ (x : Fin n → Ω), ↑n * (b + b) ∂μⁿ) = ↑n * (b + b))]
            exact p

omit [MeasurableSpace Ω] in
theorem bounded_difference_of_bounded {f : ι → Z → ℝ} {X : Ω → Z} {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b)
    (ω : Fin n → Ω) (i : ι) (ω' : Fin n → Ω) :
    |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))| ≤ ↑n * (b + b) :=
  calc
    _ ≤ ∑ k : Fin n, |(f i (X (ω k)) - f i (X (ω' k)))| :=
      Finset.univ.abs_sum_le_sum_abs (fun k ↦ f i (X (ω k)) - f i (X (ω' k)))
    _ ≤ ∑ k : Fin n, (|f i (X (ω k))| + |f i (X (ω' k))|) := by
      gcongr with k
      exact abs_sub (f i (X (ω k))) (f i (X (ω' k)))
    _ ≤ ∑ k : Fin n, (b + b) := by
      gcongr with k
      · exact hf' i (X (ω k))
      · exact hf' i (X (ω' k))
    _ ≤ ↑n * b + ↑n * b := by simp
    _ = _ := by
      ring

theorem measurable_norm_sup_abs_sum_sub [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) (ω : Fin n → Ω) :
    Measurable (fun ω' : Fin n → Ω ↦ ‖⨆ i, |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))|‖) := by
  apply Measurable.norm
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply Measurable.sub
  apply (hf i).comp measurable_const
  exact measurable_eval_comp hf i k

theorem integrable_norm_sup_abs_sum_sub [Nonempty ι] [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (ω : Fin n → Ω) :
    Integrable (fun ω' ↦ ‖⨆ i, |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))|‖) μⁿ := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_norm_sup_abs_sum_sub hf ω).aestronglyMeasurable (n * (b + b))
  filter_upwards with ω'
  simp only [norm_eq_abs, abs_abs]
  apply abs_iSup_le
  intro i
  simp only [abs_abs]
  apply bounded_difference_of_bounded hf'

theorem measurable_signed_sup_sum_prod_fst [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable (fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|) := by
  apply Measurable.mul measurable_const
  apply Finset.univ.measurable_sum
  intro σ _
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply measurable_const.mul
  apply (hf i).comp
  apply measurable_fst.eval

theorem integrable_signed_sup_sum_prod_fst [Nonempty ι] [Countable ι] {X : Ω → Z} (hf : ∀ (i : ι), Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ (↑(Fintype.card (Signs n)))⁻¹ * ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|)
      (μⁿ.prod μⁿ) := by
  simp_rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_signed_sup_sum_prod_fst hf).aestronglyMeasurable (n * b)
  filter_upwards with ω
  simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, norm_mul, norm_inv, norm_pow,
    norm_ofNat, norm_eq_abs]
  rw [inv_mul_le_iff₀' (by simp)]
  rw [mul_comm (↑n * b)]
  calc
    _ ≤ ∑ σ : Signs n, |(⨆ i, |∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|)| := by
      apply Finset.univ.abs_sum_le_sum_abs
    _ ≤ ∑ σ : Signs n, (⨆ i, (|∑ k : Fin n, ↑↑(σ k) * f i (X (ω.1 k))|)) := by
      apply Finset.sum_le_sum
      intro σ _
      apply abs_iSup_le
      intro i
      simp only [Int.reduceNeg, abs_abs]
      apply le_ciSup_of_le
      · apply bddAbove_range_abs_sum_signed hf'
      · apply le_of_eq rfl
    _ ≤ ∑ σ : Signs n, (⨆ i, (∑ k : Fin n, |↑↑(σ k) * f i (X (ω.1 k))|)) := by
      apply Finset.sum_le_sum
      intro σ _
      apply ciSup_mono
      · apply bddAbove_range_sum_abs_signed hf'
      · intro i
        exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ ↑↑(σ i_1) * f i (X (ω.1 i_1))) Finset.univ
    _ = ∑ σ : Signs n, (⨆ i, (∑ k : Fin n, |f i (X (ω.1 k))|)) := by
      congr
      ext σ
      congr
      ext i
      congr
      ext k
      simp only [Int.reduceNeg, abs_mul, Signs.apply_abs', one_mul]
    _ ≤ ∑ σ : Signs n, (⨆ i, (∑ k : Fin n, b)) := by
      apply Finset.sum_le_sum
      intro σ _
      apply ciSup_mono
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Set.range_const, bddAbove_singleton]
      · intro i
        apply Finset.sum_le_sum
        intro k _
        exact hf' i (X (ω.1 k))
    _ ≤ 2 ^ n * (↑n * b) := by simp

theorem integrable_sup_integral_abs_sum_sub {X : Ω → Z} [Nonempty ι] [Countable ι]
    (hf : ∀ i, Measurable (f i ∘ X)) {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω ↦ ⨆ i, ∫ ω', |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))| ∂μⁿ) μⁿ := by
  simp_rw [← memLp_one_iff_integrable]
  refine MemLp.of_bound ?_ (n*(b+b)) ?_
  · apply (Measurable.iSup _).aestronglyMeasurable
    intro i
    apply (Measurable.stronglyMeasurable _).integral_prod_left.measurable
    apply Measurable.abs
    apply Finset.univ.measurable_sum
    intro k _
    apply ((hf i).comp measurable_snd.eval).sub ((hf i).comp measurable_fst.eval)
  · filter_upwards with ω
    apply abs_iSup_le
    intro i
    apply abs_expectation_le_of_abs_le_const
    filter_upwards with ω'
    simp only [abs_abs]
    apply bounded_difference_of_bounded hf'

theorem integrable_integral_sup_abs_sum_sub {X : Ω → Z} [inst_2 : Nonempty ι]
  [inst_3 : Countable ι] (hf : ∀ (i : ι), Measurable (f i ∘ X)) {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
  Integrable
    (fun ω ↦ ∫ (x : Fin n → Ω), (fun ω' ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))|) x ∂μⁿ)
    μⁿ := by
  simp_rw [← memLp_one_iff_integrable]
  refine MemLp.of_bound ?_ (n*(b+b)) ?_
  · apply Measurable.aestronglyMeasurable
    apply StronglyMeasurable.measurable
    refine StronglyMeasurable.integral_prod_left ?_
    apply Measurable.stronglyMeasurable
    dsimp [Function.uncurry_def]
    apply Measurable.iSup
    intro i
    apply Measurable.abs
    apply Finset.univ.measurable_sum
    intro k _
    apply Measurable.sub
    apply (hf i).comp measurable_snd.eval
    apply (hf i).comp measurable_fst.eval
  · filter_upwards with ω
    suffices ∫ (x : Fin n → Ω), ‖⨆ i, |∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))|‖ ∂μⁿ ≤
        ∫ (x : Fin n → Ω), ⨆ i : ι, ∑ k : Fin n, (b + b) ∂μⁿ from by
      have h : ∫ (x : Fin n → Ω), ⨆ i : ι, ∑ k : Fin n, (b + b) ∂μⁿ = n * (b + b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul,
          ciSup_const, integral_const, smul_eq_mul]
        rw [probReal_univ]
        ring
      rw [← h]
      apply le_trans _ this
      apply norm_integral_le_integral_norm
    apply integral_mono
    · exact integrable_norm_sup_abs_sum_sub hf hf' ω
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul,
      ciSup_const, integrable_const]
    intro ω'
    apply abs_iSup_le
    intro i
    rw [abs_abs]
    suffices |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))| ≤ ↑n * (b + b) from by
      convert this
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul,
        ciSup_const]
      ring
    apply bounded_difference_of_bounded hf'

theorem measurable_sup_abs_sum_sub_prod{X : Ω → Z}
  [inst_3 : Countable ι] (hf : ∀ (i : ι), Measurable (f i ∘ X)) :
    Measurable (fun ω : ((Fin n → Ω) × (Fin n → Ω)) ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω.1 k)) - f i (X (ω.2 k)))|) := by
  apply Measurable.iSup
  intro i
  apply Measurable.abs
  apply Finset.univ.measurable_sum
  intro k _
  apply Measurable.sub
  apply (hf i).comp measurable_fst.eval
  apply (hf i).comp measurable_snd.eval

theorem integrable_sup_abs_sum_sub_prod {X : Ω → Z} [inst_2 : Nonempty ι]
    [inst_3 : Countable ι] (hf : ∀ (i : ι), Measurable (f i ∘ X)) {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    Integrable (fun ω ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω.1 k)) - f i (X (ω.2 k)))|)
      (μⁿ.prod μⁿ) := by
  rw [← memLp_one_iff_integrable]
  apply MemLp.of_bound (measurable_sup_abs_sum_sub_prod hf).aestronglyMeasurable (n * (b + b))
  filter_upwards with ω
  apply abs_iSup_le
  intro i
  simp only [abs_abs]
  exact bounded_difference_of_bounded hf' ω.1 i ω.2

theorem integral_sum_sub_eq_sum_sub_integral {X : Ω → Z} (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b)(ω : Fin n → Ω) (i : ι) :
    (∫ (ω' : Fin n → Ω), ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k))) ∂μⁿ) =
      ∑ k : Fin n, (f i (X (ω k)) - ∫ (ω' : Fin n → Ω), f i (X (ω' k)) ∂μⁿ) :=
  calc
    _ = (∫ (ω' : Fin n → Ω), (∑ k : Fin n, (f i (X (ω k))) - (∑ k : Fin n, f i (X (ω' k)))) ∂μⁿ) := by
      apply congrArg
      funext ω'
      exact Finset.sum_sub_distrib (fun x ↦ f i (X (ω x))) fun x ↦ f i (X (ω' x))
    _ = (∫ (ω' : Fin n → Ω), ∑ k : Fin n, f i (X (ω k)) ∂μⁿ) - (∫ (ω' : Fin n → Ω), ∑ k : Fin n, f i (X (ω' k)) ∂μⁿ) := by
      apply integral_sub
      · simp
      · apply integrable_finset_sum
        exact fun i_1 a ↦ integrable_eval_comp hf hf' i i_1
    _ = (∑ k : Fin n, f i (X (ω k)) - ∫ (ω' : Fin n → Ω), ∑ k : Fin n, f i (X (ω' k)) ∂μⁿ) := by simp
    _ = (∑ k : Fin n, f i (X (ω k)) - ∑ k : Fin n, ∫ (ω' : Fin n → Ω), f i (X (ω' k)) ∂μⁿ) := by
      simp only [sub_right_inj]
      exact integral_finset_sum Finset.univ (fun i_1 a ↦ integrable_eval_comp hf hf' i i_1)
    _ = ∑ k : Fin n, (f i (X (ω k)) - ∫ (ω' : Fin n → Ω), f i (X (ω' k)) ∂μⁿ) := by
      exact Eq.symm (Finset.sum_sub_distrib (fun x ↦ f i (X (ω x))) fun x ↦
          ∫ (ω' : (Fin n → Ω)), f i (X (ω' x)) ∂Measure.pi fun x ↦ μ)

theorem integral_fst_signed_sup_add_integral_snd_eq_two_mul
    {X : Ω → Z} [Nonempty ι] [Countable ι]
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    (μⁿ.prod μⁿ)[fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ ((Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, (|∑ k : Fin n, (σ k : ℝ) * f i (X (ω.1 k))|))]
          + ((Measure.pi fun _ ↦ μ).prod (Measure.pi fun _ ↦ μ))[fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω.2 k))|] =
      (2 * μⁿ[fun ω : Fin n → Ω ↦ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))|] : ℝ) := by
    rw [two_mul]
    apply congrArg₂
    · rw [integral_prod _ _]
      · dsimp only [Prod.fst]
        congr
        ext
        rw [integral_const]
        simp
      · exact integrable_signed_sup_sum_prod_fst hf hf'
    · rw [integral_prod _ _]
      · dsimp only [Prod.snd]
        rw [integral_const]
        simp
      · constructor
        · apply AEStronglyMeasurable.const_mul
          apply AEMeasurable.aestronglyMeasurable
          apply Measurable.aemeasurable
          refine Finset.measurable_sum Finset.univ ?left.hf.hf.h.hf
          intro i hi
          apply Measurable.iSup
          intro i_1
          refine Measurable.max ?left.hf.hf.h.hf.hf.hf ?left.hf.hf.h.hf.hf.hg
          have k0 : ∀ (k : Fin n), Measurable (fun (b : (Fin n → Ω) × (Fin n → Ω)) ↦ (i k : ℝ) * f i_1 (X (b.2 k))) := by
            intro k
            apply Measurable.mul
            exact measurable_const
            apply (hf i_1).comp
            refine Measurable.eval ?hg.hg
            exact measurable_snd
          exact Finset.measurable_sum Finset.univ fun i a ↦ k0 i
          apply Measurable.neg
          have k0 : ∀ (k : Fin n), Measurable (fun (b : (Fin n → Ω) × (Fin n → Ω)) ↦ (i k : ℝ) * f i_1 (X (b.2 k))) := by
            intro k
            apply Measurable.mul
            exact measurable_const
            apply (hf i_1).comp
            refine Measurable.eval ?hg.hg
          exact Finset.measurable_sum Finset.univ fun i a ↦ k0 i
        · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*b)
          filter_upwards
          intro a
          simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, norm_mul, norm_inv,
            norm_pow, norm_ofNat, norm_eq_abs]
          rw [inv_mul_le_iff₀]
          have l0 : |(∑ σ : Signs n, (⨆ i, |(∑ k : Fin n, (σ k : ℝ) * f i (X (a.2 k)))|))| ≤ ↑(2 ^ n) * (↑n * b) := by
            calc
            _ ≤ ∑ σ : Signs n, |(⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (a.2 k))|)| := by
              apply Finset.abs_sum_le_sum_abs
            _ ≤ ∑ σ : Signs n, ↑n * b := by
              apply Finset.sum_le_sum
              intro i hi
              apply abs_iSup_le
              intro i_1
              simp only [Int.reduceNeg, abs_abs]
              have l1 : |∑ k : Fin n, (i k : ℝ) * f i_1 (X (a.2 k))| ≤ ↑n * b := by
                calc
                _ ≤ ∑ k : Fin n, |(i k : ℝ) * f i_1 (X (a.2 k))| := by apply Finset.abs_sum_le_sum_abs
                _ ≤ ∑ k : Fin n, b := by
                  apply Finset.sum_le_sum
                  intro i_2 hi_2
                  rw [abs_mul]
                  rw [abs_sigma (i i_2)]
                  simp only [one_mul]
                  exact hf' i_1 (X (a.2 i_2))
                _ ≤ ↑n * b := by simp
              exact l1
            _ = Fintype.card (Signs n) * (↑n * b) := by simp
            _ = 2 ^ n * (↑n * b) := by simp
          exact l0
          simp

theorem bddAbove_range_integral_abs_sum_sub {X : Ω → Z} [Nonempty ι] [Countable ι]
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) (ω : Fin n → Ω) :
    BddAbove (Set.range fun i ↦ ∫ (x : Fin n → Ω), |∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))| ∂μⁿ) := by
  have hp : ∀ (i : ι) (j : Fin n), Integrable (fun (a : Fin n → Ω) ↦ f i (X (a j))) μⁿ := by
    apply integrable_eval_comp hf hf'
  have hr : ∃ C, ∀ (ω : Fin n → Ω) (k : Fin n), ∀ y ∈ (Set.range fun i ↦ f i (X (ω k))), y ≤ C := by
    exists b
    intro ω k y hy
    simp only [Set.mem_range] at hy
    obtain ⟨i, hi⟩ := hy
    rw [← hi]
    exact le_of_max_le_left (hf' i (X (ω k)))
  have hr' : ∃ C, ∀ (ω : Fin n → Ω) (k : Fin n), ∀ y ∈ (Set.range fun i ↦ f i (X (ω k))), C ≤ y := by
    exists -b
    intro ω k y hy
    simp only [Set.mem_range] at hy
    obtain ⟨i, hi⟩ := hy
    rw [← hi]
    exact neg_le_of_abs_le (hf' i (X (ω k)))
  have hq : ∀ (ω : Fin n → Ω) (k : Fin n), BddAbove (Set.range fun i ↦ f i (X (ω k))) := by
    intro ω k
    rw [bddAbove_def]
    use b
    intro x hx
    obtain ⟨i, hi⟩ := hx
    rw [← hi]
    exact le_of_max_le_left (hf' i (X (ω k)))
  have hq' : ∀ (ω : Fin n → Ω) (k : Fin n), BddBelow (Set.range fun i ↦ f i (X (ω k))) := by
    intro ω k
    rw [bddBelow_def]
    use -b
    intro x hx
    obtain ⟨i, hi⟩ := hx
    rw [← hi]
    exact neg_le_of_abs_le (hf' i (X (ω k)))
  have hq0 : ∀ (ω x: Fin n → Ω) (k : Fin n), BddAbove (Set.range fun i ↦ (f i (X (ω k)) - f i (X (x k)))) :=
  fun ω' x k => BddAbove.range_add (hq ω' k) (BddBelow.range_neg (hq' x k))
  have hq1 : ∀ (ω x: Fin n → Ω), BddAbove (Set.range fun i ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))) :=
    fun ω' x => BddAbove.range_comp (bddAbove_range_pi.mpr (hq0 ω' x)) fun f g hfg => Finset.sum_le_sum fun i a ↦ hfg i
  have hq2 : ∀ (ω x: Fin n → Ω) (k : Fin n), BddBelow (Set.range fun i ↦ (f i (X (ω k)) - f i (X (x k)))) :=
    fun ω' x k => BddBelow.range_add (hq' ω' k) (BddAbove.range_neg (hq x k))
  have hq3 : ∀ (ω x: Fin n → Ω), BddBelow (Set.range fun i ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))) :=
    fun ω' x => BddBelow.range_comp (bddBelow_range_pi.mpr (hq2 ω' x)) (fun f g hfg => Finset.sum_le_sum fun i a ↦ hfg i)
  have hq1 : ∀ (ω x: Fin n → Ω), BddAbove (Set.range fun i ↦ |∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))|) := by
    intro ω x
    obtain hq1'' := hq1 ω x
    obtain hq3'' := hq3 ω x
    have hr : ∃ a b, (Set.range fun i ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))) ⊆ Set.Icc a b := by
      rw [<- bddBelow_bddAbove_iff_subset_Icc]
      exact And.symm ⟨hq1 ω x, hq3 ω x⟩
    have hr' : ∃ a b, (Set.range fun i ↦ |∑ k : Fin n, (f i (X (ω k)) - f i (X (x k)))|) ⊆ Set.Icc a b := by
      obtain ⟨a, b, hab⟩ := hr
      use min a (-b)
      use max (-a) b
      rw [Set.range_subset_iff] at hab
      rw [Set.range_subset_iff]
      intro y
      have hab' := hab y
      rw [Set.mem_Icc] at hab'
      rw [Set.mem_Icc]
      obtain ⟨hab0', hab1'⟩ := hab'
      by_cases d : 0 ≤ ∑ k : Fin n, (f y (X (ω k)) - f y (X (x k)))
      case pos =>
        rw [abs_of_nonneg d]
        rw [inf_le_iff, le_sup_iff]
        exact ⟨Or.symm (Or.inr hab0'), Or.inr hab1'⟩
      case neg =>
        rw [abs_of_neg (lt_of_not_ge d)]
        constructor
        · rw [inf_le_iff]
          apply Or.inr (neg_le_neg_iff.mpr hab1')
        · rw [le_sup_iff]
          apply Or.inl (neg_le_neg_iff.mpr hab0')
    rw [<- bddBelow_bddAbove_iff_subset_Icc] at hr'
    exact hr'.2
  obtain ⟨C, hr0⟩ := hr
  obtain ⟨D, hr1⟩ := hr'
  apply BddAbove.range_mono
  intro a
  suffices (∫ (x : Fin n → Ω), |∑ k : Fin n, (f a (X (ω k)) - f a (X (x k)))| ∂μⁿ) ≤ n * (C - D) from by
    exact this
  have hr2 : ∀ (x : Fin n → Ω), |∑ k : Fin n, (f a (X (ω k)) - f a (X (x k)))| ≤ ↑n * (C - D) := by
    intro x
    calc
    _ ≤ ∑ k : Fin n, |(f a (X (ω k)) - f a (X (x k)))| := by
      exact Finset.abs_sum_le_sum_abs (fun i ↦ f a (X (ω i)) - f a (X (x i))) Finset.univ
    _ ≤ ∑ k : Fin n, (C - D) := by
      have w0 : ∀ (k : Fin n), |f a (X (ω k)) - f a (X (x k))| ≤ (C - D) := by
        intro k
        refine abs_sub_le_of_le_of_le ?hal ?hau ?hbl ?hbu
        repeat
        apply hr1
        simp only [Set.mem_range]
        use a
        apply hr0
        simp only [Set.mem_range]
        use a
      exact Finset.sum_le_sum fun i a ↦ w0 i
    _ = ↑n * (C - D) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have u : (∫ (x : Fin n → Ω), |∑ k : Fin n, (f a (X (ω k)) - f a (X (x k)))| ∂μⁿ) ≤ ↑n * (C - D) := by
    calc
    _ ≤ (∫ (x : Fin n → Ω), n * (C - D) ∂μⁿ) := by
      apply integral_mono
      -- Integrability
      · apply Integrable.abs
        apply Integrable.of_mem_Icc
        · apply Finset.aemeasurable_fun_sum Finset.univ _
          intro i hi
          refine AEMeasurable.sub ?_ ?_
          exact aemeasurable_const
          exact Integrable.aemeasurable (hp a i)
        · filter_upwards
          intro a_1
          constructor
          have g : ∑ k : Fin n, (- b - b) ≤ ∑ k : Fin n, (f a (X (ω k)) - f a (X (a_1 k))) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have q : -b ≤ f a (X (ω i)) := neg_le_of_abs_le (hf' a (X (ω i)))
            have q' : f a (X (a_1 i)) ≤ b := le_of_max_le_left (hf' a (X (a_1 i)))
            linarith
          exact g
          have g' : ∑ k : Fin n, (f a (X (ω k)) - f a (X (a_1 k))) ≤ ∑ k : Fin n, (b + b) := by
            apply Finset.sum_le_sum
            intro i hi
            have q : f a (X (ω i)) ≤ b := le_of_max_le_left (hf' a (X (ω i)))
            have q' : -b ≤ f a (X (a_1 i)) := neg_le_of_abs_le (hf' a (X (a_1 i)))
            linarith
          exact g'
      apply integrable_const
      exact hr2
    _ = n * (C - D) := by simp
  exact u
  rw [bddAbove_def]
  use n * (C - D) + 1
  intro y hy
  simp only [Set.range_const, Set.mem_singleton_iff] at hy
  rw [hy]
  linarith

theorem replace_mean_with_coordinate_mean {X : Ω → Z} [Nonempty ι] [Countable ι]
    (hf : ∀ i, Measurable (f i ∘ X)) :
    μⁿ[fun ω : Fin n → Ω ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k)) - μ[fun ω' ↦ f i (X ω')])|] =
      μⁿ[fun ω ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k)) - μⁿ[fun ω' ↦ f i (X (ω' k))])|] := by
  dsimp only
  congr
  ext _
  congr
  ext i
  congr
  ext k
  apply congrArg
  have : (Measure.map (fun f ↦ f k) (μⁿ))[fun y ↦ f i (X y)] = μⁿ[fun x : Fin n → Ω ↦ f i (X (x k))] :=
    integral_map (measurable_pi_apply k).aemeasurable (Measurable.aestronglyMeasurable (hf i))
  rw [← this,  pi_map_eval k]

/- Wainwright's Theorem 4.10, p.107 -/
theorem expectation_le_rademacher {X : Ω → Z} [Nonempty ι] [Countable ι]
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hb : b ≥ 0) (hf' : ∀ (i : ι) (z : Z), |f i z| ≤ b) :
    μⁿ[fun ω : Fin n → Ω ↦ ⨆ i, |∑ k : Fin n, f i (X (ω k)) - n • μ[fun ω' ↦ f i (X ω')]|] ≤
      (2 * n) • rademacherComplexity n f μ X := by
  by_cases hn : n = 0
  · rw [hn]
    simp
  have hr : ∃ C, ∀ (ω : Fin n → Ω) (k : Fin n), ∀ y ∈ (Set.range fun i ↦ f i (X (ω k))), y ≤ C := by
    exists b
    intro ω k y hy
    simp only [Set.mem_range] at hy
    obtain ⟨i, hi⟩ := hy
    rw [← hi]
    exact le_of_max_le_left (hf' i (X (ω k)))
  have hr' : ∃ C, ∀ (ω : Fin n → Ω) (k : Fin n), ∀ y ∈ (Set.range fun i ↦ f i (X (ω k))), C ≤ y := by
    exists -b
    intro ω k y hy
    simp only [Set.mem_range] at hy
    obtain ⟨i, hi⟩ := hy
    rw [← hi]
    exact neg_le_of_abs_le (hf' i (X (ω k)))
  have hq : ∀ (ω : Fin n → Ω) (k : Fin n), BddAbove (Set.range fun i ↦ f i (X (ω k))) := by
    intro ω k
    rw [bddAbove_def]
    obtain ⟨C, hr0⟩ := hr
    use C
    exact hr0 ω k
  have hq' : ∀ (ω : Fin n → Ω) (k : Fin n), BddBelow (Set.range fun i ↦ f i (X (ω k))) := by
    intro ω k
    rw [bddBelow_def]
    obtain ⟨C, hr1⟩ := hr'
    use C
    exact hr1 ω k
  calc
    _ = μⁿ[fun ω ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k)) - μ[fun ω' ↦ f i (X ω')])|] := by
      -- Move both terms inside the sum
      apply congrArg
      funext ω
      apply congrArg
      funext i
      simp
    _ = μⁿ[fun ω ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k)) - μⁿ[fun ω' ↦ f i (X (ω' k))])|] := by
      -- Replace `Y` with a copy of `X`
      apply replace_mean_with_coordinate_mean hf
    _ = μⁿ[fun ω ↦ ⨆ i, |μⁿ[fun ω' ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))]|] := by
      -- Swap the sum and the expectation
      apply congrArg
      funext ω
      apply congrArg
      funext i
      apply congrArg
      symm
      apply integral_sum_sub_eq_sum_sub_integral hf hf' ω i
    _ ≤ μⁿ[fun ω ↦ ⨆ i, μⁿ[fun ω' ↦ |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))|]] := by
      -- Exchange the absolute value and the integral
      apply integral_mono
      -- TODO: integrability
      · apply integrable_sup_abs_integral_sum_sub hf hf'
      · apply integrable_sup_integral_abs_sum_sub hf hf'
      · intro ω
        apply ciSup_mono
        · apply bddAbove_range_integral_abs_sum_sub hf hf'
        · intro x
          have w : ‖∫ (x_1 : Fin n → Ω), ∑ k : Fin n, (f x (X (ω k)) - f x (X (x_1 k))) ∂μⁿ‖ ≤
            ∫ (x_1 : Fin n → Ω), ‖∑ k : Fin n, (f x (X (ω k)) - f x (X (x_1 k)))‖ ∂μⁿ := by
            apply norm_integral_le_integral_norm
          simp only [norm_eq_abs] at w
          exact w
    _ ≤ (μⁿ[fun ω ↦ μⁿ[fun ω' ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))|]] : ℝ) := by
      apply integral_mono _ _
      intro ω
      apply iSup_integral_le (μ := μⁿ) (b := n * (b + b))
      · exact fun i ↦ measurable_sum_sub_right hf i ω
      · intro i x
        exact bounded_difference_of_bounded hf' ω i x
      -- TODO: integrability
      · apply integrable_sup_integral_abs_sum_sub hf hf'
      · apply integrable_integral_sup_abs_sum_sub hf hf'
    _ = (Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω k).1) - f i (X (ω k).2))|] := by
      -- Rewrite using the product measure
      dsimp only
      rw [←integral_prod fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ ⨆ i, |∑ k : Fin n, (f i (X (ω.1 k)) - f i (X (ω.2 k)))|]
      let mp := measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) (fun _ ↦ μ) (fun _ ↦ μ)
      rw [←mp.map_eq, integral_map mp.measurable.aemeasurable]
      · rfl
      · apply Measurable.aestronglyMeasurable
        apply Measurable.iSup
        intro i
        apply Measurable.max
        refine Finset.measurable_sum Finset.univ ?_
        intro i_1 hi_1
        apply Measurable.sub
        apply (hf i).comp
        refine Measurable.eval ?_
        exact measurable_fst
        apply (hf i).comp
        refine Measurable.eval ?_
        exact measurable_snd
        apply Measurable.neg
        refine Finset.measurable_sum Finset.univ ?_
        intro i_1 hi_1
        apply Measurable.sub
        apply (hf i).comp
        refine Measurable.eval ?_
        exact measurable_fst
        apply (hf i).comp
        refine Measurable.eval ?_
        exact measurable_snd
      · apply integrable_sup_abs_sum_sub_prod hf hf'
    _ = (Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω ↦ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * (f i (X (ω k).1) - f i (X (ω k).2))|] := by
      -- symmetrization argument
      rw [Signs.card]
      simp only [Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg]
      rw [← inv_pow 2 n]
      apply abs_symmetrization_equation hf hf'
    _ ≤ (Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω ↦ ((Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, (|∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).1)|))
          + (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).2)|] := by
      -- Split the supremum across the sum
      apply integral_mono
      · exact integrable_signed_sup_sum_sub hf hb hf'
      · apply Integrable.add
        · apply integrable_signed_sup_sum_pair_fst hf hb hf'
        · apply integrable_signed_sup_sum_pair_snd hf hb hf'
      apply symmetrization_signed_sup_le_add hf'
    _ = (μⁿ.prod μⁿ)[fun ω : (Fin n → Ω) × (Fin n → Ω) ↦
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, (|∑ k : Fin n, (σ k : ℝ) * f i (X (ω.1 k))|))
          + (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω.2 k))|] := by
      -- commutativity of Measure.prod and Measure.pi
      let mp := measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) (fun _ ↦ μ) (fun _ ↦ μ)
      rw [←mp.map_eq, integral_map mp.measurable.aemeasurable]
      · rfl
      · apply AEMeasurable.aestronglyMeasurable
        apply Measurable.aemeasurable
        apply Measurable.add
        · apply Measurable.const_mul
          exact measurable_signed_sup_sum_fst_core hf
        · apply Measurable.const_mul
          rw [← measurable_swap_iff]
          exact measurable_signed_sup_sum_fst_core hf
    _ = (μⁿ.prod μⁿ)[fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ ((Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, (|∑ k : Fin n, (σ k : ℝ) * f i (X (ω.1 k))|))]
          + ((Measure.pi fun _ ↦ μ).prod (Measure.pi fun _ ↦ μ))[fun ω : (Fin n → Ω) × (Fin n → Ω) ↦ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω.2 k))|] := by
      -- Move the sum outside the integral
      apply integral_add
      · apply integrable_signed_sup_sum_fst hf hb hf'
      · rw [← integrable_swap_iff]
        apply integrable_signed_sup_sum_fst hf hb hf'
    _ = (2 * μⁿ[fun ω : Fin n → Ω ↦ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, |∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))|] : ℝ) := by
      -- Integrate each part separately
      apply integral_fst_signed_sup_add_integral_snd_eq_two_mul hf hf'
    _ = (2 * n) * rademacherComplexity n f μ X := by
      -- Definition of the Rademacher complexity
      dsimp [rademacherComplexity, empiricalRademacherComplexity]
      rw [mul_assoc]
      congr
      rw [←integral_const_mul]
      congr
      ext _
      ring_nf
      rw [mul_assoc]
      congr
      rw [Finset.mul_sum]
      congr
      ext _
      rw [Real.mul_iSup_of_nonneg (by norm_num)]
      congr
      ext _
      rw [abs_mul]
      have : |(n:ℝ)⁻¹| = (n:ℝ)⁻¹ := by
        apply abs_of_nonneg
        apply inv_nonneg_of_nonneg
        norm_num
      rw [this, ←mul_assoc]
      rw [CommGroupWithZero.mul_inv_cancel, one_mul]
      apply Nat.cast_ne_zero.mpr hn
    _ = _ := by simp

end
