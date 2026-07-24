import FoML.Rademacher.Expectation
import FoML.ForMathlib.Analysis.FiniteSample
import FoML.ForMathlib.Order.ISup

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω] {𝒳 : Type w}
variable {n : ℕ} {ι : Type v} {f : ι → 𝒳 → ℝ} {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Replacing one observation changes uniform deviation by at most `2 * b / n`
for a function class bounded in absolute value by `b`.
-/
theorem uniformDeviation_bounded_difference [Nonempty ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ i, ∀ z : 𝒳, |f i z| ≤ b)
    (i : Fin n) (S : Fin n → 𝒳) (x' : 𝒳) :
    |uniformDeviation n f μ X S -
      uniformDeviation n f μ X (Function.update S i x')| ≤
      (n : ℝ)⁻¹ * 2 * b := by
  let g (h : ι) :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, f h (S k) -
      ∫ x : Ω, f h (X x) ∂μ
  let g' (h : ι) :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, f h (Function.update S i x' k) -
      ∫ x : Ω, f h (X x) ∂μ
  have hmean : ∀ h, |∫ x : Ω, f h (X x) ∂μ| ≤ b := by
    intro h
    calc
      |∫ x : Ω, f h (X x) ∂μ| ≤ ∫ x : Ω, |f h (X x)| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x : Ω, b ∂μ := by
        apply integral_mono
        · constructor
          · exact (measurable_abs.comp (hf h)).aestronglyMeasurable
          · apply HasFiniteIntegral.of_mem_Icc
            filter_upwards
            intro x
            exact ⟨abs_nonneg _, hf' h (X x)⟩
        · exact integrable_const b
        · exact fun x ↦ hf' h (X x)
      _ = b := by simp
  have hsample :
      ∀ (T : Fin n → 𝒳) (h : ι),
        |(n : ℝ)⁻¹ * ∑ k : Fin n, f h (T k)| ≤ b := by
    intro T h
    exact abs_normalized_fin_sum_le hn (fun _ x ↦ f h x) T
      (fun _ x ↦ hf' h x)
  have hpoint : ∀ h, |g h - g' h| ≤ (n : ℝ)⁻¹ * 2 * b := by
    intro h
    dsimp only [g, g']
    rw [sub_sub_sub_cancel_right]
    exact abs_normalized_fin_sum_update_sub_le hn
      (fun _ x ↦ f h x) (fun _ x ↦ hf' h x) i S x'
  have hg : BddAbove (Set.range fun h ↦ |g h|) := by
    refine ⟨b + b, ?_⟩
    rintro _ ⟨h, rfl⟩
    calc
      |g h| ≤
          |(n : ℝ)⁻¹ * ∑ k : Fin n, f h (S k)| +
            |∫ x : Ω, f h (X x) ∂μ| := by
              exact abs_sub _ _
      _ ≤ b + b := add_le_add (hsample S h) (hmean h)
  have hg' : BddAbove (Set.range fun h ↦ |g' h|) := by
    refine ⟨b + b, ?_⟩
    rintro _ ⟨h, rfl⟩
    calc
      |g' h| ≤
          |(n : ℝ)⁻¹ * ∑ k : Fin n, f h (Function.update S i x' k)| +
            |∫ x : Ω, f h (X x) ∂μ| := by
              exact abs_sub _ _
      _ ≤ b + b :=
        add_le_add (hsample (Function.update S i x') h) (hmean h)
  dsimp only [uniformDeviation]
  exact abs_ciSup_sub_ciSup_le hg hg' fun h ↦
    (abs_abs_sub_abs_le_abs_sub (g h) (g' h)).trans (hpoint h)

theorem uniformDeviation_measurable [Countable ι] [MeasurableSpace 𝒳]
    (X : Ω → 𝒳) (hf : ∀ i, Measurable (f i)) :
    Measurable (uniformDeviation n f μ X) :=
  .iSup fun i ↦ ((measurable_const.mul (Finset.univ.measurable_sum fun j _ ↦
    (hf i).comp (measurable_pi_apply j))).add_const
      (-∫ x : Ω, (fun ω' ↦ f i (X ω')) x ∂μ)).abs

/--
Replacing one observation changes absolute empirical Rademacher complexity by
at most `2 * b / n` for a class bounded in absolute value by `b`.
-/
theorem empiricalRademacherComplexity_bounded_difference
    [Nonempty ι]
    (hn : 0 < n) {b : ℝ}
    (hf' : ∀ i, ∀ z : 𝒳, |f i z| ≤ b)
    (j : Fin n) (S : Fin n → 𝒳) (x' : 𝒳) :
    |empiricalRademacherComplexity n f S -
      empiricalRademacherComplexity n f (Function.update S j x')| ≤
      (n : ℝ)⁻¹ * 2 * b := by
  classical
  let A (σ : Signs n) (i : ι) :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)
  let B (σ : Signs n) (i : ι) :=
    (n : ℝ)⁻¹ * ∑ k : Fin n,
      (σ k : ℝ) * f i (Function.update S j x' k)
  have hnorm :
      ∀ (T : Fin n → 𝒳) (σ : Signs n) (i : ι),
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (T k)| ≤ b := by
    intro T σ i
    apply abs_normalized_fin_sum_le hn
      (fun k x ↦ (σ k : ℝ) * f i x) T
    intro k x
    simpa [abs_mul, abs_sigma] using hf' i x
  have hpoint :
      ∀ (σ : Signs n) (i : ι),
        |A σ i - B σ i| ≤ (n : ℝ)⁻¹ * 2 * b := by
    intro σ i
    exact abs_normalized_fin_sum_update_sub_le hn
      (fun k x ↦ (σ k : ℝ) * f i x)
      (fun k x ↦ by simpa [abs_mul, abs_sigma] using hf' i x)
      j S x'
  have hsup :
      ∀ σ : Signs n,
        |((⨆ i, |A σ i|) - (⨆ i, |B σ i|))| ≤
          (n : ℝ)⁻¹ * 2 * b := by
    intro σ
    have hAbdd : BddAbove (Set.range fun i ↦ |A σ i|) :=
      ⟨b, by
        rintro _ ⟨i, rfl⟩
        exact hnorm S σ i⟩
    have hBbdd : BddAbove (Set.range fun i ↦ |B σ i|) :=
      ⟨b, by
        rintro _ ⟨i, rfl⟩
        exact hnorm (Function.update S j x') σ i⟩
    exact abs_ciSup_sub_ciSup_le hAbdd hBbdd fun i ↦
      (abs_abs_sub_abs_le_abs_sub (A σ i) (B σ i)).trans (hpoint σ i)
  dsimp only [empiricalRademacherComplexity]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul]
  have hcard : 0 < (Fintype.card (Signs n) : ℝ) := by
    rw [Signs.card]
    positivity
  rw [abs_of_pos (inv_pos.mpr hcard)]
  calc
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        |∑ σ : Signs n,
          ((⨆ i, |A σ i|) - (⨆ i, |B σ i|))|
        ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n,
              |((⨆ i, |A σ i|) - (⨆ i, |B σ i|))| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs
            (fun σ : Signs n ↦ (⨆ i, |A σ i|) - (⨆ i, |B σ i|)) Finset.univ
    _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ _σ : Signs n, ((n : ℝ)⁻¹ * 2 * b) := by
          gcongr with σ
          exact hsup σ
    _ = (n : ℝ)⁻¹ * 2 * b := by simp

end
