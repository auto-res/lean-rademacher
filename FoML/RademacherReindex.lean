import FoML.Rademacher
import FoML.ForMathlib.Analysis.FiniteSample
import FoML.ForMathlib.Order.ISup

/-!
# Reindexing function classes

These lemmas distinguish a purely set-theoretic change of hypothesis index
from the topological `denseRestriction` bridge.  Pulling a class back along
an arbitrary map can only decrease empirical complexity; a surjective map
does not change the class and hence preserves all three central quantities.
-/

open MeasureTheory

universe u v w x

section

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {G : Type w} {𝒳 : Type x}

/-- A surjective reindexing preserves the common empirical functional. -/
theorem empiricalRademacherFunctional_reindex_eq_of_surjective
    (φ : ℝ → ℝ) (F : H → 𝒳 → ℝ) (e : G → H)
    (he : Function.Surjective e) (S : Fin n → 𝒳) :
    empiricalRademacherFunctional n φ (fun g ↦ F (e g)) S =
      empiricalRademacherFunctional n φ F S := by
  dsimp [empiricalRademacherFunctional, normalizedRademacherSum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact ciSup_comp_of_surjective e he
    (fun h ↦ φ ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k)))

/--
Pulling a uniformly bounded class back along an arbitrary index map can only
decrease absolute empirical Rademacher complexity.
-/
theorem empiricalRademacherComplexity_reindex_le
    [Nonempty G]
    (F : H → 𝒳 → ℝ) (e : G → H) (S : Fin n → 𝒳)
    {b : ℝ} (hb : 0 ≤ b) (hF : ∀ h x, |F h x| ≤ b) :
    empiricalRademacherComplexity n (fun g ↦ F (e g)) S ≤
      empiricalRademacherComplexity n F S := by
  dsimp [empiricalRademacherComplexity]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro σ _
    have hbounded :
        BddAbove (Set.range fun h ↦
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k)|) := by
      refine ⟨b, ?_⟩
      rintro _ ⟨h, rfl⟩
      by_cases hn : n = 0
      · subst n
        simpa using hb
      · apply abs_normalized_fin_sum_le (Nat.pos_of_ne_zero hn)
          (fun k x ↦ (σ k : ℝ) * F h x) S
        intro k x
        simpa [abs_mul, abs_sigma] using hF h x
    apply ciSup_le
    intro g
    exact le_ciSup hbounded (e g)
  · positivity

/-- A surjective reindexing preserves absolute empirical Rademacher complexity. -/
theorem empiricalRademacherComplexity_reindex_eq_of_surjective
    (F : H → 𝒳 → ℝ) (e : G → H)
    (he : Function.Surjective e) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun g ↦ F (e g)) S =
      empiricalRademacherComplexity n F S := by
  simpa only [← empiricalRademacherFunctional_abs] using
    empiricalRademacherFunctional_reindex_eq_of_surjective
      (n := n) abs F e he S

/-- A surjective reindexing preserves one-sided empirical Rademacher complexity. -/
theorem empiricalRademacherComplexity_without_abs_reindex_eq_of_surjective
    (F : H → 𝒳 → ℝ) (e : G → H)
    (he : Function.Surjective e) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (fun g ↦ F (e g)) S =
      empiricalRademacherComplexity_without_abs n F S := by
  simpa only [← empiricalRademacherFunctional_id] using
    empiricalRademacherFunctional_reindex_eq_of_surjective
      (n := n) id F e he S

/-- A surjective hypothesis reindexing preserves expected Rademacher complexity. -/
theorem rademacherComplexity_reindex_eq_of_surjective
    (F : H → 𝒳 → ℝ) (e : G → H) (he : Function.Surjective e)
    (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity n (fun g ↦ F (e g)) μ X =
      rademacherComplexity n F μ X := by
  dsimp [rademacherComplexity]
  apply integral_congr_ae
  filter_upwards with S
  exact empiricalRademacherComplexity_reindex_eq_of_surjective
    (n := n) F e he (X ∘ S)

/-- A surjective hypothesis reindexing preserves uniform deviation. -/
theorem uniformDeviation_reindex_eq_of_surjective
    (F : H → 𝒳 → ℝ) (e : G → H) (he : Function.Surjective e)
    (μ : Measure Ω) (X : Ω → 𝒳) (S : Fin n → 𝒳) :
    uniformDeviation n (fun g ↦ F (e g)) μ X S =
      uniformDeviation n F μ X S := by
  dsimp [uniformDeviation]
  exact ciSup_comp_of_surjective e he
    (fun h ↦
      |(n : ℝ)⁻¹ * ∑ k : Fin n, F h (S k) -
        ∫ x : Ω, F h (X x) ∂μ|)

end
