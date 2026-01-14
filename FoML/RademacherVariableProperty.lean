import FoML.Defs
import FoML.Symmetrization
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open Real Function MeasureTheory
open scoped ENNReal

universe u v w
variable (n : ℕ) (k l : Fin n)

-- There is also a lemma about properties of Rademacher variables in the symmetrization file

local instance : Inhabited { z : ℤ // z ∈ ({-1, 1} : Finset ℤ) } :=
  ⟨⟨1, by simp⟩⟩

local instance : Inhabited (Signs n) :=
  ⟨fun _ => ⟨1, by simp⟩⟩

def rademacher_flip (σ : Signs n) : Signs n := fun i =>
  if i = k then -(σ i) else σ i

theorem double_rademacher_flip (σ : Signs n) : rademacher_flip n k (rademacher_flip n k σ) = σ := by
  dsimp [rademacher_flip, Signs]
  ext i
  apply Subtype.ext_iff.mp
  by_cases h : i = k
  · rw [h]
    simp only [Int.reduceNeg, ↓reduceIte, rademacher_flip]
    cases σ k with
    | mk val h' =>
        apply Or.elim (by simp at h'; exact h')
        · intro s
          subst s
          exact rfl
        · intro s
          subst s
          exact rfl
  · dsimp [rademacher_flip]
    simp [h]

theorem bijective_rademacher_flip : Bijective (rademacher_flip n k) := Involutive.bijective (double_rademacher_flip n k)

theorem sign_sum_eq_zero : ∑ σ : Signs n, (σ k : ℝ) = 0 := by
  have : ∑ σ : Signs n, (σ k : ℝ) = ∑ σ : Signs n, (rademacher_flip n k σ k : ℝ) := by
    apply Finset.sum_bijective
    · apply bijective_rademacher_flip
      exact k
    · intro i
      simp
    · intro i hi
      rw [double_rademacher_flip]
  have : ∑ σ : Signs n, (σ k : ℝ) + ∑ σ, (rademacher_flip n k σ k : ℝ) = 0 := by
    calc
    _ = ∑ σ : Signs n, ((σ k : ℝ) + (rademacher_flip n k σ k : ℝ)) := by
      exact Eq.symm Finset.sum_add_distrib
    _ = ∑ σ : Signs n, 0 := by
      apply congrArg
      ext σ
      norm_cast
      dsimp [rademacher_flip]
      simp
      exact add_eq_zero_iff_eq_neg'.mpr rfl
    _ = 0 := by simp
  grind

theorem sign_flip_product_invariance : ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) = ∑ σ : Signs n, (rademacher_flip n k σ k : ℝ) * (rademacher_flip n k σ l : ℝ) := by
  apply Finset.sum_bijective
  · apply bijective_rademacher_flip
    exact k
  · intro i
    simp
  · intro i hi
    rw [double_rademacher_flip]

theorem pair_sum_zero (pkl : k ≠ l) : ∀ σ : Fin n → ({-1, 1} : Finset ℤ),
    (σ k : ℝ) * (σ l : ℝ) + (rademacher_flip n k σ) k * (rademacher_flip n k σ) l = 0 := by
  dsimp [rademacher_flip]
  simp only [Int.reduceNeg, ↓reduceIte]
  intro σ
  calc
  _ = (σ k : ℝ) * (σ l : ℝ) + (-σ k) * (σ l) := by
    apply add_left_cancel_iff.mpr
    apply congr
    apply congrArg
    norm_cast
    apply Int.cast_inj.mpr
    apply Subtype.ext_iff.mp
    simp only [Int.reduceNeg, ite_eq_right_iff]
    intro pkl'
    exact False.elim (pkl (id (Eq.symm pkl')))
  _ = ((σ k) + (-σ k)) * (σ l) := by symm; apply RightDistribClass.right_distrib
  _ = (σ k - σ k) * (σ l) := by simp
  _ = 0 := by simp

theorem rademacher_orthogonality (n : ℕ) (k l : Fin n) (pkl : k ≠ l):
    ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) = 0 := by
  have sum_partition : ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) =
                      (1/2) * ∑ σ : Signs n, ((σ k : ℝ) * σ l + (rademacher_flip n k σ) k * (rademacher_flip n k σ) l) := by
    calc
    _ = (1/2) * (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) + ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ)) := by
      field_simp
      simp only [Int.reduceNeg, mul_eq_mul_left_iff]
      left
      norm_num
    _ = (1/2) * (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) + ∑ σ : Signs n, (rademacher_flip n k σ k : ℝ) * (rademacher_flip n k σ l : ℝ)) := by
      have p : ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) = ∑ σ : Signs n, (rademacher_flip n k σ k : ℝ) * (rademacher_flip n k σ l : ℝ) := sign_flip_product_invariance n k l
      rw [p]
    _ = _ := by
      apply congrArg
      exact Eq.symm Finset.sum_add_distrib
  rw [sum_partition]
  simp [pair_sum_zero n k l pkl]

noncomputable def signVecPMF (n : ℕ) : PMF (Signs n) :=
  PMF.uniformOfFintype (Signs n)

variable {ι : Type v} {𝒳 : Type w}

-- Equip with the discrete sigma-algebra
noncomputable instance : MeasurableSpace (Signs n) := ⊤

local notation3 "𝙋" => (signVecPMF n).toMeasure

noncomputable def empiricalRademacherComplexity_pmf
    (f : ι → 𝒳 → ℝ) (x : Fin n → 𝒳) : ℝ :=
  ∫ σ, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (x k)| ∂𝙋

lemma empiricalRademacherComplexity_eq_empiricalRademacherComplexity_pmf
    (f : ι → 𝒳 → ℝ) (x : Fin n → 𝒳) :
    empiricalRademacherComplexity n f x = empiricalRademacherComplexity_pmf n f x := by
  dsimp [empiricalRademacherComplexity, empiricalRademacherComplexity_pmf]
  set g : Signs n → ℝ :=
    (fun σ => ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (x k)|)
  have htsum :
    (∫ σ, g σ ∂𝙋)
      = ∑' σ : Signs n, g σ * ((signVecPMF n) σ).toReal := by
    rw [PMF.integral_eq_tsum]
    · congr
      ext σ
      simp
      exact CommMonoid.mul_comm ((signVecPMF n) σ).toReal (g σ)
    . dsimp [g]
      rw [<- MeasureTheory.memLp_one_iff_integrable]
      simp
  have huniform :
    ∑' σ : Signs n, g σ * ((signVecPMF n) σ).toReal
      = (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, g σ := by
    simp [signVecPMF, PMF.uniformOfFintype_apply,
          tsum_fintype, Finset.mul_sum, ENNReal.toReal_inv]
    apply congrArg
    ext σ
    exact Eq.symm (CommMonoid.mul_comm (2 ^ n)⁻¹ (g σ))
  rw [<- htsum] at huniform
  rw [<- huniform]

noncomputable def empiricalRademacherComplexity_pmf_without_abs
    (f : ι → 𝒳 → ℝ) (x : Fin n → 𝒳) : ℝ :=
  ∫ σ, ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (x k) ∂𝙋

lemma empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs
    (f : ι → 𝒳 → ℝ) (x : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n f x = empiricalRademacherComplexity_pmf_without_abs n f x := by
  dsimp [empiricalRademacherComplexity_without_abs, empiricalRademacherComplexity_pmf_without_abs]
  set g : Signs n → ℝ :=
    (fun σ => ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (x k))
  have htsum :
    (∫ σ, g σ ∂𝙋)
      = ∑' σ : Signs n, g σ * ((signVecPMF n) σ).toReal := by
    rw [PMF.integral_eq_tsum]
    · congr
      ext σ
      simp
      exact CommMonoid.mul_comm ((signVecPMF n) σ).toReal (g σ)
    . dsimp [g]
      rw [<- MeasureTheory.memLp_one_iff_integrable]
      simp
  have huniform :
    ∑' σ : Signs n, g σ * ((signVecPMF n) σ).toReal
      = (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, g σ := by
    simp [signVecPMF, PMF.uniformOfFintype_apply,
          tsum_fintype, Finset.mul_sum, ENNReal.toReal_inv]
    apply congrArg
    ext σ
    exact Eq.symm (CommMonoid.mul_comm (2 ^ n)⁻¹ (g σ))
  rw [<- htsum] at huniform
  rw [<- huniform]

lemma empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity
    (f : ι → 𝒳 → ℝ) (x : Fin n → 𝒳)
    (C : ℝ) (sC : 0 ≤ C) (hC : ∀ i j, |f i (x j)| ≤ C) :
    empiricalRademacherComplexity_without_abs n f x ≤ empiricalRademacherComplexity n f x := by
  dsimp [empiricalRademacherComplexity_without_abs, empiricalRademacherComplexity]
  apply mul_le_mul_of_nonneg_left
  refine Finset.sum_le_sum ?_
  intro i hi
  refine ciSup_mono ?_ ?_
  · rw [bddAbove_def]
    use C
    simp only [Int.reduceNeg, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
    intro a
    rw [abs_mul]
    calc
    _ ≤ |(↑n)⁻¹| * ∑ k, |↑↑(i k) * f a (x k)| := by
      apply mul_le_mul_of_nonneg_left
      exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ ↑↑(i i_1) * f a (x i_1)) Finset.univ
      simp
    _ = |(↑n)⁻¹| * ∑ k, |↑↑(i k)| * |f a (x k)| := by
      repeat apply congrArg
      ext k
      rw [abs_mul]
    _ = |(↑n)⁻¹| * ∑ k, 1 * |f a (x k)|  := by
      repeat apply congrArg
      ext k
      rw [abs_sigma]
    _ = |(↑n)⁻¹| * ∑ k, |f a (x k)| := by simp
    _ ≤ C := by
      refine mul_le_of_le_inv_mul₀ ?_ ?_ ?_
      · exact sC
      · simp
      · have : |(↑n)⁻¹|⁻¹ = (↑n : ℝ) := by
          simp [abs_of_nonneg]
        rw [this]
        calc
        ∑ k, |f a (x k)| ≤ ∑ k, C := by
          refine Finset.sum_le_sum ?_
          intro k hk
          simpa using hC a k
        _ = (n : ℝ) * C := by
          simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro x_1
    exact le_abs_self ((↑n)⁻¹ * ∑ k, ↑↑(i k) * f x_1 (x k))
  · simp
