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

/-- Empirical Rademacher complexity is nonnegative. -/
lemma empiricalRademacherComplexity_nonneg
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    0 ≤ empiricalRademacherComplexity n f S := by
  dsimp [empiricalRademacherComplexity]
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro σ _
    exact Real.iSup_nonneg fun i ↦
      abs_nonneg ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k))

/-- Pulling a function class back along a map is the same as mapping the sample. -/
lemma empiricalRademacherComplexity_comp
    {𝒴 : Type*} (g : ι → 𝒴 → ℝ) (q : 𝒳 → 𝒴) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x ↦ g i (q x)) S =
      empiricalRademacherComplexity n g (q ∘ S) := by
  rfl

/-- Add a negative copy of every function in a class. -/
def signSymmetrization (F : ι → 𝒳 → ℝ) : ι × Bool → 𝒳 → ℝ :=
  fun ib x ↦ if ib.2 then F ib.1 x else -F ib.1 x

/-- A function class is closed under pointwise negation. -/
def IsNegClosed (F : ι → 𝒳 → ℝ) : Prop :=
  ∀ i, ∃ j, F j = -F i

private lemma abs_normalized_signed_sum_le
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (C : ℝ) (sC : 0 ≤ C) (hC : ∀ i j, |f i (S j)| ≤ C)
    (σ : Signs n) (i : ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)| ≤ C := by
  by_cases hn : n = 0
  · subst n
    simpa using sC
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn_pos)]
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
    _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, C := by
          gcongr with k
          exact hC i k
    _ = C := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp

/--
Absolute empirical Rademacher complexity is the one-sided complexity of the
class enlarged by pointwise negatives.
-/
lemma empiricalRademacherComplexity_eq_without_abs_signSymmetrization
    [Nonempty ι] (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (C : ℝ) (sC : 0 ≤ C) (hC : ∀ i j, |f i (S j)| ≤ C) :
    empiricalRademacherComplexity n f S =
      empiricalRademacherComplexity_without_abs n (signSymmetrization f) S := by
  dsimp [empiricalRademacherComplexity, empiricalRademacherComplexity_without_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  let A : ι → ℝ :=
    fun i ↦ (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)
  have hrewrite :
      (fun ib : ι × Bool ↦
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * signSymmetrization f ib (S k)) =
        fun ib ↦ if ib.2 then A ib.1 else -A ib.1 := by
    funext ib
    rcases ib with ⟨i, b⟩
    cases b <;> simp [signSymmetrization, A]
  rw [hrewrite]
  have hA : ∀ i, |A i| ≤ C :=
    fun i ↦ abs_normalized_signed_sum_le n f S C sC hC σ i
  have habs : BddAbove (Set.range fun i ↦ |A i|) :=
    ⟨C, by rintro _ ⟨i, rfl⟩; exact hA i⟩
  have hsym : BddAbove (Set.range fun ib : ι × Bool ↦
      if ib.2 then A ib.1 else -A ib.1) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨i, b⟩, rfl⟩
    cases b
    · exact (neg_le_abs (A i)).trans (hA i)
    · exact (le_abs_self (A i)).trans (hA i)
  apply le_antisymm
  · apply ciSup_le
    intro i
    rw [abs_eq_max_neg]
    apply max_le
    · simpa using
        (le_ciSup hsym (i, true))
    · simpa using
        (le_ciSup hsym (i, false))
  · apply ciSup_le
    rintro ⟨i, b⟩
    cases b
    · exact (neg_le_abs (A i)).trans (le_ciSup habs i)
    · exact (le_abs_self (A i)).trans (le_ciSup habs i)

/--
For a class closed under pointwise negation, absolute and one-sided empirical
Rademacher complexity agree.
-/
lemma empiricalRademacherComplexity_eq_without_abs_of_neg_closed
    [Nonempty ι] (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (C : ℝ) (sC : 0 ≤ C) (hC : ∀ i j, |f i (S j)| ≤ C)
    (hneg : IsNegClosed f) :
    empiricalRademacherComplexity n f S =
      empiricalRademacherComplexity_without_abs n f S := by
  dsimp [empiricalRademacherComplexity, empiricalRademacherComplexity_without_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  let A : ι → ℝ :=
    fun i ↦ (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)
  have hA : ∀ i, |A i| ≤ C :=
    fun i ↦ abs_normalized_signed_sum_le n f S C sC hC σ i
  have habs : BddAbove (Set.range fun i ↦ |A i|) :=
    ⟨C, by rintro _ ⟨i, rfl⟩; exact hA i⟩
  have hplain : BddAbove (Set.range A) :=
    ⟨C, by rintro _ ⟨i, rfl⟩; exact (le_abs_self (A i)).trans (hA i)⟩
  change (⨆ i, |A i|) = ⨆ i, A i
  apply le_antisymm
  · apply ciSup_le
    intro i
    obtain ⟨j, hj⟩ := hneg i
    have hAj : A j = -A i := by
      dsimp only [A]
      rw [hj]
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [abs_eq_max_neg]
    apply max_le
    · exact le_ciSup hplain i
    · rw [← hAj]
      exact le_ciSup hplain j
  · apply ciSup_le
    intro i
    exact (le_abs_self (A i)).trans (le_ciSup habs i)

-- Equip with the discrete sigma-algebra
noncomputable instance : MeasurableSpace (Signs n) := ⊤

local notation3 "𝙋" => (signVecPMF n).toMeasure

noncomputable def empiricalRademacherComplexity_pmf
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  ∫ σ, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (S k)| ∂𝙋

lemma empiricalRademacherComplexity_eq_empiricalRademacherComplexity_pmf
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n f S = empiricalRademacherComplexity_pmf n f S := by
  dsimp [empiricalRademacherComplexity, empiricalRademacherComplexity_pmf]
  set g : Signs n → ℝ :=
    (fun σ => ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (S k)|)
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
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  ∫ σ, ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (S k) ∂𝙋

lemma empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n f S = empiricalRademacherComplexity_pmf_without_abs n f S := by
  dsimp [empiricalRademacherComplexity_without_abs, empiricalRademacherComplexity_pmf_without_abs]
  set g : Signs n → ℝ :=
    (fun σ => ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (((σ k).1 : ℤ) : ℝ) * f i (S k))
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
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (C : ℝ) (sC : 0 ≤ C) (hC : ∀ i j, |f i (S j)| ≤ C) :
    empiricalRademacherComplexity_without_abs n f S ≤ empiricalRademacherComplexity n f S := by
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
    _ ≤ |(↑n)⁻¹| * ∑ k, |↑↑(i k) * f a (S k)| := by
      apply mul_le_mul_of_nonneg_left
      exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ ↑↑(i i_1) * f a (S i_1)) Finset.univ
      simp
    _ = |(↑n)⁻¹| * ∑ k, |↑↑(i k)| * |f a (S k)| := by
      repeat apply congrArg
      ext k
      rw [abs_mul]
    _ = |(↑n)⁻¹| * ∑ k, 1 * |f a (S k)|  := by
      repeat apply congrArg
      ext k
      rw [abs_sigma]
    _ = |(↑n)⁻¹| * ∑ k, |f a (S k)| := by simp
    _ ≤ C := by
      refine mul_le_of_le_inv_mul₀ ?_ ?_ ?_
      · exact sC
      · simp
      · have : |(↑n)⁻¹|⁻¹ = (↑n : ℝ) := by
          simp [abs_of_nonneg]
        rw [this]
        calc
        ∑ k, |f a (S k)| ≤ ∑ k, C := by
          refine Finset.sum_le_sum ?_
          intro k hk
          simpa using hC a k
        _ = (n : ℝ) * C := by
          simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro x_1
    exact le_abs_self ((↑n)⁻¹ * ∑ k, ↑↑(i k) * f x_1 (S k))
  · simp
