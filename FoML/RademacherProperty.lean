import FoML.Defs

open Real Function
open scoped ENNReal

variable (n : ℕ) (k l : Fin n)

def rademacher_flip (σ : Signs n) : Signs n := fun i =>
  if i = k then -(σ i) else σ i

theorem double_rademacher_flip (σ : Signs n) : rademacher_flip n k (rademacher_flip n k σ) = σ := by
  dsimp [rademacher_flip, Signs]
  ext i
  apply Subtype.eq_iff.mp
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
  simp only [Int.reduceNeg, ↓reduceIte, rademacher_flip]
  intro σ
  calc
  _ = (σ k : ℝ) * (σ l : ℝ) + (-σ k) * (σ l) := by
    apply add_left_cancel_iff.mpr
    apply congr
    apply congrArg
    norm_cast
    apply Int.cast_inj.mpr
    apply Subtype.eq_iff.mp
    simp only [Int.reduceNeg, ite_eq_right_iff, rademacher_flip]
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
    _ = (1/2) * (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) + ∑ σ : Signs n, (rademacher_flip n k σ k : ℝ) * (rademacher_flip n k σ l : ℝ)) := by
      have p : ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) = ∑ σ : Signs n, (rademacher_flip n k σ k : ℝ) * (rademacher_flip n k σ l : ℝ) := sign_flip_product_invariance n k l
      rw [p]
    _ = _ := by
      apply congrArg
      exact Eq.symm Finset.sum_add_distrib
  rw [sum_partition]
  simp [pair_sum_zero n k l pkl]
