import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Normalized finite-sample sums

Elementary estimates for normalized sums over `Fin n`.  The summand may
depend on the coordinate, so the update lemma also applies to signed sums.
-/

open scoped BigOperators

/-- A normalized finite sum of uniformly bounded summands is uniformly bounded. -/
theorem abs_normalized_fin_sum_le
    {n : ℕ} {α : Type*} (hn : 0 < n)
    (a : Fin n → α → ℝ) (S : Fin n → α)
    {b : ℝ} (ha : ∀ k x, |a k x| ≤ b) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, a k (S k)| ≤ b := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn')]
  calc
    (n : ℝ)⁻¹ * |∑ k : Fin n, a k (S k)|
        ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, |a k (S k)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs (fun k : Fin n ↦ a k (S k)) Finset.univ
    _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b := by
          apply mul_le_mul_of_nonneg_left
          exact Finset.sum_le_sum fun k _ ↦ ha k (S k)
          positivity
    _ = b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp

/--
Replacing one coordinate changes a normalized sum by at most `2 * b / n`
when every coordinate summand is bounded in absolute value by `b`.
-/
theorem abs_normalized_fin_sum_update_sub_le
    {n : ℕ} {α : Type*} (hn : 0 < n)
    (a : Fin n → α → ℝ) {b : ℝ} (ha : ∀ k x, |a k x| ≤ b)
    (j : Fin n) (S : Fin n → α) (x' : α) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, a k (S k) -
      (n : ℝ)⁻¹ * ∑ k : Fin n, a k (Function.update S j x' k)| ≤
      (n : ℝ)⁻¹ * 2 * b := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum :
      ∑ k : Fin n, (a k (S k) - a k (Function.update S j x' k)) =
        a j (S j) - a j x' := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Function.update, hkj]
    · simp
  calc
    |(n : ℝ)⁻¹ * ∑ k : Fin n, a k (S k) -
        (n : ℝ)⁻¹ * ∑ k : Fin n, a k (Function.update S j x' k)| =
        |(n : ℝ)⁻¹ *
          ∑ k : Fin n, (a k (S k) - a k (Function.update S j x' k))| := by
            simp only [← mul_sub, ← Finset.sum_sub_distrib]
    _ = (n : ℝ)⁻¹ * |a j (S j) - a j x'| := by
          rw [hsum, abs_mul, abs_of_pos (inv_pos.mpr hn')]
    _ ≤ (n : ℝ)⁻¹ * (|a j (S j)| + |a j x'|) := by
          gcongr
          exact abs_sub _ _
    _ ≤ (n : ℝ)⁻¹ * (b + b) := by
          gcongr
          · exact ha j (S j)
          · exact ha j x'
    _ = (n : ℝ)⁻¹ * 2 * b := by ring
