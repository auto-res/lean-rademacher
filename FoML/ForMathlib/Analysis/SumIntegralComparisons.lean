import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic

/-!
# Additional sum-integral comparisons

These lemmas compare a left Riemann sum along a monotone sequence with the
integral of an antitone function.
-/

open MeasureTheory

theorem MonotoneOn.leftRiemann_sum_le_integral_antitoneOn
    (n : ℕ) (f : ℕ → ℝ) (g : ℝ → ℝ)
    (hf : Monotone f) (hg : AntitoneOn g (Set.Icc (f 0) (f n)))
    (j : Fin n) :
    (f (j + 1) - f j) * g (f (j + 1)) ≤
      ∫ x : ℝ in f j..f (j + 1), g x := by
  calc
    _ = ∫ x : ℝ in f j..f (j + 1), g (f (j + 1)) := by simp
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on
      · exact hf (by simp)
      · exact AntitoneOn.intervalIntegrable antitoneOn_const
      · apply AntitoneOn.intervalIntegrable
        refine antitoneOn_iff_forall_lt.mpr ?_
        intro a ha b hb hab
        apply hg
        · suffices
              Set.uIcc (f (j : ℕ)) (f ((j : ℕ) + 1)) ⊆
                Set.Icc (f 0) (f n) by
            grind
          refine Set.uIcc_subset_Icc ?_ ?_
          · exact ⟨hf (by simp), hf (by simp)⟩
          · exact ⟨hf (by simp), hf (Order.add_one_le_of_lt (by simp))⟩
        · suffices
              Set.uIcc (f (j : ℕ)) (f ((j : ℕ) + 1)) ⊆
                Set.Icc (f 0) (f n) by
            grind
          refine Set.uIcc_subset_Icc ?_ ?_
          · exact ⟨hf (by simp), hf (by simp)⟩
          · exact ⟨hf (by simp), hf (Order.add_one_le_of_lt (by simp))⟩
        exact hab.le
      intro x hx
      simp at hx
      apply hg
      · constructor
        · have : f 0 ≤ f (j : ℕ) := hf (by simp)
          linarith
        · have : f ((j : ℕ) + 1) ≤ f n :=
            hf (Order.add_one_le_of_lt (by simp))
          linarith
      · exact ⟨hf (by simp), hf (Order.add_one_le_of_lt (by simp))⟩
      exact hx.2

theorem AntitoneOn.leftRiemann_sum_le_integral
    (n : ℕ) (f : ℕ → ℝ) (g : ℝ → ℝ)
    (hf : Antitone f) (hg : AntitoneOn g (Set.Icc (f n) (f 0))) :
    ∑ j : Fin n, (f j - f (j + 1)) * g (f j) ≤
      ∫ x : ℝ in f n..f 0, g x := by
  by_cases hn : 0 < n
  · let h (p : ℕ) := f (n - p)
    have h0 : f n = h 0 := by
      dsimp [h]
    have h1 : f 0 = h n := by
      dsimp [h]
      simp
    have hh : Monotone h := by
      dsimp [h]
      change Monotone (f ∘ fun p ↦ n - p)
      exact hf.comp antitone_const_tsub
    rw [h0, h1]
    rw [← intervalIntegral.sum_integral_adjacent_intervals]
    have hsum :
        ∑ j : Fin n, (f (j : ℕ) - f ((j : ℕ) + 1)) * g (f (j : ℕ)) =
          ∑ j : Fin n,
            (h ((j : ℕ) + 1) - h (j : ℕ)) * g (h ((j : ℕ) + 1)) := by
      let e : Fin n ≃ Fin n :=
        { toFun := fun j =>
            ⟨n - 1 - j, by
              have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hn)
              exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
          invFun := fun j =>
            ⟨n - 1 - j, by
              have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hn)
              exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
          left_inv := by
            intro j
            apply Fin.ext
            have hj : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
            have : n - 1 - (n - 1 - j) = j := by grind
            simp [this]
          right_inv := by
            intro j
            apply Fin.ext
            have hj : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
            have : n - 1 - (n - 1 - j) = j := by grind
            simp [this] }
      have hcomp :=
        Equiv.sum_comp e (fun j : Fin n ↦ (f j - f (j + 1)) * g (f j))
      refine hcomp.symm.trans ?_
      refine Finset.sum_congr rfl ?_
      intro j _
      change
        (f (e j) - f (e j + 1)) * g (f (e j)) =
          (h (j + 1) - h j) * g (h (j + 1))
      dsimp [e, h]
      have hj : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
      simp [Nat.sub_sub, Nat.add_comm]
      left
      apply congrArg
      grind
    rw [hsum]
    have hrange :
        ∑ k ∈ Finset.range n, ∫ x : ℝ in h k..h (k + 1), g x =
          ∑ k : Fin n, ∫ x : ℝ in h k..h (k + 1), g x :=
      Finset.sum_range fun i ↦ ∫ x : ℝ in h i..h (i + 1), g x
    rw [hrange]
    apply Finset.sum_le_sum
    intro i _
    apply MonotoneOn.leftRiemann_sum_le_integral_antitoneOn
    · exact hh
    · simpa [← h0, ← h1] using hg
    intro k _
    apply AntitoneOn.intervalIntegrable
    rw [h0, h1] at hg
    apply hg.mono
    refine Set.uIcc_subset_Icc ?_ ?_
    · exact ⟨hh (by simp), hh (by linarith)⟩
    · exact ⟨hh (by simp), hh (by linarith)⟩
  · have : n = 0 := by linarith
    subst n
    simp
