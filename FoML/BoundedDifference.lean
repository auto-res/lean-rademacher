import FoML.Rademacher

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω] {Z : Type w}
variable {n : ℕ} {ι : Type v} {f : ι → Z → ℝ} {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

theorem uniformDeviation_bounded_difference [Nonempty ι] [IsProbabilityMeasure μ]
    (hn : 0 < n) (X : Ω → Z)
    (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hb : 0 ≤ b)
    (hf': ∀ i, ∀ z : Z, |f i z| ≤ b)
    (i : Fin n) (x : Fin n → Z) (x' : Z) :
    |uniformDeviation n f μ X x - uniformDeviation n f μ X (Function.update x i x')| ≤
      (n : ℝ)⁻¹ * 2 * b := by
  dsimp [uniformDeviation]
  let g (i : ι) := (↑n)⁻¹ * ∑ k : Fin n, f i (x k) - ∫ (x : Ω), f i (X x) ∂μ
  let h (i_1 : ι) := (↑n)⁻¹ * ∑ k : Fin n, f i_1 (Function.update x i x' k) - ∫ (x : Ω), f i_1 (X x) ∂μ
  have s' : ∀ (a : ι), |∫ (x : Ω), f a (X x) ∂μ| ≤ b := by
    intro a
    calc
    _ ≤ ∫ (x : Ω), |f a (X x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ (x : Ω), b ∂μ := by
      apply integral_mono
      · constructor
        · apply Measurable.aestronglyMeasurable
          exact Measurable.comp measurable_abs (hf a)
        · apply HasFiniteIntegral.of_mem_Icc
          filter_upwards
          intro a_1
          constructor
          · exact abs_nonneg (f a (X a_1))
          · apply hf'
      · exact integrable_const b
      exact fun i ↦ hf' a (X i)
    _ = b := by simp
  have p''' : ∀ j, |g j - h j| ≤ (↑n)⁻¹ * 2 * b := by
    intro j
    calc
    _ = |(↑n)⁻¹ * ∑ k : Fin n, f j (x k) - (↑n)⁻¹ * ∑ k : Fin n, f j (Function.update x i x' k)| := by
      dsimp [g, h]
      rw [sub_sub_sub_cancel_right]
    _ = |(↑n)⁻¹ * (∑ k : Fin n, f j (x k) - ∑ k : Fin n, f j (Function.update x i x' k))| := by
      apply congrArg
      exact
        Eq.symm
          (mul_sub_left_distrib (↑n)⁻¹ (∑ k : Fin n, f j (x k))
            (∑ k : Fin n, f j (Function.update x i x' k)))
    _ = |(↑n)⁻¹ * (∑ k : Fin n, (f j (x k) - f j (Function.update x i x' k)))| := by
      apply congrArg
      rw [Finset.sum_sub_distrib]
    _ = (↑n)⁻¹ * |(∑ k : Fin n, (f j (x k) - f j (Function.update x i x' k)))| := by
      rw [abs_mul]
      simp
    _ ≤ (↑n)⁻¹ * 2 * b := by
      refine (inv_mul_le_iff₀' ?_).mpr ?_
      exact Nat.cast_pos'.mpr hn
      have pe : (↑n)⁻¹ * 2 * b * ↑n = 2 * b := by
        field_simp
      rw [pe]
      trans ∑ k : Fin n, |(f j (x k) - f j (Function.update x i x' k))|
      · exact
        Finset.abs_sum_le_sum_abs (fun i_1 ↦ f j (x i_1) - f j (Function.update x i x' i_1))
          Finset.univ
      · calc
        _ = ∑ k : Fin n, |if i = k then f j (x k) - f j x' else 0| := by
          apply congrArg
          ext k
          apply congrArg
          dsimp [Function.update]
          simp only [eq_rec_constant, dite_eq_ite]
          have t : f j (x k) - f j (if k = i then x' else x k) = if i = k then f j (x k) - f j x' else 0 := by
            calc
            _ = f j (x k) - (if k = i then f j x' else f j (x k)) := by
              simp only [sub_right_inj]
              exact apply_ite (f j) (k = i) x' (x k)
            _ = (if k = i then f j (x k) - f j x' else f j (x k) - f j (x k)) := by
              exact sub_ite (k = i) (f j (x k)) (f j x') (f j (x k))
            _ = _ := by
              simp only [sub_self]
              refine Eq.symm (if_congr ?_ rfl rfl)
              exact eq_comm
          exact t
        _ = ∑ k : Fin n, if i = k then |f j (x k) - f j x'| else |0| := by
          apply congrArg
          ext k
          exact apply_ite abs (i = k) (f j (x k) - f j x') 0
        _ = |f j (x i) - f j x'| := by simp
        _ ≤ |f j (x i)| + |f j x'| := abs_sub (f j (x i)) (f j x')
        _ ≤ b + b := add_le_add (hf' j (x i)) (hf' j x')
        _ = 2 * b := by ring
  suffices |(⨆ (i : ι), (|g i|)) - ⨆ (i_1 : ι), (|h i_1|)| ≤ (↑n)⁻¹ * 2 * b from by
    exact this
  have p : (⨆ i, |g i|) - ⨆ i_1, |h i_1| ≤ (↑n)⁻¹ * 2 * b := by
    have p0 : (⨆ i, |g i|) - ⨆ i_1, |h i_1| = ⨆ i, |g i| - ⨆ i_1, |h i_1| := by
      apply ciSup_sub
      rw [bddAbove_def]
      use b + b
      simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro a
      have s : |(↑n)⁻¹ * ∑ k : Fin n, f a (x k)| ≤ b := by
        calc
        _ = (↑n)⁻¹ * |∑ k : Fin n, f a (x k)| := by
          rw [abs_mul]
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, |f a (x k)| := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.abs_sum_le_sum_abs (fun i ↦ f a (x i)) Finset.univ
          simp
          refine Fintype.sum_nonneg ?_
          refine Pi.le_def.mpr ?_
          intro i
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, b := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.sum_le_sum fun i a_1 ↦ hf' a (x i)
          simp only [inv_nonneg, Nat.cast_nonneg]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          simp only [Nat.cast_pos, mul_nonneg_iff_of_pos_left, hn, hb]
        _ = b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      trans |(↑n)⁻¹ * ∑ k : Fin n, f a (x k)| + |∫ (x : Ω), f a (X x) ∂μ|
      · exact abs_sub ((↑n)⁻¹ * ∑ k : Fin n, f a (x k)) (∫ (x : Ω), f a (X x) ∂μ)
      · exact add_le_add s (s' a)
    rw [p0]
    refine Real.iSup_le ?_ ?_
    intro j
    have p' : |g j| - ⨆ i_1, |h i_1| ≤ |g j| - |h j| := by
      refine tsub_le_tsub_left ?_ |g j|
      suffices (abs ∘ h) j ≤ ⨆ i_1, (abs ∘ h) i_1 from by
        exact this
      apply le_ciSup
      rw [bddAbove_def]
      use b + b
      intro y
      simp only [Set.mem_range, Function.comp_apply, forall_exists_index]
      intro z hx
      rw [<- hx]
      have s0 : |(↑n)⁻¹ * ∑ k : Fin n, f z (Function.update x i x' k)| ≤ b := by
        calc
        _ = (↑n)⁻¹ * |∑ k : Fin n, f z (Function.update x i x' k)| := by
          rw [abs_mul]
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, |f z (Function.update x i x' k)| := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ f z (Function.update x i x' i_1)) Finset.univ
          simp only [inv_nonneg, Nat.cast_nonneg]
          refine Fintype.sum_nonneg ?_
          refine Pi.le_def.mpr ?_
          intro i
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, b := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.sum_le_sum fun i_1 a ↦ hf' z (Function.update x i x' i_1)
          simp only [inv_nonneg, Nat.cast_nonneg]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          simp only [Nat.cast_pos, mul_nonneg_iff_of_pos_left, hn, hb]
        _ = b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      trans |(↑n)⁻¹ * ∑ k : Fin n, f z (Function.update x i x' k)| + |∫ (x : Ω), f z (X x) ∂μ|
      · exact
        abs_sub ((↑n)⁻¹ * ∑ k : Fin n, f z (Function.update x i x' k)) (∫ (x : Ω), f z (X x) ∂μ)
      · exact add_le_add s0 (s' z)
    have p'' : |g j| - |h j| ≤ |g j - h j| := abs_sub_abs_le_abs_sub (g j) (h j)
    have p1 := p''' j
    linarith
    apply (mul_nonneg_iff_of_pos_left _).mpr hb
    apply Left.mul_pos (inv_pos_of_pos (Nat.cast_pos.mpr hn)) (by linarith)
  have p' : (⨆ i_1, |h i_1|) - ⨆ i, |g i| ≤ (↑n)⁻¹ * 2 * b := by
    have p0 : (⨆ i_1, |h i_1|) - ⨆ i, |g i| = ⨆ i_1, |h i_1| - ⨆ i, |g i| := by
      apply ciSup_sub
      rw [bddAbove_def]
      use b + b
      simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro z
      have s0 : |(↑n)⁻¹ * ∑ k : Fin n, f z (Function.update x i x' k)| ≤ b := by
        calc
        _ = (↑n)⁻¹ * |∑ k : Fin n, f z (Function.update x i x' k)| := by
          rw [abs_mul]
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, |f z (Function.update x i x' k)| := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.abs_sum_le_sum_abs (fun i_1 ↦ f z (Function.update x i x' i_1)) Finset.univ
          simp only [inv_nonneg, Nat.cast_nonneg]
          refine Fintype.sum_nonneg ?_
          refine Pi.le_def.mpr ?_
          intro i
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, b := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.sum_le_sum fun i_1 a ↦ hf' z (Function.update x i x' i_1)
          simp only [inv_nonneg, Nat.cast_nonneg]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          simp only [Nat.cast_pos, mul_nonneg_iff_of_pos_left, hn, hb]
        _ = b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      trans |(↑n)⁻¹ * ∑ k : Fin n, f z (Function.update x i x' k)| + |∫ (x : Ω), f z (X x) ∂μ|
      · exact abs_sub ((↑n)⁻¹ * ∑ k : Fin n, f z (Function.update x i x' k)) (∫ (x : Ω), f z (X x) ∂μ)
      · exact add_le_add s0 (s' z)
    rw [p0]
    refine Real.iSup_le ?_ ?_
    intro j
    have p' : |h j| - ⨆ i_1, |g i_1| ≤ |h j| - |g j| := by
      refine tsub_le_tsub_left ?_ |h j|
      suffices (abs ∘ g) j ≤ ⨆ i_1, (abs ∘ g) i_1 from by
        exact this
      apply le_ciSup
      rw [bddAbove_def]
      use b + b
      intro y
      simp only [Set.mem_range, Function.comp_apply, forall_exists_index]
      intro z hx
      rw [<- hx]
      have s : |(↑n)⁻¹ * ∑ k : Fin n, f z (x k)| ≤ b := by
        calc
        _ = (↑n)⁻¹ * |∑ k : Fin n, f z (x k)| := by
          rw [abs_mul]
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, |f z (x k)| := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.abs_sum_le_sum_abs (fun i ↦ f z (x i)) Finset.univ
          simp only [inv_nonneg, Nat.cast_nonneg]
          refine Fintype.sum_nonneg ?_
          refine Pi.le_def.mpr ?_
          intro i
          simp
        _ ≤ (↑n)⁻¹ * ∑ k : Fin n, b := by
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          apply Preorder.le_refl
          exact Finset.sum_le_sum fun i a_1 ↦ hf' z (x i)
          simp only [inv_nonneg, Nat.cast_nonneg]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          simp only [Nat.cast_pos, mul_nonneg_iff_of_pos_left, hn, hb]
        _ = b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      trans |(↑n)⁻¹ * ∑ k : Fin n, f z (x k)| + |∫ (x : Ω), f z (X x) ∂μ|
      · exact abs_sub ((↑n)⁻¹ * ∑ k : Fin n, f z (x k)) (∫ (x : Ω), f z (X x) ∂μ)
      · apply add_le_add s (s' z)
    have p'' : |h j| - |g j| ≤ |h j - g j| := abs_sub_abs_le_abs_sub (h j) (g j)
    have p1 : |h j - g j| ≤ (↑n)⁻¹ * 2 * b := by
      calc
      _ = |g j - h j| := abs_sub_comm (h j) (g j)
      _ ≤ (↑n)⁻¹ * 2 * b := p''' j
    linarith
    apply Left.mul_nonneg _ hb
    apply Left.mul_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg n)) (by linarith)
  apply abs_sub_le_iff.mpr ⟨p, p'⟩

theorem uniformDeviation_measurable [Countable ι] [MeasurableSpace Z]
    (X : Ω → Z) (hf : ∀ i, Measurable (f i)) :
    Measurable (uniformDeviation n f μ X) :=
  .iSup fun i ↦ ((measurable_const.mul (Finset.univ.measurable_sum fun j _ ↦
    (hf i).comp (measurable_pi_apply j))).add_const (-∫ (x : Ω), (fun ω' ↦ f i (X ω')) x ∂μ)).abs
