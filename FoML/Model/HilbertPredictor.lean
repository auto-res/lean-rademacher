import Mathlib.Analysis.InnerProductSpace.Basic
import FoML.Rademacher.Signs

/-!
# Linear predictors on a real inner-product space

This module contains the dimension-free argument underlying the Rademacher
estimate for Euclidean linear classes and feature-map kernel classes.  The
fixed-sample theorem requires an inner-product space, but neither completeness
nor finite dimensionality.
-/

noncomputable section

universe u

open Real

variable {n : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Linear prediction by a weight in a closed ball of a real inner-product space. -/
noncomputable def hilbertPredictor
    {Λ : ℝ} (w : Metric.closedBall (0 : H) Λ) (x : H) : ℝ :=
  ⟪(w : H), x⟫

/-- Continuity of a Hilbert predictor in its weight. -/
lemma continuous_hilbertPredictor_weight
    {Λ : ℝ} (x : H) :
    Continuous fun w : Metric.closedBall (0 : H) Λ ↦
      hilbertPredictor w x := by
  unfold hilbertPredictor
  fun_prop

/-- Continuity of a Hilbert predictor in its input. -/
lemma continuous_hilbertPredictor_input
    {Λ : ℝ} (w : Metric.closedBall (0 : H) Λ) :
    Continuous fun x : H ↦ hilbertPredictor w x := by
  unfold hilbertPredictor
  fun_prop

/-- Cauchy--Schwarz together with the weight-radius constraint. -/
lemma abs_hilbertPredictor_le
    {Λ : ℝ}
    (w : Metric.closedBall (0 : H) Λ) (x : H) :
    |hilbertPredictor w x| ≤ Λ * ‖x‖ := by
  calc
    |hilbertPredictor w x| ≤ ‖(w : H)‖ * ‖x‖ :=
      abs_real_inner_le_norm (w : H) x
    _ ≤ Λ * ‖x‖ := by
      gcongr
      exact mem_closedBall_zero_iff.mp w.property

private lemma rademacher_sum_norm_sq_average
    (Y : Fin n → H) :
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 =
      ∑ k : Fin n, ‖Y k‖ ^ 2 := by
  let A : Signs n → Fin n → Fin n → ℝ :=
    fun σ k l ↦ (σ k : ℝ) * (σ l : ℝ) * ⟪Y k, Y l⟫
  have hexpand : ∀ σ : Signs n,
      ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 =
        ∑ k : Fin n, ∑ l : Fin n, A σ k l := by
    intro σ
    calc
      ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 =
          ⟪∑ k : Fin n, (σ k : ℝ) • Y k,
            ∑ l : Fin n, (σ l : ℝ) • Y l⟫ := by
        symm
        exact real_inner_self_eq_norm_sq _
      _ = ∑ k : Fin n,
          ⟪(σ k : ℝ) • Y k,
            ∑ l : Fin n, (σ l : ℝ) • Y l⟫ := by
        rw [sum_inner]
      _ = ∑ k : Fin n, ∑ l : Fin n,
          ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [inner_sum]
      _ = ∑ k : Fin n, ∑ l : Fin n, A σ k l := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        simp only [A, real_inner_smul_left, real_inner_smul_right]
        ring
  have hsign : ∀ k l : Fin n,
      ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) =
        if k = l then (Fintype.card (Signs n) : ℝ) else 0 := by
    intro k l
    by_cases hkl : k = l
    · subst l
      have hdiag :
          ∑ σ : Signs n, (σ k : ℝ) * (σ k : ℝ) =
            (Fintype.card (Signs n) : ℝ) := by
        calc
          ∑ σ : Signs n, (σ k : ℝ) * (σ k : ℝ) =
              ∑ _σ : Signs n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [← pow_two]
            calc
              (σ k : ℝ) ^ 2 = |(σ k : ℝ)| ^ 2 := (sq_abs _).symm
              _ = 1 := by rw [abs_sigma]; norm_num
          _ = Fintype.card (Signs n) := by simp
      simpa using hdiag
    · simpa [hkl] using rademacher_orthogonality n k l hkl
  calc
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 =
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ∑ k : Fin n, ∑ l : Fin n, A σ k l := by
      apply congrArg
      exact Finset.sum_congr rfl fun σ _ ↦ hexpand σ
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Signs n, A σ k l := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ k : Fin n, ∑ l : Fin n,
            (if k = l then (Fintype.card (Signs n) : ℝ) else 0) *
              ⟪Y k, Y l⟫ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [A]
      rw [← Finset.sum_mul]
      rw [hsign k l]
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ) *
            ∑ k : Fin n, ‖Y k‖ ^ 2) := by
      apply congrArg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hlk
        simp [Ne.symm hlk]
      · simp
    _ = ∑ k : Fin n, ‖Y k‖ ^ 2 := by simp

private lemma rademacher_sum_norm_average_le
    (Y : Fin n → H) :
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ≤
      Real.sqrt (∑ k : Fin n, ‖Y k‖ ^ 2) := by
  have hmean :
      (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ≤
        Real.sqrt
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2) := by
    apply le_sqrt_of_sq_le
    let f : Signs n → ℝ := fun _ ↦ 1
    let g : Signs n → ℝ := fun σ ↦
      ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ *
        (Fintype.card (Signs n) : ℝ)⁻¹
    suffices
        (∑ σ : Signs n, f σ * g σ) ^ 2 ≤
          (∑ σ : Signs n, f σ ^ 2) *
            ∑ σ : Signs n, g σ ^ 2 from by
      dsimp only [f, g] at this
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at this
      have p :
          (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ =
            ∑ σ : Signs n,
              ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ *
                (Fintype.card (Signs n) : ℝ)⁻¹ := by
        rw [mul_comm, Finset.sum_mul]
      have q :
          (Fintype.card (Signs n) : ℝ) *
              ∑ σ : Signs n,
                (‖∑ k : Fin n, (σ k : ℝ) • Y k‖ *
                  (Fintype.card (Signs n) : ℝ)⁻¹) ^ 2 =
            (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 := by
        calc
          _ = (Fintype.card (Signs n) : ℝ) *
              ∑ σ : Signs n,
                (‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 *
                  ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) := by
            congr 2
            ext σ
            ring
          _ = (Fintype.card (Signs n) : ℝ) *
              ((∑ σ : Signs n,
                  ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2) *
                ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) := by
            congr 1
            rw [Finset.sum_mul]
          _ = _ := by
            have hcard :
                (Fintype.card (Signs n) : ℝ) ≠ 0 := by
              rw [Signs.card]
              positivity
            field_simp [hcard]
      rw [p, ← q]
      exact this
    exact Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset (Signs n))) f g
  calc
    _ ≤ Real.sqrt
        ((Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2) :=
      hmean
    _ = Real.sqrt (∑ k : Fin n, ‖Y k‖ ^ 2) := by
      rw [rademacher_sum_norm_sq_average Y]

/--
Dimension-free, sample-dependent empirical Rademacher estimate for the full
closed ball of Hilbert predictors:

`Rhatₙ ≤ Λ / n * sqrt (∑ₖ ‖Sₖ‖²)`.

This fixed-sample result needs only a real inner-product space.  In particular,
completeness is not used.
-/
theorem hilbertPredictor_empiricalRademacherComplexity_le
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (S : Fin n → H) :
    empiricalRademacherComplexity n
        (hilbertPredictor :
          Metric.closedBall (0 : H) Λ → H → ℝ) S ≤
      Λ * (n : ℝ)⁻¹ *
        Real.sqrt (∑ k : Fin n, ‖S k‖ ^ 2) := by
  letI : Nonempty (Metric.closedBall (0 : H) Λ) :=
    (Metric.nonempty_closedBall.mpr hΛ).to_subtype
  calc
    empiricalRademacherComplexity n
        (hilbertPredictor :
          Metric.closedBall (0 : H) Λ → H → ℝ) S =
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ w : Metric.closedBall (0 : H) Λ,
            |(n : ℝ)⁻¹ *
              ∑ k : Fin n, (σ k : ℝ) * ⟪(w : H), S k⟫| := rfl
    _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n,
            (n : ℝ)⁻¹ * (Λ *
              ‖∑ k : Fin n, (σ k : ℝ) • S k‖) := by
      gcongr with σ
      apply ciSup_le
      intro w
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      have hinner :
          ∑ k : Fin n, (σ k : ℝ) * ⟪(w : H), S k⟫ =
            ⟪(w : H), ∑ k : Fin n, (σ k : ℝ) • S k⟫ := by
        rw [inner_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [real_inner_smul_right]
      rw [hinner]
      gcongr
      exact abs_hilbertPredictor_le w
        (∑ k : Fin n, (σ k : ℝ) • S k)
    _ = Λ * (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n,
              ‖∑ k : Fin n, (σ k : ℝ) • S k‖) := by
      rw [← Finset.mul_sum]
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum]
      ring
    _ ≤ Λ * (n : ℝ)⁻¹ *
          Real.sqrt (∑ k : Fin n, ‖S k‖ ^ 2) := by
      gcongr
      exact rademacher_sum_norm_average_le S

end
