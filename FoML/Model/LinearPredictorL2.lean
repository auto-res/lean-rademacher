import Mathlib.Analysis.InnerProductSpace.PiL2
import FoML.Model.HilbertPredictor

open Real

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Linear prediction with both the weight and input restricted to closed Euclidean balls. -/
noncomputable def linearPredictorL2
    {d : ℕ} {W X : ℝ}
    (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) : ℝ :=
  ⟪(w : EuclideanSpace ℝ (Fin d)), (x : EuclideanSpace ℝ (Fin d))⟫

lemma continuous_linearPredictorL2_weight
    {d : ℕ} {W X : ℝ}
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    Continuous fun w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W ↦
      linearPredictorL2 w x := by
  unfold linearPredictorL2
  fun_prop

lemma continuous_linearPredictorL2_input
    {d : ℕ} {W X : ℝ}
    (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :
    Continuous fun x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X ↦
      linearPredictorL2 w x := by
  unfold linearPredictorL2
  fun_prop

/-- Pointwise boundedness needed by the generalization theorem. -/
lemma abs_linearPredictorL2_le
    {d : ℕ} {W X : ℝ} (hW : 0 ≤ W)
    (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
    (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    |linearPredictorL2 w x| ≤ X * W := by
  calc
    |linearPredictorL2 w x|
        ≤ ‖(w : EuclideanSpace ℝ (Fin d))‖ *
            ‖(x : EuclideanSpace ℝ (Fin d))‖ := by
          exact abs_real_inner_le_norm
            (w : EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    _ ≤ W * X := by
      apply mul_le_mul
      · exact mem_closedBall_zero_iff.mp w.property
      · exact mem_closedBall_zero_iff.mp x.property
      · exact norm_nonneg (x : EuclideanSpace ℝ (Fin d))
      · exact hW
    _ = X * W := mul_comm W X

/--
Sample-dependent empirical Rademacher-complexity bound for the full class of
`ℓ₂`-bounded linear predictors.
-/
theorem linear_predictor_l2_empirical_bound_of_sample
    (d n : ℕ) (W X : ℝ) (hW : 0 ≤ W)
    (S : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    empiricalRademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ) S
      ≤ W * (n : ℝ)⁻¹ *
        Real.sqrt
          (∑ k : Fin n, ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2) := by
  letI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W) :=
    (Metric.nonempty_closedBall.mpr hW).to_subtype
  change empiricalRademacherComplexity n
    (fun (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W)
        (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) ↦
      ⟪(w : EuclideanSpace ℝ (Fin d)), (x : EuclideanSpace ℝ (Fin d))⟫) S
      ≤ W * (n : ℝ)⁻¹ *
        Real.sqrt
          (∑ k : Fin n, ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2)
  rw [empiricalRademacherComplexity_comp]
  exact hilbertPredictor_empiricalRademacherComplexity_le
    (H := EuclideanSpace ℝ (Fin d)) W hW (Subtype.val ∘ S)

/--
Empirical Rademacher-complexity bound for the full class of `ℓ₂`-bounded
linear predictors on an `ℓ₂`-bounded input space.
-/
theorem linear_predictor_l2_empirical_bound
    (d n : ℕ) (W X : ℝ) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (S : Fin n → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X) :
    empiricalRademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ) S
      ≤ X * W / Real.sqrt (n : ℝ) := by
  calc
    empiricalRademacherComplexity n
        (linearPredictorL2 :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ) S ≤
        W * (n : ℝ)⁻¹ *
          Real.sqrt
            (∑ k : Fin n,
              ‖(S k : EuclideanSpace ℝ (Fin d))‖ ^ 2) :=
      linear_predictor_l2_empirical_bound_of_sample d n W X hW S
    _ ≤ W * (n : ℝ)⁻¹ * Real.sqrt (∑ _k : Fin n, X ^ 2) := by
      gcongr with k
      exact mem_closedBall_zero_iff.mp (S k).property
    _ = W * (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ) * X ^ 2) := by simp
    _ = W * (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) * X) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hX]
    _ = X * W / Real.sqrt (n : ℝ) := by
      by_cases hn : 0 < n
      · have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
        field_simp [hsqrt]
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp
