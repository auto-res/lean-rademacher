import FoML.Model.HilbertPredictor

/-!
# Feature-map kernels and RKHS predictor bounds

Mathlib does not currently provide a construction of the RKHS associated with
an arbitrary positive-semidefinite kernel.  This module therefore starts with
a feature map `Φ : 𝒳 → H` into a real Hilbert space and uses the induced kernel

`K(x,y) = ⟪Φ x, Φ y⟫`.

This is exactly the representation used in the proof of Mohri, Rostamizadeh,
and Talwalkar, *Foundations of Machine Learning*, Theorem 6.12.
-/

noncomputable section

universe u v

open Real

variable {n : ℕ}
variable {𝒳 : Type u}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The kernel induced by a feature map into a real inner-product space. -/
noncomputable def kernelOfFeatureMap (Φ : 𝒳 → H) (x y : 𝒳) : ℝ :=
  ⟪Φ x, Φ y⟫

/-- The diagonal of a feature-map kernel is the squared feature norm. -/
@[simp]
lemma kernelOfFeatureMap_self
    (Φ : 𝒳 → H) (x : 𝒳) :
    kernelOfFeatureMap Φ x x = ‖Φ x‖ ^ 2 := by
  exact real_inner_self_eq_norm_sq _

/--
A feature-map kernel is positive semidefinite: every finite Gram quadratic
form is nonnegative.
-/
theorem kernelOfFeatureMap_positiveSemidefinite
    (Φ : 𝒳 → H) {m : ℕ} (x : Fin m → 𝒳) (a : Fin m → ℝ) :
    0 ≤ ∑ i : Fin m, ∑ j : Fin m,
      a i * a j * kernelOfFeatureMap Φ (x i) (x j) := by
  have hgram :
      ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * kernelOfFeatureMap Φ (x i) (x j) =
        ‖∑ i : Fin m, a i • Φ (x i)‖ ^ 2 := by
    calc
      ∑ i : Fin m, ∑ j : Fin m,
          a i * a j * kernelOfFeatureMap Φ (x i) (x j) =
          ∑ i : Fin m, ∑ j : Fin m,
            ⟪a i • Φ (x i), a j • Φ (x j)⟫ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [kernelOfFeatureMap, real_inner_smul_left,
          real_inner_smul_right]
        ring
      _ = ⟪∑ i : Fin m, a i • Φ (x i),
          ∑ j : Fin m, a j • Φ (x j)⟫ := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_sum]
      _ = ‖∑ i : Fin m, a i • Φ (x i)‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
  rw [hgram]
  positivity

/-- The diagonal kernel trace of a sample. -/
noncomputable def kernelTrace
    (Φ : 𝒳 → H) (S : Fin n → 𝒳) : ℝ :=
  ∑ k : Fin n, kernelOfFeatureMap Φ (S k) (S k)

@[simp]
lemma kernelTrace_eq_sum_norm_sq
    (Φ : 𝒳 → H) (S : Fin n → 𝒳) :
    kernelTrace Φ S = ∑ k : Fin n, ‖Φ (S k)‖ ^ 2 := by
  simp [kernelTrace]

/-- Prediction by a bounded Hilbert-space weight after applying a feature map. -/
noncomputable def rkhsPredictor
    (Φ : 𝒳 → H) {Λ : ℝ}
    (w : Metric.closedBall (0 : H) Λ) (x : 𝒳) : ℝ :=
  hilbertPredictor w (Φ x)

/-- Continuity of the feature-map predictor in its weight. -/
lemma continuous_rkhsPredictor_weight
    (Φ : 𝒳 → H) {Λ : ℝ} (x : 𝒳) :
    Continuous fun w : Metric.closedBall (0 : H) Λ ↦
      rkhsPredictor Φ w x :=
  continuous_hilbertPredictor_weight (Φ x)

/-- Measurability in the input follows from measurability of the feature map. -/
lemma measurable_rkhsPredictor_input
    [MeasurableSpace 𝒳] [MeasurableSpace H] [BorelSpace H]
    (Φ : 𝒳 → H) (hΦ : Measurable Φ) {Λ : ℝ}
    (w : Metric.closedBall (0 : H) Λ) :
    Measurable fun x ↦ rkhsPredictor Φ w x :=
  (continuous_hilbertPredictor_input w).measurable.comp hΦ

/-- A diagonal kernel bound implies the corresponding feature-norm bound. -/
lemma norm_featureMap_le_of_kernel_self_le
    (Φ : 𝒳 → H) {r : ℝ} (hr : 0 ≤ r) {x : 𝒳}
    (hx : kernelOfFeatureMap Φ x x ≤ r ^ 2) :
    ‖Φ x‖ ≤ r := by
  rw [kernelOfFeatureMap_self] at hx
  exact (sq_le_sq₀ (norm_nonneg _) hr).mp hx

/-- Pointwise boundedness obtained from the weight and kernel-diagonal bounds. -/
lemma abs_rkhsPredictor_le
    (Φ : 𝒳 → H) {Λ r : ℝ} (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (w : Metric.closedBall (0 : H) Λ) (x : 𝒳) :
    |rkhsPredictor Φ w x| ≤ r * Λ := by
  calc
    |rkhsPredictor Φ w x| ≤ Λ * ‖Φ x‖ :=
      abs_hilbertPredictor_le w (Φ x)
    _ ≤ Λ * r := by
      gcongr
      exact norm_featureMap_le_of_kernel_self_le Φ hr (hdiag x)
    _ = r * Λ := mul_comm _ _

/--
Mohri, Rostamizadeh, and Talwalkar, Theorem 6.12, in kernel-trace form:

`Rhatₙ ≤ Λ / n * sqrt (∑ₖ K(Sₖ,Sₖ))`.

The feature space is assumed complete here to match the Hilbert/RKHS
interpretation.  The underlying dimension-free theorem in
`FoML.Model.HilbertPredictor` does not require completeness.
-/
theorem rkhs_empiricalRademacherComplexity_le_kernelTrace
    [CompleteSpace H]
    (Φ : 𝒳 → H) (Λ : ℝ) (hΛ : 0 ≤ Λ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) S ≤
      Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S) := by
  change empiricalRademacherComplexity n
      (fun w x ↦ hilbertPredictor w (Φ x)) S ≤
    Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S)
  rw [empiricalRademacherComplexity_comp]
  simpa using
    hilbertPredictor_empiricalRademacherComplexity_le
      Λ hΛ (Φ ∘ S)

/--
Uniform-diagonal form of Mohri et al., Theorem 6.12:

if `K(x,x) ≤ r²`, then `Rhatₙ ≤ r Λ / √n`.
-/
theorem rkhs_empiricalRademacherComplexity_le
    [CompleteSpace H]
    (Φ : 𝒳 → H) (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r)
    (hdiag : ∀ x, kernelOfFeatureMap Φ x x ≤ r ^ 2)
    (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) S ≤
      r * Λ / Real.sqrt (n : ℝ) := by
  calc
    empiricalRademacherComplexity n
        (rkhsPredictor Φ :
          Metric.closedBall (0 : H) Λ → 𝒳 → ℝ) S ≤
        Λ * (n : ℝ)⁻¹ * Real.sqrt (kernelTrace Φ S) :=
      rkhs_empiricalRademacherComplexity_le_kernelTrace Φ Λ hΛ S
    _ ≤ Λ * (n : ℝ)⁻¹ *
        Real.sqrt (∑ _k : Fin n, r ^ 2) := by
      rw [kernelTrace_eq_sum_norm_sq]
      gcongr with k
      exact norm_featureMap_le_of_kernel_self_le Φ hr (hdiag (S k))
    _ = Λ * (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ) * r ^ 2) := by simp
    _ = Λ * (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) * r) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hr]
    _ = r * Λ / Real.sqrt (n : ℝ) := by
      by_cases hn : 0 < n
      · have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
        field_simp [hsqrt]
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp

end
