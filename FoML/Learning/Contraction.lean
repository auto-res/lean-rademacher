import FoML.Learning.Defs
import FoML.Rademacher.Signs

/-!
# A finite-class Rademacher contraction inequality

For the absolute empirical Rademacher complexity used in this project, a
Lipschitz map vanishing at zero costs a factor `2`.  The factor appears when
the absolute supremum is split into its positive and negative one-sided
parts.  For the one-sided convention the contraction lemma below has factor
`1`.

The implementation in this file treats finite hypothesis types.  This is
already useful for finite model selection and, unlike an assumption packaged
as a predicate, records a fully proved contraction principle.  Extensions to
general separable classes can be built by dense finite approximation.
-/

noncomputable section

universe u v

open Real
open scoped BigOperators

variable {H : Type u} {𝒳 : Type v}

private lemma two_iSup_contraction
    [Fintype H] [Nonempty H]
    (A x : H → ℝ) (ψ : ℝ → ℝ) {L : ℝ}
    (hψ : ∀ u v, |ψ u - ψ v| ≤ L * |u - v|) :
    (⨆ h, A h + ψ (x h)) + (⨆ h, A h - ψ (x h)) ≤
      (⨆ h, A h + L * x h) + (⨆ h, A h - L * x h) := by
  obtain ⟨h₁, hh₁⟩ :=
    exists_eq_ciSup_of_finite (f := fun h ↦ A h + ψ (x h))
  obtain ⟨h₂, hh₂⟩ :=
    exists_eq_ciSup_of_finite (f := fun h ↦ A h - ψ (x h))
  rw [← hh₁, ← hh₂]
  by_cases hx : x h₂ ≤ x h₁
  · have hdiff : ψ (x h₁) - ψ (x h₂) ≤ L * (x h₁ - x h₂) := by
      calc
        ψ (x h₁) - ψ (x h₂) ≤ |ψ (x h₁) - ψ (x h₂)| :=
          le_abs_self _
        _ ≤ L * |x h₁ - x h₂| := hψ _ _
        _ = L * (x h₁ - x h₂) := by rw [abs_of_nonneg (sub_nonneg.mpr hx)]
    calc
      (A h₁ + ψ (x h₁)) + (A h₂ - ψ (x h₂)) =
          A h₁ + A h₂ + (ψ (x h₁) - ψ (x h₂)) := by ring
      _ ≤ A h₁ + A h₂ + L * (x h₁ - x h₂) := by linarith
      _ = (A h₁ + L * x h₁) + (A h₂ - L * x h₂) := by ring
      _ ≤ (⨆ h, A h + L * x h) + (⨆ h, A h - L * x h) := by
        exact add_le_add
          (le_ciSup
            (f := fun h ↦ A h + L * x h) (Finite.bddAbove_range _) h₁)
          (le_ciSup
            (f := fun h ↦ A h - L * x h) (Finite.bddAbove_range _) h₂)
  · have hx' : x h₁ ≤ x h₂ := le_of_not_ge hx
    have hdiff : ψ (x h₁) - ψ (x h₂) ≤ L * (x h₂ - x h₁) := by
      calc
        ψ (x h₁) - ψ (x h₂) ≤ |ψ (x h₁) - ψ (x h₂)| :=
          le_abs_self _
        _ ≤ L * |x h₁ - x h₂| := hψ _ _
        _ = L * (x h₂ - x h₁) := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hx')]
    calc
      (A h₁ + ψ (x h₁)) + (A h₂ - ψ (x h₂)) =
          A h₁ + A h₂ + (ψ (x h₁) - ψ (x h₂)) := by ring
      _ ≤ A h₁ + A h₂ + L * (x h₂ - x h₁) := by linarith
      _ = (A h₂ + L * x h₂) + (A h₁ - L * x h₁) := by ring
      _ ≤ (⨆ h, A h + L * x h) + (⨆ h, A h - L * x h) := by
        exact add_le_add
          (le_ciSup
            (f := fun h ↦ A h + L * x h) (Finite.bddAbove_range _) h₂)
          (le_ciSup
            (f := fun h ↦ A h - L * x h) (Finite.bddAbove_range _) h₁)

/--
The finite-sign, one-sided contraction principle, strengthened by an arbitrary
offset `c`.  The offset is what makes induction over the sample coordinates
possible.
-/
private theorem sum_iSup_contraction_one_sided
    [Fintype H] [Nonempty H]
    (n : ℕ) (a : H → Fin n → ℝ) (ψ : Fin n → ℝ → ℝ)
    (c : H → ℝ) {L : ℝ}
    (hψ : ∀ k u v, |ψ k u - ψ k v| ≤ L * |u - v|) :
    (∑ σ : Signs n,
        ⨆ h, c h + ∑ k : Fin n, (σ k : ℝ) * ψ k (a h k)) ≤
      ∑ σ : Signs n,
        ⨆ h, c h + L * ∑ k : Fin n, (σ k : ℝ) * a h k := by
  induction n generalizing c with
  | zero =>
      simp
  | succ m ih =>
      let a₀ : H → Fin m → ℝ := fun h k ↦ a h k.castSucc
      let ψ₀ : Fin m → ℝ → ℝ := fun k ↦ ψ k.castSucc
      let x : H → ℝ := fun h ↦ a h (Fin.last m)
      have hψ₀ : ∀ k u v, |ψ₀ k u - ψ₀ k v| ≤ L * |u - v| :=
        fun k u v ↦ hψ k.castSucc u v
      have hlast :
          ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    ψ (Fin.last m) (x h)) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    ψ (Fin.last m) (x h))) ≤
            ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    L * x h) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    L * x h)) := by
        apply Finset.sum_le_sum
        intro τ _
        let A : H → ℝ :=
          fun h ↦ c h + ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)
        simpa [A, add_assoc] using
          two_iSup_contraction A x (ψ (Fin.last m))
            (hψ (Fin.last m))
      have hminus :=
        ih (a := a₀) (ψ := ψ₀) (c := fun h ↦ c h - L * x h) hψ₀
      have hplus :=
        ih (a := a₀) (ψ := ψ₀) (c := fun h ↦ c h + L * x h) hψ₀
      let q : ℤ → Signs m → ℝ :=
        fun s τ ↦
          ⨆ h,
            c h +
              ((∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                (s : ℝ) * ψ (Fin.last m) (x h))
      let qL : ℤ → Signs m → ℝ :=
        fun s τ ↦
          ⨆ h,
            c h +
              L *
                ((∑ k : Fin m, (τ k : ℝ) * a₀ h k) +
                  (s : ℝ) * x h)
      calc
        (∑ σ : Signs (m + 1),
            ⨆ h, c h + ∑ k : Fin (m + 1),
              (σ k : ℝ) * ψ k (a h k)) =
          ∑ σ : Signs (m + 1), q (σ (Fin.last m)) (Fin.init σ) := by
              apply Finset.sum_congr rfl
              intro σ _
              dsimp only [q]
              apply congrArg
              funext h
              rw [Fin.sum_univ_castSucc]
              rfl
        _ =
          ∑ s ∈ ({-1, 1} : Finset ℤ), ∑ τ : Signs m,
              ⨆ h,
                c h +
                  ((∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    (s : ℝ) * ψ (Fin.last m) (x h)) := by
              exact (sigma_eq (n := m) q).symm
        _ =
            ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    ψ (Fin.last m) (x h)) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    ψ (Fin.last m) (x h))) := by
              simp [Finset.sum_add_distrib, add_comm, add_left_comm]
              apply Finset.sum_congr rfl
              intro τ _
              apply congrArg
              funext h
              ring
        _ ≤ ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    L * x h) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    L * x h)) := by
              simpa [add_comm] using hlast
        _ = (∑ τ : Signs m,
              ⨆ h,
                (c h - L * x h) +
                  ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
            ∑ τ : Signs m,
              ⨆ h,
                (c h + L * x h) +
                  ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k) := by
              simp only [Finset.sum_add_distrib]
              congr 1 <;> apply Finset.sum_congr rfl <;> intro τ _ <;>
                apply congrArg <;> funext h <;> ring
        _ ≤ (∑ τ : Signs m,
              ⨆ h,
                (c h - L * x h) +
                  L * ∑ k : Fin m, (τ k : ℝ) * a₀ h k) +
            ∑ τ : Signs m,
              ⨆ h,
                (c h + L * x h) +
                  L * ∑ k : Fin m, (τ k : ℝ) * a₀ h k :=
              add_le_add hminus hplus
        _ = ∑ s ∈ ({-1, 1} : Finset ℤ), ∑ τ : Signs m,
              ⨆ h,
                c h +
                  L *
                    ((∑ k : Fin m, (τ k : ℝ) * a₀ h k) +
                      (s : ℝ) * x h) := by
              simp [add_comm, add_assoc]
              congr 1 <;> apply Finset.sum_congr rfl <;> intro τ _ <;>
                apply congrArg <;> funext h <;> ring
        _ = ∑ σ : Signs (m + 1), qL (σ (Fin.last m)) (Fin.init σ) :=
              sigma_eq (n := m) qL
        _ = ∑ σ : Signs (m + 1),
              ⨆ h, c h + L * ∑ k : Fin (m + 1),
                (σ k : ℝ) * a h k := by
              apply Finset.sum_congr rfl
              intro σ _
              dsimp only [qL]
              apply congrArg
              funext h
              rw [Fin.sum_univ_castSucc]
              rfl

/--
One-sided empirical Rademacher contraction for a finite hypothesis class.

Unlike the absolute convention, the one-sided convention has constant `L`.
The map may depend on the observation `x`; this is useful for supervised
losses, where the contraction map depends on the observed label.
-/
theorem empiricalRademacherComplexity_without_abs_contraction_finite
    [Fintype H] [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (ψ : 𝒳 → ℝ → ℝ)
    (S : Fin n → 𝒳) {L : ℝ} (hL : 0 ≤ L)
    (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ L * |u - v|) :
    empiricalRademacherComplexity_without_abs n
        (fun h x ↦ ψ x (F h x)) S ≤
      L * empiricalRademacherComplexity_without_abs n F S := by
  let q : ℝ := (n : ℝ)⁻¹
  have hq : 0 ≤ q := by positivity
  have hcontract :=
    sum_iSup_contraction_one_sided n
      (fun h k ↦ F h (S k))
      (fun k u ↦ q * ψ (S k) u)
      (fun _ ↦ 0) (by
        intro k u v
        rw [← mul_sub, abs_mul, abs_of_nonneg hq]
        calc
          q * |ψ (S k) u - ψ (S k) v| ≤
              q * (L * |u - v|) := by
            gcongr
            exact hψ (S k) u v
          _ = (q * L) * |u - v| := by ring)
  dsimp only [empiricalRademacherComplexity_without_abs]
  calc
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        (∑ σ : Signs n,
        ⨆ h, (n : ℝ)⁻¹ *
          ∑ k : Fin n, (σ k : ℝ) * ψ (S k) (F h (S k))) =
      (Fintype.card (Signs n) : ℝ)⁻¹ *
        (∑ σ : Signs n,
          ⨆ h, (0 : ℝ) +
            ∑ k : Fin n, (σ k : ℝ) *
              (q * ψ (S k) (F h (S k)))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro σ _
        apply congrArg
        funext h
        simp only [zero_add, q]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
        (∑ σ : Signs n,
          ⨆ h, (0 : ℝ) + (q * L) *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)) :=
      mul_le_mul_of_nonneg_left hcontract (by positivity)
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
        (L * ∑ σ : Signs n,
          ⨆ h, (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      obtain ⟨hmax, hhmax⟩ :=
        exists_eq_ciSup_of_finite
          (f := fun h ↦ (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k))
      apply le_antisymm
      · apply ciSup_le
        intro h
        calc
          0 + (q * L) * ∑ k : Fin n, (σ k : ℝ) * F h (S k) =
              L * ((n : ℝ)⁻¹ *
                ∑ k : Fin n, (σ k : ℝ) * F h (S k)) := by
            simp only [zero_add, q]
            ring
          _ ≤ L * (⨆ h, (n : ℝ)⁻¹ *
                ∑ k : Fin n, (σ k : ℝ) * F h (S k)) := by
            gcongr
            exact le_ciSup
              (f := fun h ↦ (n : ℝ)⁻¹ *
                ∑ k : Fin n, (σ k : ℝ) * F h (S k))
              (Finite.bddAbove_range _) h
      · rw [← hhmax]
        calc
          L * ((n : ℝ)⁻¹ *
              ∑ k : Fin n, (σ k : ℝ) * F hmax (S k)) =
              0 + (q * L) *
                ∑ k : Fin n, (σ k : ℝ) * F hmax (S k) := by
            simp only [zero_add, q]
            ring
          _ ≤ ⨆ h, 0 + (q * L) *
              ∑ k : Fin n, (σ k : ℝ) * F h (S k) :=
            le_ciSup
              (f := fun h ↦ 0 + (q * L) *
                ∑ k : Fin n, (σ k : ℝ) * F h (S k))
              (Finite.bddAbove_range _) hmax
    _ = L * ((Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n,
          ⨆ h, (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)) := by ring

/-- Add a zero function to a function class. -/
def withZeroClass (F : H → 𝒳 → ℝ) : Option H → 𝒳 → ℝ
  | none, _ => 0
  | some h, x => F h x

private lemma empiricalRademacherComplexity_le_pos_add_neg
    [Fintype H] [Nonempty H]
    (n : ℕ) (G : H → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n G S ≤
      empiricalRademacherComplexity_without_abs n (withZeroClass G) S +
      empiricalRademacherComplexity_without_abs n
        (fun oh x ↦ -withZeroClass G oh x) S := by
  dsimp only [empiricalRademacherComplexity,
    empiricalRademacherComplexity_without_abs]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro σ _
  let A : H → ℝ :=
    fun h ↦ (n : ℝ)⁻¹ *
      ∑ k : Fin n, (σ k : ℝ) * G h (S k)
  let B : Option H → ℝ
    | none => 0
    | some h => A h
  have hneg :
      (fun oh : Option H ↦
        (n : ℝ)⁻¹ * ∑ k : Fin n,
          (σ k : ℝ) * -withZeroClass G oh (S k)) = fun oh ↦ -B oh := by
    funext oh
    cases oh <;> simp [B, A, withZeroClass, Finset.sum_neg_distrib]
  have hpos :
      (fun oh : Option H ↦
        (n : ℝ)⁻¹ * ∑ k : Fin n,
          (σ k : ℝ) * withZeroClass G oh (S k)) = B := by
    funext oh
    cases oh <;> simp [B, A, withZeroClass]
  rw [hpos, hneg]
  apply ciSup_le
  intro h
  rw [abs_eq_max_neg]
  apply max_le
  · calc
      A h ≤ ⨆ oh, B oh :=
        le_ciSup (f := B) (Finite.bddAbove_range _) (some h)
      _ ≤ (⨆ oh, B oh) + ⨆ oh, -B oh := by
        have hz : 0 ≤ ⨆ oh, -B oh := by
          have : (0 : ℝ) = -B none := by simp [B]
          rw [this]
          exact le_ciSup (f := fun oh ↦ -B oh)
            (Finite.bddAbove_range _) none
        linarith
  · calc
      -A h ≤ ⨆ oh, -B oh :=
        le_ciSup (f := fun oh ↦ -B oh)
          (Finite.bddAbove_range _) (some h)
      _ ≤ (⨆ oh, B oh) + ⨆ oh, -B oh := by
        have hz : 0 ≤ ⨆ oh, B oh := by
          have : (0 : ℝ) = B none := by simp [B]
          rw [this]
          exact le_ciSup (f := B) (Finite.bddAbove_range _) none
        linarith

private lemma empiricalRademacherComplexity_without_abs_withZero_le
    [Fintype H] [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (withZeroClass F) S ≤
      empiricalRademacherComplexity n F S := by
  dsimp only [empiricalRademacherComplexity_without_abs,
    empiricalRademacherComplexity]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro σ _
  apply ciSup_le
  intro oh
  cases oh with
  | none =>
      simp only [withZeroClass, mul_zero, Finset.sum_const_zero, mul_zero]
      exact Real.iSup_nonneg fun h ↦
        abs_nonneg ((n : ℝ)⁻¹ *
          ∑ k : Fin n, (σ k : ℝ) * F h (S k))
  | some h =>
      calc
        (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * withZeroClass F (some h) (S k) =
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k) := by
          rfl
        _ ≤ |(n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)| :=
          le_abs_self _
        _ ≤ ⨆ h, |(n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)| :=
          le_ciSup
            (f := fun h ↦ |(n : ℝ)⁻¹ *
              ∑ k : Fin n, (σ k : ℝ) * F h (S k)|)
            (Finite.bddAbove_range _) h

/--
Absolute empirical Rademacher contraction for a finite hypothesis class.

Because `empiricalRademacherComplexity` takes an absolute value inside the
hypothesis supremum, the general Lipschitz contraction constant is `2 * L`.
For the one-sided definition, use
`empiricalRademacherComplexity_without_abs_contraction_finite`, whose constant
is `L`.
-/
theorem empiricalRademacherComplexity_contraction_finite
    [Fintype H] [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (ψ : 𝒳 → ℝ → ℝ)
    (S : Fin n → 𝒳) {L : ℝ} (hL : 0 ≤ L)
    (hψ_zero : ∀ x, ψ x 0 = 0)
    (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (fun h x ↦ ψ x (F h x)) S ≤
      2 * L * empiricalRademacherComplexity n F S := by
  let G : H → 𝒳 → ℝ := fun h x ↦ ψ x (F h x)
  have hsplit :=
    empiricalRademacherComplexity_le_pos_add_neg n G S
  have hpos :
      empiricalRademacherComplexity_without_abs n (withZeroClass G) S ≤
        L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S := by
    have hclass :
        (fun oh x ↦ ψ x (withZeroClass F oh x)) = withZeroClass G := by
      funext oh x
      cases oh <;> simp [withZeroClass, G, hψ_zero]
    rw [← hclass]
    exact empiricalRademacherComplexity_without_abs_contraction_finite
      n (withZeroClass F) ψ S hL hψ
  have hneg :
      empiricalRademacherComplexity_without_abs n
          (fun oh x ↦ -withZeroClass G oh x) S ≤
        L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S := by
    let ψneg : 𝒳 → ℝ → ℝ := fun x u ↦ -ψ x u
    have hψneg : ∀ x u v, |ψneg x u - ψneg x v| ≤ L * |u - v| := by
      intro x u v
      change |-ψ x u - -ψ x v| ≤ L * |u - v|
      rw [show -ψ x u - -ψ x v = -(ψ x u - ψ x v) by ring, abs_neg]
      exact hψ x u v
    have hclass :
        (fun oh x ↦ ψneg x (withZeroClass F oh x)) =
          fun oh x ↦ -withZeroClass G oh x := by
      funext oh x
      cases oh <;> simp [withZeroClass, G, ψneg, hψ_zero]
    rw [← hclass]
    exact empiricalRademacherComplexity_without_abs_contraction_finite
      n (withZeroClass F) ψneg S hL hψneg
  have hraw :=
    empiricalRademacherComplexity_without_abs_withZero_le n F S
  calc
    empiricalRademacherComplexity n G S ≤
        empiricalRademacherComplexity_without_abs n (withZeroClass G) S +
          empiricalRademacherComplexity_without_abs n
            (fun oh x ↦ -withZeroClass G oh x) S :=
      hsplit
    _ ≤ L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S +
        L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S :=
      add_le_add hpos hneg
    _ ≤ L * empiricalRademacherComplexity n F S +
        L * empiricalRademacherComplexity n F S := by
      gcongr
    _ = 2 * L * empiricalRademacherComplexity n F S := by ring

/--
Contraction for a centered supervised loss class over a finite hypothesis
type.  The loss is centered by subtracting `loss 0 y`, so the contraction map
vanishes at zero.
-/
theorem empiricalRademacherComplexity_centered_supervisedLossClass_le
    {𝒴 : Type*}
    [Fintype H] [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (loss : ℝ → 𝒴 → ℝ)
    (S : Fin n → 𝒳 × 𝒴) {L : ℝ} (hL : 0 ≤ L)
    (hloss : ∀ y u v, |loss u y - loss v y| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (supervisedLossClass F (centeredLoss loss)) S ≤
      2 * L *
        empiricalRademacherComplexity n
          (fun (h : H) (z : 𝒳 × 𝒴) ↦ F h z.1) S := by
  apply empiricalRademacherComplexity_contraction_finite
    n (fun (h : H) (z : 𝒳 × 𝒴) ↦ F h z.1)
      (fun z u ↦ centeredLoss loss u z.2) S hL
  · intro z
    exact centeredLoss_zero loss z.2
  · intro z u v
    simpa [centeredLoss, sub_sub_sub_cancel_right] using hloss z.2 u v

end
