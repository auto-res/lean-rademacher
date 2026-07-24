import FoML.Entropy.Dudley

/-!
# Explicit Dudley bounds for finite classes

For a class indexed by a finite type `H`, the sign-symmetrized empirical
function space has at most `2 * card H` elements.  Substituting this elementary
cover into Dudley's entropy integral removes `coveringNumber` from the final
estimate.
-/

noncomputable section

universe u v

open MeasureTheory Real

variable {n : ℕ} {H : Type u} {𝒳 : Type v}

/--
The sign-symmetrized empirical class has covering number at most `2 * |H|`.
-/
theorem coveringNumber_signSymmetrization_le_two_mul_card
    [Fintype H] [Nonempty H]
    (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) {ε : ℝ} (hε : 0 < ε) :
    coveringNumber
        (signSymmetrization_totallyBounded
          (F := F) (S := S) empiricalFunctionSpace_totallyBounded) ε ≤
      2 * Fintype.card H := by
  calc
    coveringNumber
        (signSymmetrization_totallyBounded
          (F := F) (S := S) empiricalFunctionSpace_totallyBounded) ε ≤
        Fintype.card
          (EmpiricalFunctionSpace (signSymmetrization F) S) :=
      coveringNumber_le_fintype_card _ hε
    _ = Fintype.card (H × Bool) := card_empiricalFunctionSpace
    _ = 2 * Fintype.card H := by simp [mul_comm]

/--
The explicit finite-class Dudley expression

`4α + (12 / √n) * (c/2 - α) * √(log (2|H|))`.
-/
noncomputable def finiteClassDudleyEstimate
    (n card : ℕ) (α c : ℝ) : ℝ :=
  4 * α + (12 / Real.sqrt n) * (c / 2 - α) *
    Real.sqrt (Real.log (2 * card))

private lemma finiteClass_entropy_integral_le
    [Fintype H] [Nonempty H]
    (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳)
    {α c : ℝ} (hα : 0 < α) (hαc : α < c / 2) :
    (∫ x : ℝ in α..(c / 2),
      Real.sqrt (Real.log (coveringNumber
        (signSymmetrization_totallyBounded
          (F := F) (S := S) empiricalFunctionSpace_totallyBounded) x))) ≤
      (c / 2 - α) *
        Real.sqrt (Real.log (2 * Fintype.card H)) := by
  let htb :
      TotallyBounded
        (Set.univ :
          Set (EmpiricalFunctionSpace (signSymmetrization F) S)) :=
    signSymmetrization_totallyBounded
      (F := F) (S := S) empiricalFunctionSpace_totallyBounded
  let g : ℝ → ℝ :=
    fun x ↦ Real.sqrt (Real.log (coveringNumber htb x))
  let C : ℝ := Real.sqrt (Real.log (2 * Fintype.card H))
  have hanti : AntitoneOn g (Set.uIcc α (c / 2)) := by
    intro a ha b hb hab
    rw [Set.uIcc_of_lt hαc] at ha hb
    have ha0 : 0 < a := by
      exact hα.trans_le ha.1
    have hb0 : 0 < b := ha0.trans_le hab
    dsimp only [g]
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log
    · exact_mod_cast coveringNumber_nonzero
        (Set.univ_nonempty :
          (Set.univ :
            Set (EmpiricalFunctionSpace (signSymmetrization F) S)).Nonempty)
        htb hb0
    · exact_mod_cast coveringNumber_antitone htb ha0 hb0 hab
  have hg : IntervalIntegrable g MeasureTheory.volume α (c / 2) :=
    hanti.intervalIntegrable
  calc
    (∫ x : ℝ in α..(c / 2),
        Real.sqrt (Real.log (coveringNumber
          (signSymmetrization_totallyBounded
            (F := F) (S := S) empiricalFunctionSpace_totallyBounded) x))) =
        ∫ x : ℝ in α..(c / 2), g x := rfl
    _ ≤ ∫ _x : ℝ in α..(c / 2), C := by
      apply intervalIntegral.integral_mono_on (le_of_lt hαc) hg
        intervalIntegrable_const
      intro x hx
      dsimp only [g, C]
      apply Real.sqrt_le_sqrt
      apply Real.log_le_log
      · exact_mod_cast coveringNumber_nonzero
          (Set.univ_nonempty :
            (Set.univ :
              Set (EmpiricalFunctionSpace (signSymmetrization F) S)).Nonempty)
          htb (hα.trans_le hx.1)
      · exact_mod_cast
          coveringNumber_signSymmetrization_le_two_mul_card
            F S (hα.trans_le hx.1)
    _ = (c / 2 - α) * C := by simp
    _ = (c / 2 - α) *
        Real.sqrt (Real.log (2 * Fintype.card H)) := rfl

/--
Finite-class Dudley estimate with no remaining covering number.
-/
theorem empiricalRademacherComplexity_le_finiteClassDudleyEstimate
    [Fintype H] [Nonempty H]
    (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳)
    {α c : ℝ} (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (hNorm : ∀ h, empiricalNorm S (F h) ≤ c) :
    empiricalRademacherComplexity n F S ≤
      finiteClassDudleyEstimate n (Fintype.card H) α c := by
  calc
    empiricalRademacherComplexity n F S ≤
        4 * α + (12 / Real.sqrt n) *
          (∫ x : ℝ in α..(c / 2),
            Real.sqrt (Real.log (coveringNumber
              (signSymmetrization_totallyBounded
                (F := F) (S := S)
                empiricalFunctionSpace_totallyBounded) x))) :=
      dudley_entropy_integral_abs
        hα empiricalFunctionSpace_totallyBounded hn hNorm hαc
    _ ≤ finiteClassDudleyEstimate n (Fintype.card H) α c := by
      dsimp only [finiteClassDudleyEstimate]
      rw [show
        (12 / Real.sqrt ↑n) * (c / 2 - α) *
              Real.sqrt (Real.log (2 * ↑(Fintype.card H))) =
            (12 / Real.sqrt ↑n) *
              ((c / 2 - α) *
                Real.sqrt (Real.log (2 * ↑(Fintype.card H)))) by ring]
      apply add_le_add
      · rfl
      · apply mul_le_mul_of_nonneg_left
        · exact finiteClass_entropy_integral_le F S hα hαc
        · exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

/--
The concrete choice `α = c/4` gives

`Rhatₙ(F;S) ≤ c + (3c/√n) √(log (2|H|))`.
-/
theorem empiricalRademacherComplexity_le_finiteClassDudleyEstimate_quarter
    [Fintype H] [Nonempty H]
    (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳)
    {c : ℝ} (hn : 0 < n) (hc : 0 < c)
    (hNorm : ∀ h, empiricalNorm S (F h) ≤ c) :
    empiricalRademacherComplexity n F S ≤
      c + (3 * c / Real.sqrt n) *
        Real.sqrt (Real.log (2 * Fintype.card H)) := by
  have h :=
    empiricalRademacherComplexity_le_finiteClassDudleyEstimate
      F S hn (show 0 < c / 4 by positivity)
        (show c / 4 < c / 2 by linarith) hNorm
  dsimp only [finiteClassDudleyEstimate] at h
  convert h using 1
  ring

end
