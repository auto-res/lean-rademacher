import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Notation
import Mathlib.Tactic.Cases
import FoML.Probability.Expectation
import FoML.Defs

open MeasureTheory ProbabilityTheory Real

universe u v w

/-
# Formalizing the symmetrization argument
Method where we fix exactly one instance of `X`
-/

variable {Z : Type w} {ι : Type v}
variable {f : ι → Z → ℝ}

variable {Ω : Type u} [MeasurableSpace Ω]

variable {X : Ω → Z}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {n : ℕ}

@[simp]
theorem Signs.card (n : ℕ) : Fintype.card (Signs n) = 2^n := by
  simp [Signs]

@[simp]
theorem Signs.apply_abs (σ : Signs n) (k : Fin n) : (|σ k| : ℤ) = 1 := by
  have := (σ k).property
  have : (σ k : ℤ) = -1 ∨ (σ k : ℤ) = 1 :=
    List.mem_pair.mp this
  rcases this with h | h
  · rw [h]
    simp
  · rw [h]
    simp

@[simp]
theorem Signs.apply_abs' (σ : Signs n) (k : Fin n) : (|σ k| : ℝ) = 1 := by
  norm_cast
  simp

theorem measurable_snocEquiv:
  @Measurable (Ω × (Fin n → Ω)) (Fin (n + 1) → Ω) Prod.instMeasurableSpace MeasurableSpace.pi fun f ↦ Fin.snoc f.2 f.1 := by
  apply measurable_pi_lambda
  intro i
  dsimp [Fin.snoc]
  if h : i.1 < n then
    have : (fun c : Ω × (Fin n → Ω) ↦ if h : ↑i < n then c.2 (i.castLT h) else c.1) = fun c ↦ c.2 (i.castLT h) := by
      ext c
      rw [dif_pos h]
    rw [this]
    exact Measurable.eval measurable_snd
  else
    have : (fun c : Ω × (Fin n → Ω)↦ if h : ↑i < n then c.2 (i.castLT h) else c.1) = fun c ↦ c.1 := by
      ext c
      rw [dif_neg h]
    rw [this]
    exact measurable_fst


lemma measure_equiv : (MeasureTheory.Measure.pi (fun _ ↦ μ) : Measure (Fin n.succ → Ω))
 = (μ.prod (MeasureTheory.Measure.pi (fun _ ↦ μ) : Measure (Fin n → Ω))).map (Fin.snocEquiv (fun _ ↦ Ω)):= by
  dsimp [Fin.snocEquiv]
  apply Measure.pi_eq
  intros s hs
  rw [Measure.map_apply measurable_snocEquiv (MeasurableSet.univ_pi hs)]
  have : ((fun (f : Ω × (Fin n → Ω)) (x : Fin (n+1)) ↦ @Fin.snoc n (fun x ↦ Ω) f.2 f.1 x) ⁻¹' Set.univ.pi s)
    = (s (Fin.last n)) ×ˢ (Set.univ.pi (s ∘ Fin.castSucc)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_prod,
      Function.comp_apply]
    constructor
    · intro h
      have := h (Fin.last n)
      rw [Fin.snoc_last] at this
      use this
      intro i
      have := h i.castSucc
      rw [Fin.snoc_castSucc] at this
      exact this
    · rintro ⟨h₁, h₂⟩ i
      dsimp [Fin.snoc]
      if h : i.1 < n then
        rw [dif_pos]
        exact h₂ (i.castLT h)
      else
        rw [dif_neg h]
        have : i = Fin.last n := Fin.eq_last_of_not_lt h
        rw [this]
        exact h₁
  rw [this, Measure.prod_prod, Measure.pi_pi]

  calc
    _ = ∏ i : Fin (n+1), Fin.snoc (μ ∘ s ∘ Fin.castSucc) (μ (s (Fin.last n))) i := by
      rw [mul_comm, Fin.prod_snoc]
      simp
    _ = _ := by
      congr
      ext i
      dsimp [Fin.snoc]
      simp only [ite_eq_left_iff, not_lt]
      intro h
      congr
      apply Eq.symm
      exact Fin.last_le_iff.mp h

lemma sigma_eq (f : ℤ → (Signs n) → ℝ) :
  ∑ σ' ∈ ({-1,1} : Finset ℤ), ∑ σ : Signs n, f σ' σ
  = ∑ σ : Signs (n + 1), f (σ (Fin.last n)) (Fin.init σ)  := by
  calc
    _ = ∑ σ : ({-1,1} : Finset ℤ) × (Signs n), f σ.1 σ.2 := by
      exact Eq.symm (Fintype.sum_prod_type _)
    _ = ∑ σ : Signs (n + 1), (fun σ' ↦ f σ'.1 σ'.2) ((Fin.snocEquiv (fun _ ↦ ({-1,1} : Finset ℤ))).symm σ) := by
      dsimp only [Signs]
      exact Eq.symm
        (Fintype.sum_equiv (Fin.snocEquiv fun x ↦ { x // x ∈ {-1, 1} }).symm
          (fun x ↦
            (fun σ' ↦ f (↑σ'.1) σ'.2) ((Fin.snocEquiv fun x ↦ { x // x ∈ {-1, 1} }).symm x))
          (fun x ↦ f (↑x.1) x.2) (congrFun rfl))
    _ = _ := by simp

omit [MeasurableSpace Ω] in
lemma bound_sub {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {ω : Ω × Ω} {I : ι}:
  |f I (X ω.1) - f I (X ω.2)| ≤ b+b := by
  calc
   _ ≤ |f I (X ω.1)| + |f I (X ω.2)| := by apply abs_sub
  _ ≤ _ := by linarith [h𝓕' I (X ω.1), h𝓕' I (X ω.2)]

omit [MeasurableSpace Ω] in
lemma boundedness₀ {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b)
  {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C) (ω : Ω × Ω) :
  ∀ (I : ι), |f I (X ω.1) - f I (X ω.2) + c I| ≤ b+b+C := by
  intro I
  calc
    _ ≤ |f I (X ω.1) - f I (X ω.2)| + |c I| := by apply abs_add_le
    _ ≤ b+b + |c I| := by
      apply add_le_add_left
      exact bound_sub h𝓕'
    _ ≤ _ := by linarith [hC I]

lemma abs_sigma (σ : ({-1, 1} : Finset ℤ)) : |@Int.cast ℝ instIntCast σ.1| = 1 := by aesop

omit [MeasurableSpace Ω] in
lemma boundedness₁ {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b)
  {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C) (ω : Ω × Ω) (σ : ({-1,1} : Finset ℤ)):
  ∀ (I : ι), |σ * (f I (X ω.1) - f I (X ω.2)) + c I| ≤ b+b+C := by
  intro I
  calc
    _ ≤ |σ * (f I (X ω.1) - f I (X ω.2))| + |c I| := by apply abs_add_le
    _ ≤ b+b + |c I| := by
      apply add_le_add_left
      rw [abs_mul, abs_sigma σ]
      simp only [one_mul]
      exact bound_sub h𝓕'
    _ ≤ _ := by linarith [hC I]


omit [IsProbabilityMeasure μ] in
lemma ineq (ω : Ω × Ω) {b : ℝ} (h𝓕': ∀ I : ι, ∀ z : Z, |f I z| ≤ b)
  {c : ι → ℝ} {C : ℝ} (hC : ∀ I : ι, |c I| ≤ C)
  (ih : ∀ (c : ι → ℝ),
  (∃ C, ∀ I : ι, |c I| ≤ C) →
    (∫ (ω' : Fin n → Ω × Ω),
        (⨆ I : ι, ∑ i : Fin n, (f I (X (ω' i).1) - f I (X (ω' i).2)) + c I) ∂Measure.pi fun _ ↦ μ.prod μ) =
      ∫ (ω' : Fin n → Ω × Ω),
        (2⁻¹ ^ n *
              ∑ σ : Fin n → ({-1, 1} : Finset ℤ), ⨆ I : ι, ∑ i : Fin n, (σ i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + c I)
          ∂Measure.pi fun _ ↦ μ.prod μ):
  let μ2n : Measure ((Fin n) → Ω × Ω):= MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ)
  (μ2n)[fun ω' : Fin n → Ω × Ω ↦ ⨆ I : ι,
    (∑ i : Fin n, (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)]
  = (μ2n)[fun ω' : (Fin n) → Ω × Ω ↦ (2:ℝ)⁻¹ ^ n * ∑ σ : Signs n,
      ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)] := by
  apply ih (fun I ↦ (f I (X ω.1) - f I (X ω.2)) + c I)
  use b+b+C
  exact boundedness₀ h𝓕' hC ω

omit [MeasurableSpace Ω] in
lemma inineq (ω : Ω × Ω) (ω': Fin n → Ω × Ω) {c : ι → ℝ}:
  (2 : ℝ)⁻¹ * ((2⁻¹ ^ n * ∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.2) - f I (X ω.1) + c I)) +
    2⁻¹ ^ n * ∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.1) - f I (X ω.2) + c I))
  = 2⁻¹ ^ (n+1) * ∑ σ : Signs (n + 1),
    (⨆ I : ι, ∑ i : Fin n, σ (Fin.castSucc i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + (σ (Fin.last n) * (f I (X ω.1) - f I (X ω.2)) + c I)) := by
  calc
    _ = 2⁻¹ ^ (n+1) * ∑ σ' ∈ ({-1, 1} : Finset ℤ), (∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (σ' * (f I (X ω.1) - f I (X ω.2)) + c I)) := by
      rw [←mul_add, ←mul_assoc]
      simp only [inv_pow, Int.reduceNeg, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
        Finset.sum_insert, Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_sub,
        Finset.sum_singleton, mul_eq_mul_right_iff]
      left
      ring_nf
    _ = _ := by
      rw [sigma_eq]
      simp only [inv_pow, Int.reduceNeg,
        mul_eq_mul_left_iff, inv_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
        and_false, not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
      rfl

lemma measurable_sub_part [Countable ι]
  (h𝓕 : ∀ (I : ι), Measurable (f I ∘ X))
  {n : ℕ} {I : ι} {i : Fin n}:
  Measurable fun ω : Fin n → Ω × Ω ↦ f I (X (ω i).1) - f I (X (ω i).2) := by
  apply Measurable.sub
  · apply (h𝓕 I).comp
    apply measurable_fst.comp
    exact measurable_pi_apply i
  · apply (h𝓕 I).comp
    apply measurable_snd.comp
    exact measurable_pi_apply i


lemma measurable_sum_part [Countable ι]
  (h𝓕 : ∀ (I : ι), Measurable (f I ∘ X))
  {n : ℕ} {I : ι}:
  Measurable fun ω : Fin n → Ω × Ω ↦ ∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2)) := by
  apply Finset.measurable_sum Finset.univ
  intro i _
  exact measurable_sub_part h𝓕

lemma measurable₀ [Countable ι]
  (h𝓕 : ∀ (I : ι), Measurable (f I ∘ X)) (n : ℕ)
  (c : ι → ℝ) :
  Measurable fun ω : Fin n → Ω × Ω ↦ ⨆ I, ∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2)) + c I := by
  apply Measurable.iSup
  intro I
  apply Measurable.add_const
  exact measurable_sum_part h𝓕

theorem abs_iSup_le [Nonempty ι] {f : ι → ℝ} {a : ℝ} (hf : ∀ i, |f i| ≤ a):
  |⨆ i, f i| ≤ a := by
  have hbdd : BddAbove (Set.range f) := by
    use a
    intro x ⟨i, heq⟩
    have := hf i
    rw [heq] at this
    exact le_of_max_le_left this
  apply abs_le.mpr
  constructor
  · let i : ι := Nonempty.some (by assumption)
    exact le_trans (abs_le.mp (hf i)).1 (le_ciSup hbdd i)
  · apply ciSup_le
    exact fun x ↦ le_of_max_le_left (hf x)

omit [MeasurableSpace Ω] in
lemma bound_lem {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b)
  (ω : Fin n → Ω × Ω) (I : ι) : |∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2))| ≤ ↑n * (b + b) := by
  calc
    _ ≤ ∑ i : Fin n, |f I (X (ω i).1) - f I (X (ω i).2)| := IsAbsoluteValue.abv_sum abs (fun i ↦ f I (X (ω i).1) - f I (X (ω i).2)) Finset.univ
    _ ≤ ∑ i : Fin n, (b+b) := by
      apply Fintype.sum_mono
      intro i
      exact bound_sub h𝓕'
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul]
      ring_nf

omit [MeasurableSpace Ω] in
lemma bound_isum' [Nonempty ι] {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C)
  (ω : Fin n → Ω × Ω) :
  |⨆ I, ∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2)) + c I| ≤ ↑n * (b + b) + C := by
  apply abs_iSup_le
  intro I
  calc
    _ ≤ |∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2))| + |c I| := by apply abs_add_le
    _ ≤ n*(b+b) + |c I| := by apply add_le_add_left (bound_lem h𝓕' ω I)
    _ ≤ _ := (add_le_add_iff_left (↑n * (b + b))).mpr (hC I)

omit [MeasurableSpace Ω] in
lemma bound_lem' {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b)
  (ω : Fin n → Ω × Ω) (I : ι) (σ : Fin n → ({-1, 1} : Finset ℤ)):
  |∑ i : Fin n, (σ i) * (f I (X (ω i).1) - f I (X (ω i).2))| ≤ ↑n * (b + b) := by
  calc
    _ ≤ ∑ i : Fin n, |(σ i) * (f I (X (ω i).1) - f I (X (ω i).2))| := IsAbsoluteValue.abv_sum abs _ Finset.univ
    _ ≤ ∑ i : Fin n, (b+b) := by
      apply Fintype.sum_mono
      intro i
      dsimp
      have : |(σ i : ℝ)| = 1 := abs_sigma (σ i)
      rw [abs_mul, this]
      simp only [one_mul, ge_iff_le]
      exact bound_sub h𝓕'
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul]
      ring_nf

omit [MeasurableSpace Ω] in
lemma bound_isum [Nonempty ι] {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C)
  (ω : Fin n → Ω × Ω) (σ : Fin n → ({-1, 1} : Finset ℤ)) :
  |⨆ I, ∑ i : Fin n, ↑↑(σ i) * (f I (X (ω i).1) - f I (X (ω i).2)) + c I| ≤ ↑n * (b + b) + C := by
  apply abs_iSup_le
  intro I
  calc
    _ ≤ |∑ i : Fin n, (σ i) * (f I (X (ω i).1) - f I (X (ω i).2))| + |c I| := by apply abs_add_le
    _ ≤ n*(b+b) + |c I| := by apply add_le_add_left (bound_lem' h𝓕' ω I σ)
    _ ≤ _ := (add_le_add_iff_left (↑n * (b + b))).mpr (hC I)

lemma integrable₀ [Countable ι] [Nonempty ι]
  (h𝓕 : ∀ (I : ι), Measurable (f I ∘ X)) {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {n : ℕ}
  {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C) :
  let μ2n := Measure.pi fun _ ↦ μ.prod μ;
  Integrable (fun ω ↦ ⨆ I, ∑ i : Fin n, (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) + (f I (X ω.1.1) - f I (X ω.1.2) + c I))
    ((μ.prod μ).prod μ2n) := by
  constructor
  · apply Measurable.aestronglyMeasurable
    apply Measurable.iSup
    intro I
    apply Measurable.add
    · apply (measurable_sum_part h𝓕).comp
      exact measurable_snd
    · apply Measurable.add_const
      apply Measurable.sub
      · exact (h𝓕 I).comp <| measurable_fst.comp measurable_fst
      · exact (h𝓕 I).comp <| measurable_snd.comp measurable_fst
  · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*(b+b)+(b+b+C))
    filter_upwards with ω
    dsimp
    exact bound_isum' h𝓕' (boundedness₀ h𝓕' hC ω.1) ω.2

omit [MeasurableSpace Ω] in
lemma bound_σsum [Nonempty ι]
  {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {c : ι → ℝ} {C : ℝ}
  (hC : ∀ (I : ι), |c I| ≤ C) (ω' : Fin n → Ω × Ω) :
  |2⁻¹ ^ n *
        ∑ σ : Fin n → ({-1, 1} : Finset ℤ), ⨆ I, ∑ i : Fin n, ↑↑(σ i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + c I| ≤
    ↑n * (b + b) + C := by
  rw [abs_mul, abs_of_pos (by simp)]
  have : |∑ σ : Fin n → ({-1, 1} : Finset ℤ),
    ⨆ I : ι, ∑ i : Fin n, (σ i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + c I|
    ≤ 2^n * (n*(b+b)+C) := by
    calc
      _ ≤ ∑ σ : Fin n → ({-1, 1} : Finset ℤ),
        |⨆ I : ι, ∑ i : Fin n, (σ i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + c I| := by
        apply Finset.abs_sum_le_sum_abs
      _ ≤ ∑ σ : Fin n → ({-1, 1} : Finset ℤ), (n*(b+b)+C) := by
        apply Finset.sum_le_sum
        intro σ _
        apply bound_isum h𝓕' hC
      _ = (Finset.univ : Finset (Fin n → ({-1, 1} : Finset ℤ))).card • (n*(b+b)+C) := by
        exact Finset.sum_const (n*(b+b)+C)
      _ = _ := by
        simp only [Int.reduceNeg, Finset.card_univ, Finset.mem_insert, Finset.mem_singleton,
          Fintype.card_pi, Fintype.card_coe, reduceCtorEq, not_false_eq_true,
          Finset.card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd, Finset.prod_const,
          Fintype.card_fin, smul_add, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring_nf
  calc
    _ ≤ 2⁻¹^n * (2^n * (n*(b+b)+C)) := mul_le_mul_of_nonneg_left this (by simp)
    _ = _ := by simp

theorem integrable₁' [Countable ι] [Nonempty ι]
  (h𝓕 : ∀ I : ι, Measurable (f I ∘ X)) {b : ℝ} (h𝓕' : ∀ I : ι, ∀ (z : Z), |f I z| ≤ b) {c : ι → ℝ} {C : ℝ}
  (hC : ∀ I : ι, |c I| ≤ C) :
  let μ2n := Measure.pi fun _ ↦ μ.prod μ;
  Integrable
    (fun a ↦
      2⁻¹ ^ n *
        ∑ σ : Fin n → ({-1, 1} : Finset ℤ),
          ⨆ I : ι, ∑ i : Fin n, (σ i) * (f I (X (a i).1) - f I (X (a i).2)) + c I)
    μ2n := by
  constructor
  · apply Measurable.aestronglyMeasurable
    apply Measurable.const_mul
    apply Finset.measurable_sum Finset.univ
    intro σ _
    apply Measurable.iSup
    intro I
    apply Measurable.add_const
    apply Finset.measurable_sum Finset.univ
    intro i _
    apply Measurable.const_mul
    apply Measurable.sub
    · apply (h𝓕 I).comp
      apply measurable_fst.comp
      exact measurable_pi_apply i
    · apply (h𝓕 I).comp
      apply measurable_snd.comp
      exact measurable_pi_apply i
  · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*(b+b)+C)
    filter_upwards with ω'
    dsimp
    exact bound_σsum h𝓕' hC ω'


theorem integrable₁ (ω : Ω × Ω) [Countable ι] [Nonempty ι]
  (h𝓕 : ∀ I : ι, Measurable (f I ∘ X)) {b : ℝ} (h𝓕' : ∀ I : ι, ∀ (z : Z), |f I z| ≤ b) {c : ι → ℝ} {C : ℝ}
  (hC : ∀ I : ι, |c I| ≤ C) :
  let μ2n := Measure.pi fun _ ↦ μ.prod μ;
  Integrable
    (fun a ↦
      2⁻¹ ^ n *
        ∑ σ : Fin n → ({-1, 1} : Finset ℤ),
          ⨆ I : ι, ∑ i : Fin n, (σ i) * (f I (X (a i).1) - f I (X (a i).2)) + (f I (X ω.1) - f I (X ω.2) + c I))
    μ2n := by
  exact integrable₁' h𝓕 h𝓕' (boundedness₀ h𝓕' hC ω)

set_option maxHeartbeats 900000

theorem integrable₂ [Countable ι] [Nonempty ι]
  (h𝓕 : ∀ (I : ι), Measurable (f I ∘ X)) {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {n : ℕ}
  {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C) :
  Integrable
    (fun a ↦
      ∫ (x : Fin n → Ω × Ω),
        (fun ω' ↦
            2⁻¹ ^ n *
              ∑ σ : Fin n → ({-1, 1} : Finset ℤ),
                ⨆ I, ∑ i : Fin n, ↑↑(σ i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + (f I (X a.1) - f I (X a.2) + c I))
          x ∂ Measure.pi fun _ ↦ μ.prod μ)
    (μ.prod μ) := by
  constructor
  · apply StronglyMeasurable.aestronglyMeasurable
    apply @StronglyMeasurable.integral_prod_right' (Ω × Ω) (Fin n → (Ω × Ω)) ℝ _ _ (Measure.pi fun _ ↦ μ.prod μ) _ _ _ (fun ω ↦ (2⁻¹ ^ n *
      ∑ σ : Fin n → ({-1, 1} : Finset ℤ),
      ⨆ I, ∑ i : Fin n, ↑↑(σ i) * (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) + (f I (X ω.1.1) - f I (X ω.1.2) + c I)))
    apply Measurable.stronglyMeasurable
    apply Measurable.const_mul
    apply Finset.measurable_sum Finset.univ
    intro σ _
    apply Measurable.iSup
    intro I
    apply Measurable.add
    · apply Finset.measurable_sum Finset.univ
      intro i _
      apply Measurable.const_mul
      exact (measurable_sub_part h𝓕).comp measurable_snd
    · apply Measurable.add_const
      apply Measurable.sub
      · exact (h𝓕 I).comp <| measurable_fst.comp measurable_fst
      · exact (h𝓕 I).comp <| measurable_snd.comp measurable_fst
  · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*(b+b)+(b+b+C))
    filter_upwards with ω'
    dsimp
    apply abs_expectation_le_of_abs_le_const
    filter_upwards with ω
    exact bound_σsum h𝓕' (boundedness₀ h𝓕' hC ω') ω

theorem integrable₃ [Countable ι] [Nonempty ι]
  (h𝓕 : ∀ (I : ι), Measurable (f I ∘ X)) {b : ℝ} (h𝓕' : ∀ (I : ι) (z : Z), |f I z| ≤ b) {n : ℕ}
  {c : ι → ℝ} {C : ℝ} (hC : ∀ (I : ι), |c I| ≤ C) :
  Integrable
    (fun ω ↦
      2⁻¹ ^ (n + 1) *
        ∑ σ : Fin (n + 1) → ({-1, 1} : Finset ℤ),
          ⨆ I,
            ∑ i : Fin n, (σ (Fin.castSucc i)) * (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) +
              ((σ (Fin.last n)) * (f I (X ω.1.1) - f I (X ω.1.2)) + c I))
    ((μ.prod μ).prod (Measure.pi fun _ ↦ μ.prod μ)) := by
  constructor
  · apply Measurable.aestronglyMeasurable
    apply Measurable.const_mul
    apply Finset.measurable_sum Finset.univ
    intro σ _
    apply Measurable.iSup
    intro I
    apply Measurable.add
    · apply Finset.measurable_sum Finset.univ
      intro i _
      apply Measurable.const_mul
      exact (measurable_sub_part h𝓕).comp measurable_snd
    · apply Measurable.add_const
      apply Measurable.const_mul
      apply Measurable.sub
      · exact (h𝓕 I).comp <| measurable_fst.comp measurable_fst
      · exact (h𝓕 I).comp <| measurable_snd.comp measurable_fst
  · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (n*(b+b)+(b+b+C))
    filter_upwards with ω
    dsimp
    rw [abs_mul, abs_of_pos (by simp)]
    have : |∑ σ : Fin (n+1) → ({-1, 1} : Finset ℤ),
      ⨆ I : ι, ∑ i : Fin n, (σ (Fin.castSucc i)) * (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) + ((σ (Fin.last n)) * (f I (X ω.1.1) - f I (X ω.1.2)) + c I)|
      ≤ 2^(n+1) * (n*(b+b)+(b+b+C)) := by
      calc
        _ ≤ ∑ σ : Fin (n+1) → ({-1, 1} : Finset ℤ),
          |⨆ I : ι, ∑ i : Fin n, (σ (Fin.castSucc i)) * (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) + ((σ (Fin.last n)) * (f I (X ω.1.1) - f I (X ω.1.2)) + c I)| := by
          apply Finset.abs_sum_le_sum_abs
        _ ≤ ∑ σ : Fin (n+1) → ({-1, 1} : Finset ℤ), (n*(b+b)+(b+b+C)) := by
          apply Finset.sum_le_sum
          intro σ _
          apply bound_isum h𝓕'
          exact boundedness₁ h𝓕' hC ω.1 (σ (Fin.last n))
        _ = (Finset.univ : Finset (Fin (n+1) → ({-1, 1} : Finset ℤ))).card • (n*(b+b)+(b+b+C)) := Finset.sum_const (n*(b+b)+(b+b+C))
        _ = _ := by
          simp only [Int.reduceNeg, Finset.card_univ, Finset.mem_insert, Finset.mem_singleton,
            Fintype.card_pi, Fintype.card_coe, reduceCtorEq, not_false_eq_true,
            Finset.card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd, Finset.prod_const,
            Fintype.card_fin, smul_add, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          ring_nf
    calc
      _ ≤ 2⁻¹^(n+1) * (2^(n+1) * (n*(b+b)+(b+b+C))) := mul_le_mul_of_nonneg_left this (by simp)
      _ = _ := by simp only [inv_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero, inv_mul_cancel_left₀]

lemma ineq2 (ω : Ω × Ω) [Countable ι] [Nonempty ι] (h𝓕 : ∀ I : ι, Measurable (f I ∘ X))
  {b : ℝ} (h𝓕': ∀ I : ι, ∀ z : Z, |f I z| ≤ b)
  {c : ι → ℝ} {C : ℝ} (hC : ∀ I : ι, |c I| ≤ C):
  let μ2n : Measure ((Fin n) → Ω × Ω):= MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ)
  (2 : ℝ)⁻¹ * ((μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
    (⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.2) - f I (X ω.1) + c I))] +
    (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
    (⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.1) - f I (X ω.2) + c I))])
  = (μ2n)[fun ω' ↦ (2 : ℝ)⁻¹ ^ (n+1) * ∑ σ : Signs (n + 1),
    (⨆ I : ι, ∑ i : Fin n, σ (Fin.castSucc i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + (σ (Fin.last n) * (f I (X ω.1) - f I (X ω.2)) + c I))] := by
  let μ2n : Measure ((Fin n) → Ω × Ω):= MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ)
  calc
    _ = (2 : ℝ)⁻¹ * ((μ2n)[fun ω' ↦ (2⁻¹ ^ n * ∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.2) - f I (X ω.1) + c I)) +
    2⁻¹ ^ n * ∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.1) - f I (X ω.2) + c I)]) := by
      apply congr_arg
      apply Eq.symm
      apply integral_add
      · apply integrable₁ ω.swap h𝓕 h𝓕' hC
      · apply integrable₁ ω h𝓕 h𝓕' hC
    _ = (μ2n)[fun ω' ↦ (2 : ℝ)⁻¹ * ((2⁻¹ ^ n * ∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.2) - f I (X ω.1) + c I)) +
    2⁻¹ ^ n * ∑ σ : Signs n,
    ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + (f I (X ω.1) - f I (X ω.2) + c I))] := by
      apply Eq.symm
      apply integral_const_mul
    _ = _ := by
      apply congr_arg
      ext ω'
      dsimp
      exact inineq ω ω'

lemma aux₃ [Countable ι] [Nonempty ι] (h𝓕 : ∀ I : ι, Measurable (f I ∘ X))
  {b : ℝ} (h𝓕': ∀ I : ι, ∀ z : Z, |f I z| ≤ b):
  ∀ (c : ι → ℝ), (∃ C : ℝ, ∀ I : ι, |c I| ≤ C) → (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
    ↦ ⨆ I : ι, ∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2)) + c I]
  = (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
    ↦ 2⁻¹ ^ n * ∑ σ : Signs n, (⨆ I : ι, ∑ i : Fin n, σ i * (f I (X (ω i).1) - f I (X (ω i).2)) + c I)]:= by
  induction' n with n ih
  · simp
  · rintro c ⟨C, hC⟩
    let μ2n : Measure ((Fin n) → Ω × Ω):= MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ)
    calc
      _ = (((μ.prod μ).prod μ2n).map (Fin.snocEquiv (fun _ ↦ Ω × Ω)))[fun ω ↦ ⨆ I : ι, ∑ i : Fin (n + 1), (f I (X (ω i).1) - f I (X (ω i).2)) + c I] := by
        rw [measure_equiv]
      _ = ((μ.prod μ).prod μ2n)[(fun ω ↦ ⨆ I : ι, ∑ i : Fin (n + 1), (f I (X (ω i).1) - f I (X (ω i).2)) + c I) ∘ (Fin.snocEquiv (fun _ ↦ Ω × Ω))] := by
        apply integral_map
        · apply Measurable.aemeasurable
          dsimp [Fin.snocEquiv]
          exact measurable_snocEquiv
        · apply Measurable.aestronglyMeasurable
          exact measurable₀ h𝓕 (n+1) c
      _ = ((μ.prod μ).prod μ2n)[fun ω ↦ ⨆ I : ι, ∑ i : Fin n, (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) + ((f I (X ω.1.1) - f I (X ω.1.2)) + c I)] := by
        apply congr_arg
        ext
        dsimp
        apply congr_arg
        ext f
        rw [Fin.sum_univ_castSucc, add_assoc]
        simp
      _ = (μ.prod μ)[fun ω ↦ (μ2n)[fun ω' ↦ ⨆ I : ι, ∑ i : Fin n, (f I (X (ω' i).1) - f I (X (ω' i).2)) + ((f I (X ω.1) - f I (X ω.2)) + c I)]] := by
        apply integral_prod
        apply integrable₀ h𝓕 h𝓕' hC
      _ = (μ.prod μ)[fun ω ↦ (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)]] := by
        apply congr_arg
        ext ω
        dsimp
        exact (ineq ω h𝓕' hC ih) -- Removing the parentheses triggers an unexpected error
      _ = (2:ℝ)⁻¹ * ((μ.prod μ)[fun ω'' ↦ (fun ω ↦ ((μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n, ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.2) - f I (X ω.1)) + c I)])) ω''.swap] +
            (μ.prod μ)[fun ω ↦ (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n, ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)]]) := by
        grind only [= Prod.snd_swap, = Prod.swap_prod_mk, = Prod.fst_swap, cases eager Prod,
          cases Or]
      _ = (2:ℝ)⁻¹ * ((μ.prod μ)[fun ω ↦ (μ2n)[fun ω' : Fin n → (Ω × Ω) ↦ (2:ℝ)⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.2) - f I (X ω.1)) + c I)]] +
          (μ.prod μ)[fun ω ↦ (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)]]) := by
        apply congr_arg
        apply congrFun
        apply congr_arg
        apply integral_prod_swap
      _ = (2:ℝ)⁻¹ * (μ.prod μ)[fun ω ↦ (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.2) - f I (X ω.1)) + c I)] +
          (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)]] := by
          apply congr_arg
          apply Eq.symm
          apply integral_add
          · exact (integrable₂ h𝓕 h𝓕' hC).swap
          · exact integrable₂ h𝓕 h𝓕' hC
      _ = (μ.prod μ)[fun ω ↦ 2⁻¹ * ((μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.2) - f I (X ω.1)) + c I)] +
          (μ2n)[fun ω' ↦ 2⁻¹ ^ n * ∑ σ : Signs n,
          ⨆ I : ι, (∑ i : Fin n, σ i * (f I (X (ω' i).1) - f I (X (ω' i).2))) + ((f I (X ω.1) - f I (X ω.2)) + c I)])] := by
          apply Eq.symm
          apply integral_const_mul
      _ = (μ.prod μ)[fun ω ↦ (μ2n)[fun ω' ↦  (2:ℝ)⁻¹ ^ (n+1) * ∑ σ : Signs (n + 1),
        (⨆ I : ι, ∑ i : Fin n, σ (Fin.castSucc i) * (f I (X (ω' i).1) - f I (X (ω' i).2)) + (σ (Fin.last n) * (f I (X ω.1) - f I (X ω.2)) + c I))]] := by
        apply congr_arg
        ext ω
        dsimp
        exact ineq2 ω h𝓕 h𝓕' hC
      _ = ((μ.prod μ).prod μ2n)[fun ω ↦  2⁻¹ ^ (n+1) * ∑ σ : Signs (n + 1),
        (⨆ I : ι, ∑ i : Fin n, σ (Fin.castSucc i) * (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)) + (σ (Fin.last n) * (f I (X ω.1.1) - f I (X ω.1.2)) + c I))] := by
        apply Eq.symm
        apply integral_prod
        exact integrable₃ h𝓕 h𝓕' hC
      _ = ((μ.prod μ).prod μ2n)[(fun ω : Fin (n+1) → Ω × Ω
        ↦ 2⁻¹ ^ (n+1) * ∑ σ : Signs (n + 1), (⨆ I : ι, ∑ i : Fin (n+1), σ i * (f I (X (ω i).1) - f I (X (ω i).2)) + c I))
        ∘ (Fin.snocEquiv fun _ ↦ (Ω × Ω))] := by
        apply congr_arg
        ext ω
        dsimp
        congr
        ext σ
        apply iSup_congr
        intro I
        have : ∑ i : Fin (n + 1), (σ i) *
          (f I (X (@Fin.snoc n (fun _ ↦ Ω × Ω) ω.2 ω.1 i).1) - f I (X (@Fin.snoc n (fun _ ↦ Ω × Ω) ω.2 ω.1 i).2))
          = ∑ i : Fin (n + 1),
            Fin.snoc (fun i : Fin n ↦ (σ (Fin.castSucc i)) * (f I (X (ω.2 i).1) - f I (X (ω.2 i).2)))
            ((σ (Fin.last n)) * (f I (X ω.1.1) - f I (X ω.1.2))) i := by
          congr
          ext i
          dsimp [Fin.snoc]
          if h : i.1 < n then
            rw [dif_pos h, dif_pos h]
          else
            rw [dif_neg h, dif_neg h]
            congr
            simp only [not_lt] at h
            exact Fin.last_le_iff.mp h
        rw [this, Fin.sum_snoc, add_assoc]
      _ = (((μ.prod μ).prod μ2n).map (Fin.snocEquiv fun _ ↦ (Ω × Ω)))[(fun ω : Fin (n+1) → Ω × Ω
        ↦ 2⁻¹ ^ (n+1) * ∑ σ : Signs (n + 1), (⨆ I : ι, ∑ i : Fin (n+1), σ i * (f I (X (ω i).1) - f I (X (ω i).2)) + c I))] := by
        apply Eq.symm
        apply integral_map
        · apply Measurable.aemeasurable
          dsimp [Fin.snocEquiv]
          exact measurable_snocEquiv
        · rw [←measure_equiv]
          exact (integrable₁' h𝓕 h𝓕' hC).aestronglyMeasurable
      _ = _ := by
        rw [←measure_equiv]

theorem symmetrization_equation [Countable ι] [Nonempty ι] (h𝓕 : ∀ I : ι, Measurable (f I ∘ X))
  {b : ℝ} (h𝓕': ∀ I : ι, ∀ z : Z, |f I z| ≤ b):
  (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
    ↦ ⨆ I : ι, ∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2))]
  = (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
    ↦ 2⁻¹ ^ n * ∑ σ : Signs n, ⨆ I : ι, ∑ i : Fin n, σ i * (f I (X (ω i).1) - f I (X (ω i).2))]:= by
  have := @aux₃ Z ι f Ω _ X μ _ n _ _ h𝓕 b h𝓕' (fun _ ↦ 0) ⟨0, by simp⟩
  simp only [Finset.sum_sub_distrib, add_zero, inv_pow, Int.reduceNeg] at this
  simp only [Finset.sum_sub_distrib, inv_pow, Int.reduceNeg]
  exact this

lemma sup_abs_lemma [Nonempty ι] {V : (Z → ℝ) → ℝ} (hV₀: ∀ f, V (-f) = - (V f)) (hV₁: BddAbove (Set.range fun i ↦ |V (f i)|)):
  ⨆ i : ι, |V (f i)| = ⨆ i : Fin 2 × ι, V (if i.1.1 == 0 then f i.2 else -(f i.2)) := by
  have hV₁' : BddAbove (Set.range fun i : Fin 2 × ι ↦ V (if i.1.1 == 0 then f i.2 else -(f i.2))) := by
    obtain ⟨a,ha⟩ := hV₁
    use a
    dsimp [upperBounds] at *
    rintro x ⟨⟨s, i⟩, eq⟩
    have hax := ha ⟨i, rfl⟩
    dsimp at hax
    rw [←eq]
    dsimp
    if h : s.1 == 0 then
      rw [if_pos h]
      exact le_of_max_le_left hax
    else
      rw [if_neg h, hV₀]
      exact le_of_max_le_right hax
  apply le_antisymm
  · apply ciSup_le
    intro i
    apply abs_le'.mpr
    constructor
    · exact le_ciSup hV₁' ⟨(0 : Fin 2), i⟩
    · rw [←hV₀]
      exact le_ciSup hV₁' ⟨(1 : Fin 2), i⟩
  · apply ciSup_le
    rintro ⟨s,i⟩
    apply le_trans _ (le_ciSup hV₁ i)
    if h : s.1 == 0 then
      rw [if_pos h]
      exact le_abs_self (V (f i))
    else
      rw [if_neg h, hV₀]
      exact neg_le_abs (V (f i))

theorem abs_symmetrization_equation [Countable ι] [Nonempty ι] (h𝓕 : ∀ I : ι, Measurable (f I ∘ X))
  {b : ℝ} (h𝓕': ∀ I : ι, ∀ z : Z, |f I z| ≤ b):
  (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
    ↦ ⨆ I : ι, |∑ i : Fin n, (f I (X (ω i).1) - f I (X (ω i).2))|]
  = (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
    ↦ 2⁻¹ ^ n * ∑ σ : Signs n, ⨆ I : ι, |∑ i : Fin n, σ i * (f I (X (ω i).1) - f I (X (ω i).2))|]:= by
  let f' : (Fin 2 × ι) → Z → ℝ := fun i ↦ if i.1.1 == 0 then f i.2 else -(f i.2)
  calc
    _ = (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
      ↦ ⨆ I : Fin 2 × ι, ∑ i : Fin n, (f' I (X (ω i).1) - f' I (X (ω i).2))] := by
      congr
      ext ω
      dsimp
      let V : (Z → ℝ ) → ℝ := fun f ↦ ∑ i, (f (X (ω i).1) - f (X (ω i).2))
      have hV₀: ∀ f, V (-f) = - (V f) := by
        intro f
        dsimp [V]
        rw [←Finset.sum_neg_distrib]
        congr
        ext i
        ring_nf
      have hV₁: BddAbove (Set.range fun i ↦ |V (f i)|) := by
        use n * (b+b)
        intro x ⟨I,eq⟩
        rw [←eq]
        dsimp [V]
        exact bound_lem h𝓕' ω I
      exact sup_abs_lemma hV₀ hV₁
    _ = (MeasureTheory.Measure.pi (fun _ ↦ μ.prod μ))[fun ω : Fin n → Ω × Ω
      ↦ 2⁻¹ ^ n * ∑ σ : Signs n, ⨆ I : Fin 2 × ι, ∑ i : Fin n, σ i * (f' I (X (ω i).1) - f' I (X (ω i).2))]:= by
      have h𝓕₂ : ∀ I, Measurable (f' I ∘ X) := by
        dsimp [f']
        rintro ⟨s, I⟩
        if h : s.1 == 0 then
          rw [if_pos h]
          dsimp
          exact h𝓕 I
        else
          rw [if_neg h]
          dsimp
          exact (h𝓕 I).neg
      have h𝓕'₂: ∀ I, ∀ z : Z, |f' I z| ≤ b := by
        rintro ⟨s,I⟩ z
        dsimp [f']
        if h : s.1 == 0 then
          rw [if_pos h]
          exact h𝓕' I z
        else
          rw [if_neg h]
          simp only [Pi.neg_apply, abs_neg]
          exact h𝓕' I z
      exact symmetrization_equation h𝓕₂ h𝓕'₂
    _ = _ := by
      congr
      ext ω
      dsimp
      congr
      ext σ
      dsimp
      let V : (Z → ℝ ) → ℝ := fun f ↦ ∑ i, (σ i) * (f (X (ω i).1) - f (X (ω i).2))
      have hV₀: ∀ f, V (-f) = - (V f) := by
        intro f
        dsimp [V]
        rw [←Finset.sum_neg_distrib]
        congr
        ext i
        ring_nf
      have hV₁: BddAbove (Set.range fun i ↦ |V (f i)|) := by
        use n * (b+b)
        intro x ⟨I,eq⟩
        rw [←eq]
        dsimp [V]
        exact bound_lem' h𝓕' ω I σ
      exact (sup_abs_lemma hV₀ hV₁).symm
