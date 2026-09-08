import FoML.Probability.Expectation
import FoML.Probability.Hoeffding
import FoML.Probability.MeasurePi
import Mathlib.Tactic.Cases

open MeasureTheory ProbabilityTheory

lemma double_integral_indep_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Type*} {β : Type*} {β' : Type*}
  {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}
  {F : β × β' → E}
  {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [MeasureTheory.IsFiniteMeasure μ]
  {hF' : StronglyMeasurable F}
  (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : ProbabilityTheory.IndepFun f g μ)
  (hF: HasFiniteIntegral F ((Measure.map f μ).prod (Measure.map g μ))):
  ∫ (ω : Ω), (∫ (ω' : Ω), F (f ω, g ω') ∂μ) ∂μ = ∫ (ω : Ω), F (f ω, g ω) ∂μ := by
  let ν : Measure β := Measure.map f μ
  let ν' : Measure β' := Measure.map g μ
  have hfg' : Measure.map (fun (ω : Ω) => (f ω, g ω)) μ = ν.prod ν' := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hf hg).mp hfg
  calc
  _ = ∫ (ω : Ω), (∫ (x' : β'), F (f ω, x') ∂ ν') ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    apply Eq.symm
    apply MeasureTheory.integral_map
    assumption
    apply StronglyMeasurable.aestronglyMeasurable
    apply hF'.comp_measurable
    exact measurable_prodMk_left
  _ = ∫ (x : β), (∫ (x' : β'), F (x, x') ∂ ν') ∂ ν := by
    apply Eq.symm
    apply MeasureTheory.integral_map
    assumption
    apply StronglyMeasurable.aestronglyMeasurable
    exact StronglyMeasurable.integral_prod_right hF'
  _ = ∫ (z : β × β'), F z ∂ (ν.prod ν') := by
    apply Eq.symm
    apply MeasureTheory.integral_prod
    exact ⟨hF'.aestronglyMeasurable, hF⟩
  _ = ∫ (z : β × β'), F z ∂ (Measure.map (fun (ω : Ω) => (f ω, g ω)) μ) := by rw [←hfg']
  _ = ∫ (ω : Ω), F (f ω, g ω) ∂μ := by
    apply MeasureTheory.integral_map
    exact AEMeasurable.prodMk hf hg
    rw [hfg']
    exact hF'.aestronglyMeasurable

theorem ProbabilityTheory.iIndepFun.comp_right
  {Ω ι ι' : Type*} [DecidableEq ι] {_mΩ : MeasurableSpace Ω}
  {μ : MeasureTheory.Measure Ω} {β : ι → Type*}
  {mβ : (i : ι) → MeasurableSpace (β i)}
  {f : (i : ι) → Ω → β i} (h : ProbabilityTheory.iIndepFun f μ)
  {g : ι' → ι} (hg : Function.Injective g):
  ProbabilityTheory.iIndepFun (fun i ↦ f (g i)) μ := by
  simp only [iIndepFun, Kernel.iIndepFun, Kernel.iIndep, Kernel.iIndepSets, Set.mem_setOf_eq,
    Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure] at *
  intro s' f₁' h₁'
  let s := s'.image g
  have hunique (i : ι): ∀ (y₁ y₂ : ι'), y₁ ∈ s' ∧ g y₁ = i → y₂ ∈ s' ∧ g y₂ = i → y₁ = y₂ := by
    intro y₁ y₂ ⟨_, hy₁⟩ ⟨_, hy₂⟩
    exact hg <| hy₁.trans hy₂.symm
  let invg : Π (i : s), { i' : ι' // i' ∈ s' ∧ g i' = i.1 } := fun ⟨i, hi⟩ ↦ by
    simp only [Finset.mem_image, s] at hi
    exact Finset.chooseX (fun i' ↦ g i' = i) s' <| existsUnique_of_exists_of_unique hi (hunique i)
  let f₁ : ι → Set Ω := fun i ↦
    if hi : i ∈ s then
      f₁' (invg ⟨i,hi⟩).1
    else
      Set.univ
  have h₁ : ∀ i ∈ s, @MeasurableSet Ω (MeasurableSpace.comap (f i) (mβ i)) (f₁ i) := by
    intro i hi
    dsimp only [f₁]
    rw [dif_pos hi]
    have key : ∀ j : ι', j ∈ s' → g j = i →
        @MeasurableSet Ω (MeasurableSpace.comap (f i) (mβ i)) (f₁' j) := by
      intro j hjs hji
      subst hji
      exact h₁' j hjs
    exact key _ (invg ⟨i, hi⟩).2.1 (invg ⟨i, hi⟩).2.2

  calc
    _ = μ (⋂ i ∈ s, f₁ i) := by
      apply congrArg
      apply Set.Subset.antisymm
      · intro x hx
        apply Set.mem_iInter₂_of_mem
        intro i hi
        dsimp only [f₁]
        rw [dif_pos hi]
        simp only [Set.mem_iInter] at hx
        apply hx
        exact (invg ⟨i, hi⟩).2.1
      · intro x hx
        apply Set.mem_iInter₂_of_mem
        simp only [Finset.mem_image, Set.iInter_exists, Set.biInter_and',
          Set.iInter_iInter_eq_right, Set.mem_iInter, s, f₁, invg] at hx
        intro i' hi'
        have hx := hx i' hi'
        rw [dif_pos (⟨i', ⟨hi', rfl⟩⟩ : ∃ a ∈ s', g a = g i')] at hx
        have h₀ : g i' ∈ Finset.image g s' := (Function.Injective.mem_finset_image hg).mpr hi'
        have : (invg ⟨g i', h₀⟩).1 = i' := hg (invg ⟨g i', h₀⟩).2.2
        rw [this] at hx
        exact hx
    _ = ∏ x ∈ s, μ (f₁ x) := h s h₁
    _ = _ := by
      apply Eq.symm
      apply Finset.prod_bij (fun i' _ ↦ g i')
      · intro i' hi'
        simp only [Finset.mem_image, s]
        use i'
      · exact fun _ _ _ _ a ↦ hg a
      · intro i hi
        simp only [Finset.mem_image, s] at hi
        exact bex_def.mpr hi
      · intro i' hi'
        apply congrArg
        dsimp [f₁]
        have : g i' ∈ s := (Function.Injective.mem_finset_image hg).mpr hi'
        rw [dif_pos this]
        apply congrArg
        apply hg
        exact (invg ⟨g i', this⟩).2.2.symm

variable {𝓧 : Type*}

variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

-- instead of using condexp, we define Y directly by integration
-- Y_k(x_0, …, x_{k-1}) := ∫ f(x_0, …, x_{k-1}, X_k, …, X_{m-1}) dΩ
-- A_k(x_0, …, x_{k-1}) := inf_x ∫ f(x_0, …, x_{k-1}, x, X_{k+1}, …, X_{m-1}) dΩ
-- B_k(x_0, …, x_{k-1}) := sup_x ∫ f(x_0, …, x_{k-1}, x, X_{k+1}, …, X_{m-1}) dΩ
noncomputable def expressionY (μ : Measure Ω) (X' : Fin m → Ω → 𝓧) (f' : (Fin m → 𝓧) → ℝ) (k : Fin m.succ) (Xk : Fin k → 𝓧) : ℝ :=
  ∫ (x : Ω), (fun ω ↦ f' fun i ↦ if h : i.1 < k.1 then Xk ⟨i.1, h⟩ else X' i ω) x ∂μ

noncomputable def expressionA (μ : Measure Ω) (X' : Fin m → Ω → 𝓧) (f' : (Fin m → 𝓧) → ℝ) (k: Fin m) (Xk : Fin k → 𝓧) :=
  ⨅ (x : 𝓧), μ[fun ω ↦ f' (fun i ↦ if h : i.1 < k.1 then Xk ⟨i.1,h⟩ else if i.1 = k.1 then x else X' i ω)]

noncomputable def expressionB (μ : Measure Ω) (X' : Fin m → Ω → 𝓧) (f' : (Fin m → 𝓧) → ℝ) (k: Fin m) (Xk : Fin k → 𝓧) :=
  ⨆ (x : 𝓧), μ[fun ω ↦ f' (fun i ↦ if h : i.1 < k.1 then Xk ⟨i.1,h⟩ else if i.1 = k.1 then x else X' i ω)]

noncomputable def expressionV (μ : Measure Ω) (X' : Fin m → Ω → 𝓧) (f' : (Fin m → 𝓧) → ℝ) (k : Fin m) (Xk : Fin k → 𝓧) :=
  fun ω ↦ expressionY μ X' f' k.succ (Fin.snoc Xk (X' k ω)) - expressionY μ X' f' k.castSucc Xk

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma expectation_const {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  (c : E) : ∫ (_ : Ω), c ∂μ = c := by
  calc
    _ = (μ Set.univ).toReal • c := by
      exact integral_const c
    _ = c := by
      have : μ (Set.univ : Set Ω) = 1 := isProbabilityMeasure_iff.mp (by assumption)
      rw [this]
      simp

variable {X' : Fin m → Ω → 𝓧} {f' : (Fin m → 𝓧) → ℝ}

omit [IsProbabilityMeasure μ] in
lemma Y_snoc_eq
  (k : Fin m) (Xk : Fin k → 𝓧) (x : 𝓧) :
  expressionY μ X' f' k.succ (Fin.snoc Xk x) =
    μ[fun ω ↦ f' fun i ↦ if h : i.1 < k.1 then Xk ⟨i.1, h⟩ else if i.1 = k.1 then x else X' i ω] := by
  apply integral_congr_ae
  filter_upwards with ω
  apply congr rfl
  ext i
  if h : i.1 < k.1 then
    have hi : i.1<(Fin.succ k).1 := by dsimp; linarith
    rw [dif_pos hi, dif_pos h]
    exact Fin.snoc_castSucc (α := fun _ ↦ 𝓧) (p := Xk) (x := x) (i := ⟨i.1, h⟩)
  else
    rw [dif_neg h]
    if h2 : i.1 = k.1 then
      have hi : i.1 < (Fin.succ k).1 := by dsimp; linarith
      rw [dif_pos hi, if_pos h2]
      have hlast : (⟨i.1, hi⟩ : Fin (k.1 + 1)) = Fin.last k := Fin.ext h2
      show (Fin.snoc Xk x : Fin (k.1 + 1) → 𝓧) ⟨i.1, hi⟩ = x
      rw [hlast]
      apply Fin.snoc_last
    else
      have : ¬ (i.1 < (Fin.succ k).1) := by
        simp only [Fin.val_succ, not_lt]
        simp only [Fin.val_fin_lt, not_lt] at h
        apply Fin.val_add_one_le_of_lt
        exact lt_of_le_of_ne h fun a => h2 (congrArg Fin.val (id (Eq.symm a)))
      rw [dif_neg this, if_neg h2]

variable {c' : Fin m → ℝ}

lemma bound_f'
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (x₀ : 𝓧):
  ∀ (xi : Fin m → 𝓧), |f' xi| ≤ |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i := by
  have h (k : ℕ) : (h' : k ≤ m) → ∀ xi : (Fin m → 𝓧), |f' xi| ≤
    |f' (fun i ↦ if i.1 < k then x₀ else xi i)| + ∑ (i : Fin k), c' ⟨i.1, by linarith [i.2, h']⟩  := by
    induction' k with k ih
    · simp only [zero_le, not_lt_zero, ↓reduceIte, Finset.univ_eq_empty, Finset.sum_empty,
      add_zero, le_refl, implies_true]
    · intro h' xi
      apply le_trans <| ih (by linarith [h']) xi
      have : |f' (fun i ↦ if i.1 < k then x₀ else xi i)| - |f' fun i ↦ if i.1 < k + 1 then x₀ else xi i| ≤ c' ⟨k, h'⟩ := by
        apply le_trans (abs_sub_abs_le_abs_sub _ _)
        have : (fun i ↦ if i.1 < k + 1 then x₀ else xi i) = Function.update (fun i ↦ if i.1 < k then x₀ else xi i) ⟨k, by linarith [h']⟩ x₀ := by
          ext i
          if hik : i.1 < k then
            have : i.1 < k+1 := by linarith
            rw [if_pos this]
            have : i ≠ ⟨k, by linarith [h']⟩:= Fin.ne_of_lt hik
            rw [Function.update_of_ne this, if_pos hik]
          else
            if hik' : i.1 = k then
              have : i.1 < k+1 := by linarith
              rw [if_pos this]
              have : i = ⟨k, by linarith [h']⟩ := Fin.eq_mk_iff_val_eq.mpr hik'
              rw [this, Function.update_self]
            else
              have : ¬ i.1 < k + 1 := by
                simp only [not_lt] at hik
                simp only [not_lt]
                apply Nat.succ_le_of_lt
                exact Nat.lt_of_le_of_ne hik (fun a ↦ hik' (id (Eq.symm a)))
              rw [if_neg this]
              have : i ≠ ⟨k, by linarith [h']⟩ := Fin.ne_of_val_ne hik'
              rw [Function.update_of_ne this, if_neg hik]
        rw [this]
        apply hfι
      have : ∑ (i : Fin (k+1)), c' ⟨i.1, by linarith [i.2, h']⟩ = (∑ (i : Fin k), c' ⟨i.1, by linarith [i.2, h']⟩) + c' ⟨k, h'⟩ := by
        apply Fin.sum_univ_castSucc
      rw [this]
      linarith
  intro xi
  have h' := h m (Nat.le_refl m) xi
  have : (fun i : Fin m ↦ if ↑i < m then x₀ else xi i) = fun _ ↦ x₀ := by
    ext i
    rw [if_pos i.2]
  rw [this] at h'
  exact h'

lemma hAY (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (x₀ : 𝓧) (k : Fin m) (Xk : Fin k → 𝓧) (x : 𝓧) :
  expressionA μ X' f' k Xk ≤ expressionY μ X' f' (Fin.succ k) (Fin.snoc Xk x) := by
  rw [Y_snoc_eq k Xk x]
  apply ciInf_le _ x
  use -(|f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i)
  intro r ⟨x, heqr⟩
  rw [←heqr]
  apply (abs_le.mp _).1
  apply abs_expectation_le_of_abs_le_const
  filter_upwards with _
  apply bound_f' hfι x₀

lemma hBddAbove (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (x₀ : 𝓧) (k : Fin m) (Xk : Fin k → 𝓧) : BddAbove (Set.range fun x ↦
  ∫ (a : Ω), (fun ω ↦ f' fun i ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x else X' i ω) a ∂μ):= by
  use |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i
  intro r ⟨x, heqr⟩
  rw [←heqr]
  apply (abs_le.mp _).2
  apply abs_expectation_le_of_abs_le_const
  filter_upwards with _
  apply bound_f' hfι x₀

lemma hYB (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (x₀ : 𝓧) (k : Fin m) (Xk : Fin k → 𝓧) (x : 𝓧) :
  expressionB μ X' f' k Xk ≥ expressionY μ X' f' (Fin.succ k) (Fin.snoc Xk x) := by
  rw [Y_snoc_eq k Xk x]
  apply le_ciSup_of_le _ x (by apply le_refl)
  exact hBddAbove hfι x₀ k Xk

variable {m𝓧 : MeasurableSpace 𝓧}

lemma hmeasurableY
  (hX'' : ∀ i, Measurable (X' i))
  (hf'' : StronglyMeasurable f')
  (k : Fin m.succ) : Measurable (expressionY μ X' f' k) := by
  apply stronglyMeasurable_iff_measurable.mp
  apply StronglyMeasurable.integral_prod_left
  have : (Function.uncurry fun (x : Ω) (y : Fin k.1 → 𝓧) ↦ f' fun (i : Fin m) ↦ if h : i.1 < k.1 then y ⟨↑i, h⟩ else X' i x)
    = f' ∘ (fun xy : (Ω × (Fin k.1 → 𝓧)) ↦ fun (i : Fin m) ↦ if h : i.1 < k.1 then xy.2 ⟨↑i, h⟩ else X' i xy.1) := rfl
  rw [this]
  apply StronglyMeasurable.comp_measurable hf''
  apply measurable_pi_lambda
  intro i
  if h : i.1 < k.1 then
    have : (fun (c : Ω × (Fin k.1 → 𝓧)) ↦ if h : i.1 < k.1 then c.2 ⟨↑i, h⟩ else X' i c.1)
      = (fun c ↦ c ⟨i.1, h⟩) ∘ Prod.snd := by
      ext c
      rw [dif_pos h]
      simp only [Nat.succ_eq_add_one, Function.comp_apply]
    rw [this]
    apply Measurable.comp
    · apply measurable_pi_apply
    · exact measurable_snd
  else
    have : (fun (c : Ω × (Fin k.1 → 𝓧)) ↦ if h : i.1 < k.1 then c.2 ⟨↑i, h⟩ else X' i c.1) = (X' i) ∘ Prod.fst := by
      ext c
      rw [dif_neg h]
      simp
    rw [this]
    apply Measurable.comp
    · exact hX'' i
    · exact measurable_fst

lemma hYbdd (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (x₀ : 𝓧) (k : Fin m.succ) (Xk : Fin k → 𝓧) :
  |expressionY μ X' f' k Xk| ≤ |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i := by
  apply abs_expectation_le_of_abs_le_const
  filter_upwards with _
  apply bound_f' hfι x₀

variable [hnonempty𝓧 : Nonempty 𝓧]

lemma hintegrablelefts
  (hX'' : ∀ i, Measurable (X' i))
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f')
  {t'' : ℝ} (ht'' : t'' ≥ 0) (E : ℝ)
  (k : ℕ) (h : k ≤ m):
  Integrable (fun x ↦ Real.exp (t'' * ((expressionY μ X' f' ⟨k, Nat.lt_add_one_of_le h⟩ fun i ↦ X' (Fin.castLE h i) x) - E))) μ := by
  constructor
  · apply Measurable.aestronglyMeasurable
    apply Measurable.exp
    apply Measurable.const_mul
    apply Measurable.sub_const _ E
    have : (fun x ↦ expressionY μ X' f' ⟨k, Nat.lt_add_one_of_le h⟩ fun i ↦ X' (Fin.castLE h i) x)
      = expressionY μ X' f' ⟨k, Nat.lt_add_one_of_le h⟩ ∘ fun x ↦ fun i ↦ X' (Fin.castLE h i) x := rfl
    rw [this]
    apply (hmeasurableY hX'' hf'' ⟨k, Nat.lt_add_one_of_le h⟩).comp
    apply measurable_pi_lambda
    intro _
    apply hX''
  · let x₀ : 𝓧 := (Classical.inhabited_of_nonempty hnonempty𝓧).default
    let bdf := |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i
    apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ _ (t'' * (bdf-E)).exp
    filter_upwards with ω
    dsimp only [norm]
    rw [Real.abs_exp]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ht''
    apply tsub_le_tsub_right _ E
    apply le_of_max_le_left
    apply hYbdd hfι x₀ ⟨k, Nat.lt_add_one_of_le h⟩ fun i ↦ X' (Fin.castLE h i) ω

lemma hintegrableAB
  (hX'' : ∀ i, Measurable (X' i))
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f')
  (k : Fin m) (Xk : Fin k → 𝓧) (x : 𝓧) :
  Integrable (fun a ↦ f' fun i ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x else X' i a) μ := by
  let x₀ : 𝓧 := (Classical.inhabited_of_nonempty hnonempty𝓧).default
  constructor
  · apply @AEStronglyMeasurable.comp_aemeasurable (Fin m → 𝓧) ℝ _ f' Ω
    apply hf''.aestronglyMeasurable
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro i
    if h₀ : i.1 < k.1 then
      have : (fun x_1 ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x else X' i x_1) = fun _ ↦ Xk ⟨i.1, h₀⟩ := by
        ext x
        rw [dif_pos h₀]
      rw [this]
      exact measurable_const
    else
      if h₁ : i.1 = k.1 then
        have : (fun x_1 ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x else X' i x_1) = fun _ ↦ x := by
          ext x
          rw [dif_neg h₀, if_pos h₁]
        rw [this]
        exact measurable_const
      else
        have : (fun x_1 ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x else X' i x_1) = fun x_1 ↦ X' i x_1 := by
          ext x
          rw [dif_neg h₀, if_neg h₁]
        rw [this]
        exact hX'' i
  · apply MeasureTheory.HasFiniteIntegral.of_bounded _
    exact |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i
    filter_upwards with _
    apply bound_f' hfι x₀

lemma hAB
  (hX'' : ∀ i, Measurable (X' i))
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f')
  (k : Fin m) (Xk : Fin k → 𝓧) :
  expressionB μ X' f' k Xk ≤ expressionA μ X' f' k Xk + c' k := by
  let x₀ : 𝓧 := (Classical.inhabited_of_nonempty hnonempty𝓧).default
  apply le_ciInf_add
  intro x₁
  apply (ciSup_le_iff (hBddAbove hfι x₀ k Xk)).mpr
  intro x₂
  calc
    _ ≤ ∫ (ω : Ω), (f' fun i ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x₁ else X' i ω) + c' k ∂μ := by
      apply integral_mono
      exact hintegrableAB hX'' hfι hf'' k Xk x₂
      exact integrable_add_const_iff.mpr (hintegrableAB hX'' hfι hf''  k Xk x₁)
      intro ω
      have : (fun i : Fin m ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x₁ else X' i ω)
        = Function.update (fun i : Fin m ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x₂ else X' i ω) k x₁ := by
          ext i
          if h : i.1 < k.1 then
            have : i ≠ k := Fin.ne_of_lt h
            rw [dif_pos h, Function.update_of_ne this, dif_pos h]
          else
            rw [dif_neg h]
            if h': i.1 = k.1 then
              have : i=k :=  Fin.eq_of_val_eq h'
              rw [if_pos h', this, Function.update_self]
            else
              rw [if_neg h']
              have : i ≠ k := fun a ↦ h' (congrArg Fin.val a)
              rw [Function.update_of_ne this, dif_neg h, if_neg h']
      dsimp
      rw [this]
      apply tsub_le_iff_left.mp
      apply le_of_max_le_left
      apply hfι
    _ = (∫ (ω : Ω), f' fun i ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if i.1 = k.1 then x₁ else X' i ω ∂μ)
        + (∫ (_ : Ω), c' k ∂μ) := integral_add (hintegrableAB hX'' hfι hf'' k Xk x₁) (integrable_const (c' k))
    _ = _ := add_left_cancel_iff.mpr (expectation_const (c' k))

-- we use independency for the martingale property
-- ∫ Y(x_0, …, x_{k-1}, X_k) dΩ = Y(x_0, …, x_{m-1})
-- use double_integral_indep_eq_integral
lemma hmartingale
  (hX'' : ∀ i, Measurable (X' i))
  (hIndep' : iIndepFun X' μ)
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f')
  (k : Fin m) (Xk : Fin k → 𝓧) :
  ∫ (ω : Ω), expressionY μ X' f' k.succ (Fin.snoc Xk (X' k ω)) ∂μ = expressionY μ X' f' k.castSucc Xk := by
  let S : Finset (Fin m) := {i : Fin m | i.1 > k.1}
  let T : Finset (Fin m) := {k}
  have hST : Disjoint T S := by
    apply Finset.disjoint_singleton_left.mpr
    simp only [gt_iff_lt, Fin.val_fin_lt, Finset.mem_filter, Finset.mem_univ, lt_self_iff_false,
      and_false, not_false_eq_true, S]
  have hindep := ProbabilityTheory.iIndepFun.indepFun_finset T S hST hIndep' hX''
  let toelS (i : Fin m) (h : ¬ i.1 < k.1) (h' : ¬ i.1 = k.1): S := by
    use i
    simp only [gt_iff_lt, Fin.val_fin_lt, Finset.mem_filter, Finset.mem_univ, true_and, S]
    simp only [Fin.val_fin_lt, not_lt] at h
    exact lt_of_le_of_ne h fun a ↦ h' (congrArg Fin.val (id (Eq.symm a)))
  let elT : T := ⟨k, Finset.mem_singleton.mpr rfl⟩
  let F : (T → 𝓧) × (S → 𝓧) → ℝ := fun ⟨t,s⟩ ↦
    f' (fun i ↦ if h : i.1 < k.1 then Xk ⟨i.1,h⟩
      else if h': i.1 = k.1 then t elT
      else s (toelS i h h'))
  let gT : Ω → T → 𝓧 := fun ω t ↦ X' t.1 ω
  let gS : Ω → S → 𝓧 := fun ω s ↦ X' s.1 ω

  have hlefteq  : ∫ (ω : Ω), expressionY μ X' f' k.succ (Fin.snoc Xk (X' k ω)) ∂μ
    = ∫ (ω : Ω), ∫ (a : Ω), F ⟨(gT ω), (gS a)⟩ ∂μ ∂μ := by
    dsimp only [F]
    apply integral_congr_ae
    filter_upwards with ω
    apply integral_congr_ae
    filter_upwards with a
    apply congr rfl
    ext i
    if h : i.1 < k.1 then
      rw [dif_pos h]
      have : i.1 < k.succ := Nat.lt_succ_of_lt h
      rw [dif_pos this]
      exact Fin.snoc_castSucc (α := fun _ ↦ 𝓧) (p := Xk) (x := X' k ω) (i := ⟨i.1, h⟩)
    else
      rw [dif_neg h]
      if h' : i.1 = k.1 then
        rw [dif_pos h', h']
        have : k.1 < k.succ := Nat.lt_add_one k.1
        rw [dif_pos this]
        exact Fin.snoc_last (α := fun _ ↦ 𝓧) (p := Xk) (x := X' k ω)
      else
        rw [dif_neg h']
        have : ¬ i.1 < k.succ := by
          simp only [Fin.val_succ, not_lt]
          simp only [Fin.val_fin_lt, not_lt] at h
          exact Nat.lt_of_le_of_ne h fun a ↦ h' (id (Eq.symm a))
        rw [dif_neg this]
  apply Eq.trans hlefteq
  have hrighteq : expressionY μ X' f' k.castSucc Xk = ∫ (ω : Ω), F ⟨(gT ω), (gS ω)⟩ ∂μ := by
    dsimp only [F]
    apply integral_congr_ae
    filter_upwards with ω
    apply congr rfl
    ext i
    if h : i.1 < k.1 then
      rw [dif_pos h]
      have : i.1 < k.castSucc.1 := h
      rw [dif_pos this]
      rfl
    else
      rw [dif_neg h]
      have : ¬ i.1 < k.castSucc.1 := h
      rw [dif_neg this]
      if h' : i.1 = k.1 then
        rw [dif_pos h']
        dsimp [gT]
        have : i = k := Fin.eq_of_val_eq h'
        rw [this]
      else
        rw [dif_neg h']
  apply Eq.trans _ hrighteq.symm
  apply double_integral_indep_eq_integral
  · apply StronglyMeasurable.comp_measurable hf''
    apply measurable_pi_iff.mpr
    intro i
    if h : i < k then
      have : (fun x : (T → 𝓧) × (S → 𝓧) ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if h' : i.1 = k.1 then x.1 elT else x.2 (toelS i h h')) = fun _ ↦ Xk ⟨i.1, h⟩ := by
        simp only [Fin.val_fin_lt]
        ext x
        rw [dif_pos h]
      rw [this]
      exact measurable_const
    else
      if h' : i.1 = k.1 then
        have : (fun x : (T → 𝓧) × (S → 𝓧) ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if h' : i.1 = k.1 then x.1 elT else x.2 (toelS i h h')) = fun x ↦ x.1 elT := by
          simp only [Fin.val_fin_lt]
          ext x
          rw [dif_neg h, dif_pos h']
        rw [this]
        exact Measurable.eval measurable_fst
      else
        have : (fun x : (T → 𝓧) × (S → 𝓧) ↦ if h : i.1 < k.1 then Xk ⟨↑i, h⟩ else if h' : i.1 = k.1 then x.1 elT else x.2 (toelS i h h')) = fun x ↦ x.2 (toelS i h h') := by
          simp only [Fin.val_fin_lt]
          ext x
          rw [dif_neg h, dif_neg h']
        rw [this]
        exact Measurable.eval measurable_snd
  · apply Measurable.aemeasurable
    exact measurable_pi_lambda gT fun a ↦ hX'' ↑a
  · apply Measurable.aemeasurable
    exact measurable_pi_lambda gS fun a ↦ hX'' ↑a
  · exact hindep
  · let x₀ : 𝓧 := (Classical.inhabited_of_nonempty hnonempty𝓧).default
    apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ F (|f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i)
    filter_upwards with ⟨t, s⟩
    apply bound_f' hfι x₀

lemma hhoeffding_V
  (hX'' : ∀ i, Measurable (X' i))
  (hIndep' : iIndepFun X' μ)
  {c' : Fin m → ℝ}
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f') (t'' : ℝ)
  (k : Fin m) (Xk : Fin k → 𝓧) : ∫ (ω : Ω), (t'' * (expressionV μ X' f' k Xk ω)).exp ∂μ ≤ (t''^2 * (c' k)^2 / 8).exp := by
  let Y : Π (k: Fin m.succ), (Fin k → 𝓧) → ℝ := expressionY μ X' f'
  let A : Π (k: Fin m), (Fin k → 𝓧) → ℝ := expressionA μ X' f'
  let B : Π (k: Fin m), (Fin k → 𝓧) → ℝ := expressionB μ X' f'
  let x₀ : 𝓧 := (Classical.inhabited_of_nonempty hnonempty𝓧).default
  let a := A k Xk - Y k.castSucc Xk
  let b := B k Xk - Y k.castSucc Xk
  have hmeasurable : Measurable (fun x ↦ Fin.snoc Xk (X' k x) : Ω → Fin (k.1+1) → 𝓧):= by
    apply measurable_pi_lambda
    intro i
    if h : i.1 < k.1 then
        have : (fun ω ↦ (Fin.snoc Xk (X' k ω) : Fin k.succ → 𝓧) i) = fun _ ↦ Xk ⟨i.1, h⟩ := by
          ext ω
          dsimp [Fin.snoc]
          rw [dif_pos h]
          exact rfl
        exact (congrArg Measurable this).mpr measurable_const
    else
      have : (fun ω ↦ (Fin.snoc Xk (X' k ω) : Fin k.succ → 𝓧) i) = fun ω ↦ X' k ω := by
        ext ω
        dsimp [Fin.snoc]
        rw [dif_neg h]
      exact (congrArg Measurable this).mpr (hX'' k)
  calc
    _ ≤ ((t''^2 * (b - a)^2 / 8).exp : ℝ) := by
      apply hoeffding μ t'' a b
      · apply Measurable.aemeasurable
        apply Measurable.add_const _ (-Y k.castSucc Xk)
        apply (hmeasurableY hX'' hf'' k.succ).comp
        exact hmeasurable
      · filter_upwards with ω
        dsimp only [Set.Icc]
        constructor
        · exact tsub_le_tsub_right (hAY hfι x₀ k Xk (X' k ω)) (Y k.castSucc Xk)
        · exact tsub_le_tsub_right (hYB hfι x₀ k Xk (X' k ω)) (Y k.castSucc Xk)
      · calc
          _ = (∫ (ω : Ω), Y k.succ (Fin.snoc Xk (X' k ω)) ∂μ) - ∫ (_ : Ω), Y k.castSucc Xk ∂μ := by
            apply integral_sub
            · constructor
              · apply aestronglyMeasurable_iff_aemeasurable.mpr
                apply Measurable.comp_aemeasurable'
                · exact hmeasurableY hX'' hf'' k.succ
                · apply Measurable.aemeasurable
                  exact hmeasurable
              · apply MeasureTheory.HasFiniteIntegral.of_bounded _
                exact max (B k Xk) (-(A k Xk))
                filter_upwards with ω
                calc
                  _ ≤ max (Y k.succ (Fin.snoc Xk (X' k ω))) (-Y k.succ (Fin.snoc Xk (X' k ω))) :=
                    Preorder.le_refl ‖Y k.succ (Fin.snoc Xk (X' k ω))‖
                  _ ≤ max (Y k.succ (Fin.snoc Xk (X' k ω))) (-(A k Xk)) := by
                    apply max_le_max_left (Y k.succ (Fin.snoc Xk (X' k ω)))
                    exact neg_le_neg_iff.mpr (hAY hfι x₀ k Xk (X' k ω))
                  _ ≤ _ := max_le_max_right (-A k Xk) (hYB hfι x₀ k Xk (X' k ω))
            · exact integrable_const (Y k.castSucc Xk)
          _ = (∫ (ω : Ω), Y k.succ (Fin.snoc Xk (X' k ω)) ∂μ) - Y k.castSucc Xk := by
            apply sub_right_inj.mpr
            exact expectation_const (Y k.castSucc Xk)
          _ = _ := sub_eq_zero_of_eq (hmartingale hX'' hIndep' hfι hf'' k Xk)
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg t'')
      have : b - a = B k Xk - A k Xk := by simp only [sub_sub_sub_cancel_right, b, a]
      rw [this]
      apply pow_le_pow_left₀ _ _ 2
      · apply sub_nonneg.mpr
        let c : ℝ := μ[fun ω ↦ f' (fun i ↦ if h : i.1 < k.1 then Xk ⟨i.1,h⟩ else if i.1 = k.1 then x₀ else X' i ω)]
        calc
          _ ≤ c := le_of_le_of_eq (hAY hfι x₀ k Xk x₀) (Y_snoc_eq k Xk x₀)
          _ ≤ _ := (le_iff_le_of_cmp_eq_cmp (congrFun (congrArg cmp (Y_snoc_eq k Xk x₀)) (B k Xk))).mp
                (hYB hfι x₀ k Xk x₀)
      · exact tsub_le_iff_left.mpr (hAB hX'' hfι hf'' k Xk)

lemma heqind
  (hX'' : ∀ i, Measurable (X' i))
  (hIndep' : iIndepFun X' μ)
  {c' : Fin m → ℝ}
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f')
  {t'' : ℝ} (ht'' : t'' ≥ 0)
  (x₀ : 𝓧) (k : ℕ) (h : k ≤ m) :
  ∫ (ω : Ω), (t'' *(expressionY μ X' f' ⟨k,Nat.lt_add_one_of_le h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h i) ω) - expressionY μ X' f' 0 (fun _ ↦ x₀))).exp ∂μ
    ≤ ((t'' ^2 * ∑ (i : Fin k), c' (Fin.castLE h i) ^ 2)/8).exp := by
  let Y : Π (k: Fin m.succ), (Fin k → 𝓧) → ℝ := expressionY μ X' f'
  let V : Π (k : Fin m), (Fin k → 𝓧) → Ω → ℝ := expressionV μ X' f'
  let bdf := |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i
  let E := Y 0 (fun _ ↦ x₀)

  induction' k with k ih
  · simp only [Nat.succ_eq_add_one, Fin.val_zero, not_lt_zero, ↓reduceDIte,
    sub_self, mul_zero, Real.exp_zero, integral_const, probReal_univ, smul_eq_mul, mul_one,
    Finset.univ_eq_empty, Finset.sum_empty, zero_div, le_refl, expressionY]
  · have ih := ih <| Nat.le_of_succ_le h
    calc
      _ = ∫ (ω : Ω), ∫ (ω' : Ω), (t'' *(Y ⟨k+1,Nat.lt_add_one_of_le h⟩
          (Fin.snoc (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) (X' ⟨k,h⟩ ω')) - E)).exp ∂μ ∂μ := by
        let S : Finset (Fin m) := {i : Fin m | i.1 < k}
        let T : Finset (Fin m) := {⟨k,h⟩}
        have hST : Disjoint S T := by
          apply Finset.disjoint_singleton_right.mpr
          simp only [Finset.mem_filter, Finset.mem_univ, lt_self_iff_false, and_false,
            not_false_eq_true, S]
        have hindep := ProbabilityTheory.iIndepFun.indepFun_finset S T hST hIndep' hX''
        let toelS (i : Fin k) : S := by
          use (Fin.castLE h (Fin.castSucc i))
          simp only [Fin.castLE_castSucc, Finset.mem_filter, Finset.mem_univ,
            Fin.val_castLE, Fin.is_lt, and_self, S]
        let elT : T := ⟨⟨k,h⟩, Finset.mem_singleton.mpr rfl⟩
        let F : (S → 𝓧) × (T → 𝓧) → ℝ := fun ⟨s,t⟩ ↦
          Real.exp (t'' * (Y ⟨k + 1, Nat.lt_add_one_of_le h⟩ (Fin.snoc (fun i ↦ s (toelS i)) (t elT)) - E))
        let gT : Ω → T → 𝓧 := fun ω t ↦ X' t.1 ω
        let gS : Ω → S → 𝓧 := fun ω s ↦ X' s.1 ω
        have hlefteq : ∫ (ω : Ω), Real.exp (t'' * ((Y ⟨k + 1, Nat.lt_add_one_of_le h⟩ fun i ↦ X' (Fin.castLE h i) ω) - E)) ∂μ
          = ∫ (ω : Ω), F ⟨gS ω, gT ω⟩ ∂μ := by
          apply congrArg
          ext ω
          apply congrArg
          apply congrArg
          apply sub_left_inj.mpr
          apply congrArg
          ext i
          if h': i.1 < k then
            dsimp only [Fin.snoc]
            rw [dif_pos h']
            congr
          else
            dsimp only [Fin.snoc]
            rw [dif_neg h']
            simp only [cast_eq, gT]
            have : i.1 = k := by
              simp only [Nat.succ_eq_add_one, not_lt] at h'
              exact Nat.eq_of_le_of_lt_succ h' i.2
            apply congrFun
            apply congrArg
            exact Fin.eq_mk_iff_val_eq.mpr this
        have hrighteq : ∫ (ω : Ω), ∫ (ω' : Ω), Real.exp (t'' * (Y ⟨k + 1, Nat.lt_add_one_of_le h⟩
          (Fin.snoc (fun i ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) (X' ⟨k, h⟩ ω')) - E)) ∂μ ∂μ
          = ∫ (ω : Ω), ∫ (ω' : Ω), F ⟨gS ω, gT ω'⟩ ∂μ ∂μ := by
          apply congrArg
          ext ω
          apply congrArg
          ext ω'
          apply congrArg
          apply congrArg
          apply sub_left_inj.mpr
          apply congrArg
          ext i
          apply congrArg₂
          · dsimp [gT]
          · dsimp [gS]
        rw [hlefteq, hrighteq]
        apply Eq.symm

        apply double_integral_indep_eq_integral
        · apply StronglyMeasurable.comp_measurable Real.measurable_exp.stronglyMeasurable
          apply Measurable.comp (measurable_const_mul t'')
          apply Measurable.sub_const _ E
          exact MeasurableSpace.pi
          exact MeasurableSpace.pi
          apply Measurable.comp (hmeasurableY hX'' hf'' ⟨k + 1, Nat.lt_add_one_of_le h⟩)
          apply measurable_pi_iff.mpr
          intro i
          if h' : i.1 < k then
            have : (fun x : (S → 𝓧) × (T → 𝓧) ↦ @Fin.snoc k (fun _ ↦ 𝓧) (fun i ↦ x.1 (toelS i)) (x.2 elT) i)
              = (fun x ↦ x (toelS ⟨i, h'⟩)) ∘ Prod.fst := by
              ext x
              dsimp [Fin.snoc]
              rw [dif_pos h']
              rfl
            rw [this]
            apply Measurable.comp _ measurable_fst
            exact measurable_pi_apply (toelS ⟨↑i, h'⟩)
          else
            have : (fun x : (S → 𝓧) × (T → 𝓧) ↦ @Fin.snoc k (fun _ ↦ 𝓧) (fun i ↦ x.1 (toelS i)) (x.2 elT) i)
              = (fun x ↦ x elT) ∘ Prod.snd := by
              ext x
              dsimp [Fin.snoc]
              rw [dif_neg h']
            rw [this]
            apply Measurable.comp _ measurable_snd
            exact measurable_pi_apply elT
        · apply Measurable.aemeasurable
          exact measurable_pi_lambda gS fun a ↦ hX'' ↑a
        · apply Measurable.aemeasurable
          exact measurable_pi_lambda gT fun a ↦ hX'' ↑a
        · exact hindep
        · apply @MeasureTheory.HasFiniteIntegral.of_bounded _ _ _ _ _ _ F (t''*(bdf-E)).exp
          filter_upwards with ⟨a, t⟩
          dsimp only [F, norm]
          rw [Real.abs_exp]
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ ht''
          apply tsub_le_tsub_right _ E
          apply le_of_max_le_left
          apply hYbdd hfι x₀
      _ = ∫ (ω : Ω), ∫ (ω' : Ω), (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)).exp
        * (t'' *(V ⟨k,h⟩ fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) ω').exp ∂μ ∂μ := by
        dsimp only [V]
        apply congrArg
        ext ω
        apply congrArg
        ext ω'
        calc
          _ = (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)
          + t'' *(V ⟨k,h⟩ fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) ω').exp := by
            apply congrArg
            rw [←mul_add]
            apply congrArg
            dsimp only [V, Y, expressionV]
            simp only [Nat.succ_eq_add_one, Fin.castLE_castSucc, Fin.succ_mk,
              Fin.castSucc_mk, sub_add_sub_cancel']
          _ = _ := by apply Real.exp_add
      _ = ∫ (ω : Ω), (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)).exp
        * ∫ (ω' : Ω), (t'' *(V ⟨k,h⟩ fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) ω').exp ∂μ ∂μ := by
        apply congrArg
        ext ω
        exact
          integral_const_mul
            (Real.exp (t'' * ((Y ⟨k, Nat.lt_succ_of_lt h⟩ fun i ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)))
            fun a ↦ Real.exp (t'' * V ⟨k, h⟩ (fun i ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) a)
      _ ≤ ∫ (ω : Ω), (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)).exp
        * (t'' ^2 * (c' ⟨k, h⟩)^2 / 8).exp ∂μ := by
        have (h : k ≤ m) :
          Integrable (fun x ↦ Real.exp (t'' * ((Y ⟨k, Nat.lt_add_one_of_le h⟩ fun i ↦ X' (Fin.castLE h i) x) - E))) μ :=
            hintegrablelefts hX'' hfι hf'' ht'' E k h
        have hintegrableleft := this (Nat.le_of_succ_le h)
        simp only [Nat.succ_eq_add_one] at hintegrableleft
        apply integral_mono
        · have : (fun (ω : Ω) ↦ (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)).exp
          * ∫ (ω' : Ω), (t'' *(V ⟨k,h⟩ fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) ω').exp ∂μ)
          = (fun (ω : Ω) ↦ (∫ (ω' : Ω), (t'' *(V ⟨k,h⟩ fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) ω').exp ∂μ)
        * (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)).exp) := by
            ext ω
            rw [mul_comm]
          rw [this]
          apply Integrable.bdd_mul (c:= (t'' * (bdf + bdf)).exp)
          · simp only [Nat.succ_eq_add_one, Fin.castLE_castSucc]
            exact hintegrableleft
          · apply StronglyMeasurable.aestronglyMeasurable
            apply StronglyMeasurable.integral_prod_left
            apply StronglyMeasurable.comp_measurable Real.measurable_exp.stronglyMeasurable
            apply Measurable.comp
            · exact measurable_const_mul t''
            · apply Measurable.sub
              · apply (hmeasurableY hX'' hf'' (⟨k, h⟩ : Fin m).succ).comp
                apply measurable_pi_lambda
                intro i
                if h' : i.1 < k then
                  have : (fun c : Ω × Ω ↦
                    @Fin.snoc k (fun _ ↦ 𝓧) (fun i : Fin k ↦ X' (Fin.castLE h (Fin.castSucc i)) c.2) (X' ⟨k, h⟩ c.1) i)
                    = fun c ↦ X' (Fin.castLE h i) c.2 := by
                    ext c
                    dsimp only [Fin.snoc]
                    rw [dif_pos h']
                    simp
                  exact (congrArg Measurable this).mpr ((hX'' _).comp measurable_snd)
                else
                  have : (fun c : Ω × Ω ↦
                    @Fin.snoc k (fun _ ↦ 𝓧) (fun i : Fin k ↦ X' (Fin.castLE h (Fin.castSucc i)) c.2) (X' ⟨k, h⟩ c.1) i)
                    = fun c ↦ X' ⟨k, h⟩ c.1 := by
                    ext c
                    dsimp only [Fin.snoc]
                    rw [dif_neg h']
                    simp
                  exact (congrArg Measurable this).mpr ((hX'' _).comp measurable_fst)
              · have : (fun a : Ω × Ω ↦ Y (⟨k, h⟩ : Fin m).castSucc fun i ↦ X' (Fin.castLE h (Fin.castSucc i)) a.2)
                  = (Y (⟨k, h⟩ : Fin m).castSucc) ∘ (fun a : Ω ↦ fun i ↦ X' (Fin.castLE h (Fin.castSucc i)) a) ∘ Prod.snd := rfl
                dsimp
                dsimp at this
                rw [this]
                apply (hmeasurableY hX'' hf'' (⟨k, h⟩ : Fin m).castSucc).comp
                apply Measurable.comp _ measurable_snd
                apply measurable_pi_lambda
                intro i
                apply hX''
          · filter_upwards with ω
            apply abs_expectation_le_of_abs_le_const
            filter_upwards with ω'
            rw [Real.abs_exp]
            apply Real.exp_le_exp.mpr
            apply mul_le_mul_of_nonneg_left _ ht''
            dsimp only [V]
            apply (le_abs.mpr (Or.inl le_rfl)).trans
            apply (abs_sub _ _).trans
            apply add_le_add
            · apply hYbdd hfι x₀
            · apply hYbdd hfι x₀ (⟨k, h⟩ : Fin m).castSucc fun i ↦ X' (Fin.castLE h (Fin.castSucc i)) ω
        · apply Integrable.mul_const (by simp; exact hintegrableleft) (Real.exp (t'' ^ 2 * c' ⟨k, h⟩ ^ 2 / 8))
        · intro ω
          apply mul_le_mul_of_nonneg_left
          · apply hhoeffding_V hX'' hIndep' hfι hf'' t''
          · apply Real.exp_nonneg
      _ = (∫ (ω : Ω), (t'' *(Y ⟨k,Nat.lt_succ_of_lt h⟩ (fun (i : Fin k) ↦ X' (Fin.castLE h (Fin.castSucc i)) ω) - E)).exp ∂μ)
        * (t'' ^2 * (c' ⟨k, h⟩)^2 / 8).exp := by
        apply integral_mul_const
      _ ≤ Real.exp ((t'' ^2 * ∑ i : Fin k, c' (Fin.castLE (Nat.le_of_succ_le h) i) ^ 2) / 8)
        * (t'' ^2 * (c' ⟨k, h⟩)^2 / 8).exp := by
        apply mul_le_mul_of_nonneg_right
        · simp only [Nat.succ_eq_add_one, Fin.castLE_castSucc]
          exact ih
        · apply Real.exp_nonneg
      _ = Real.exp ((t'' ^2 * ∑ i : Fin k, c' (Fin.castLE (Nat.le_of_succ_le h) i) ^ 2) / 8
        + t'' ^2 * (c' ⟨k, h⟩)^2 / 8) := by
          apply Eq.symm
          apply Real.exp_add
      _ = _ := by
        apply congrArg
        rw [←add_div, ←mul_add]
        apply congrArg (fun (a:ℝ) ↦ t''^2 * a / 8)
        exact Eq.symm (Fin.sum_univ_castSucc fun i ↦ c' (Fin.castLE h i) ^ 2)

theorem mcdiarmid_inequality_aux
  (hX'' : ∀ i, Measurable (X' i))
  (hIndep' : iIndepFun X' μ)
  {c' : Fin m → ℝ}
  (hfι : ∀ (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : StronglyMeasurable f')
  {ε : ℝ} (hε : ε ≥ 0)
  {t : ℝ} (ht : t ≥ 0) (ht' : t * ∑ i, (c' i) ^ 2 ≤ 1) :
  (μ (fun ω : Ω ↦ (f' ∘ (Function.swap X')) ω - μ[f' ∘ (Function.swap X')] ≥ ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp := by

  let Y : Π (k: Fin m.succ), (Fin k → 𝓧) → ℝ := expressionY μ X' f'

  -- inequalities about Y, A, B are not hard to prove
  let x₀ : 𝓧 := (Classical.inhabited_of_nonempty hnonempty𝓧).default
  let bdf := |f' (fun _ ↦ x₀)| + ∑ i : Fin m, c' i

  let t'' := 4 * ε * t
  have ht'' : t'' ≥ 0 := by
    apply mul_nonneg
    apply mul_nonneg
    norm_num
    apply hε
    exact ht

  let E := Y 0 (fun _ ↦ x₀)

  have := heqind hX'' hIndep' hfι hf'' ht'' x₀  m le_rfl
  simp only [Nat.succ_eq_add_one, Fin.castLE_rfl, id_eq, Fin.is_lt, ↓reduceDIte, Fin.eta,
    integral_const, smul_eq_mul, Fin.val_zero,
    not_lt_zero, expressionY] at this
  have hintegrable :
    Integrable (fun x ↦ Real.exp (t'' * ((Y ⟨m, Nat.lt_add_one_of_le le_rfl⟩ fun i ↦ X' (Fin.castLE le_rfl i) x) - E))) μ
    := hintegrablelefts hX'' hfι hf'' ht'' E m le_rfl
  simp only [Nat.succ_eq_add_one, Fin.castLE_rfl, id_eq, Fin.is_lt, ↓reduceDIte, Fin.eta,
    integral_const, smul_eq_mul, Fin.val_zero,
    not_lt_zero, Y, expressionY, E] at hintegrable
  convert (ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht'' hintegrable).trans _
  · rfl
  · simp only [Function.comp_apply, ge_iff_le, probReal_univ, one_mul]
    rfl
  dsimp only [mgf]
  calc
    _ ≤ Real.exp (-t'' * ε) * Real.exp ((t'' ^ 2 * ∑ x : Fin m, c' x ^ 2) / 8) := by
      apply mul_le_mul_of_nonneg_left this
      apply Real.exp_nonneg
    _ ≤ _ := by
      rw [←Real.exp_add]
      apply Real.exp_monotone
      simp only [neg_mul, neg_add_le_iff_le_add, le_add_neg_iff_add_le, t'']
      calc
        _ = 2 * ε ^ 2 * t * (t * ∑ x : Fin m, c' x ^ 2) + 2 * ε ^ 2 * t := by ring
        _ ≤ 2 * ε ^ 2 * t * 1 + 2 * ε ^ 2 * t := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left ht'
          apply mul_nonneg _ ht
          norm_num
          exact sq_nonneg ε
        _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]

omit hnonempty𝓧 in
lemma bounded_difference_iff (f : (ι → 𝓧) → ℝ) (c : ι → ℝ):
  (∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f x - f (Function.update x i x')| ≤ c i)
   ↔ ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), f x - f (Function.update x i x') ≤ c i := by
  constructor
  · intro h i xi x'
    exact le_of_max_le_left (h i xi x')
  · intro h i xi x'
    apply abs_sub_le_iff.mpr
    constructor
    · exact h i xi x'
    · have : xi = Function.update (Function.update xi i x') i (xi i) := by
        simp only [Function.update_idem, Function.update_eq_self]
      nth_rewrite 2 [this]
      exact h i (Function.update xi i x') (xi i)

variable  [Fintype ι]

theorem mcdiarmid_inequality_pos
  (X : ι → Ω → 𝓧) (hX : ∀ i, Measurable (X i))
  (hX' : iIndepFun X μ) {f : (ι → 𝓧) → ℝ}
  {c : ι → ℝ}
  (hf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f x - f (Function.update x i x')| ≤ c i)
  (hf' : Measurable f)
  {ε : ℝ} (hε : ε ≥ 0)
  {t : ℝ} (ht' : t * ∑ i, (c i) ^ 2 ≤ 1) :
  (μ (fun ω : Ω ↦ (f ∘ (Function.swap X)) ω - μ[f ∘ (Function.swap X)] ≥ ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp := by
  let m := Fintype.card ι
  let ιm : ι ≃ Fin m := Fintype.equivFinOfCardEq rfl
  let X' := X ∘ ιm.symm
  let f' := f ∘ (fun s ↦ s ∘ ιm)
  let c' := c ∘ ιm.symm

  have hfι (i : Fin m) (x : Fin m → 𝓧) (x' : 𝓧) : |f' x - f' (Function.update x i x')| ≤ c' i := by
    dsimp [f']
    rw [Function.update_comp_equiv x ιm i x']
    apply hf

  have hf'' : StronglyMeasurable f' := by
    apply hf'.stronglyMeasurable.comp_measurable
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_pi_apply (ιm i)

  have hIndep' : iIndepFun X' μ := by
    apply ProbabilityTheory.iIndepFun.comp_right hX'
    exact Equiv.injective ιm.symm

  have hX'' := fun i ↦ hX (ιm.symm i)

  have ht'' : t * ∑ (i' : Fin m), c' i' ^2 ≤ 1 := by
    have : ∑ (i' : Fin m), c' i' ^2 = ∑ (i : ι), c i ^2 := by
      exact Fintype.sum_equiv ιm.symm (fun x ↦ c' x ^ 2) (fun x ↦ c x ^ 2) (congrFun rfl)
    rw [this]
    assumption
  if ht : t ≥ 0 then
    have := mcdiarmid_inequality_aux hX'' hIndep' hfι hf'' hε ht ht''
    have eq : (f' ∘ Function.swap fun i ↦ X (ιm.symm i)) = (f ∘ Function.swap X) := by
      dsimp only [f']
      ext ω
      simp only [Function.comp_apply]
      apply congrArg
      ext i
      dsimp [Function.swap]
      simp
    rw [eq] at this
    exact this
  else
    calc
      _ ≤ (1 : ENNReal).toReal := by
        apply ENNReal.toReal_mono
        exact ENNReal.one_ne_top
        apply MeasureTheory.prob_le_one
      _ = (1 : ℝ) := rfl
      _ ≤ _ := by
        apply Real.one_le_exp
        simp only [ge_iff_le, not_le] at ht
        apply mul_nonneg_of_nonpos_of_nonpos
        · norm_num
          exact sq_nonneg ε
        · exact le_of_lt ht


theorem mcdiarmid_inequality_neg
  (X : ι → Ω → 𝓧) (hX : ∀ i, Measurable (X i))
  (hX' : iIndepFun X μ) (f : (ι → 𝓧) → ℝ)
  (c : ι → ℝ)
  (hf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f x - f (Function.update x i x')| ≤ c i)
  (hf' : Measurable f)
  (ε : ℝ) (hε : ε ≥ 0)
  (t : ℝ) (ht' : t * ∑ i, (c i) ^ 2 ≤ 1):
  (μ (fun ω : Ω ↦ (f ∘ (Function.swap X)) ω - μ[f ∘ (Function.swap X)] ≤ -ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp := by
  have hmf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |(-f) x - (-f) (Function.update x i x')| ≤ c i := by
    intro i x x'
    rw [←abs_neg]
    simp only [Pi.neg_apply, sub_neg_eq_add, neg_add_rev, neg_neg]
    rw [add_comm]
    apply hf
  have hmf' : Measurable (-f) := by
    apply Measurable.comp measurable_neg hf'
  have : (fun ω ↦ (f ∘ Function.swap X) ω - ∫ (a : Ω), (f ∘ Function.swap X) a ∂μ ≤ -ε)
    = (fun ω ↦ ((-f) ∘ Function.swap X) ω - ∫ (a : Ω), ((-f) ∘ Function.swap X) a ∂μ ≥ ε) := by
    ext ω
    have : ((-f) ∘ Function.swap X) ω - ∫ (a : Ω), ((-f) ∘ Function.swap X) a ∂μ
      = -((f ∘ Function.swap X) ω - ∫ (a : Ω), (f ∘ Function.swap X) a ∂μ) := by
      simp only [Function.comp_apply, Pi.neg_apply, neg_sub]
      rw [integral_neg]
      ring_nf
    rw [this]
    exact le_neg
  rw [this]
  apply mcdiarmid_inequality_pos X hX hX' hmf hmf' hε ht'

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

theorem mcdiarmid_inequality_pos'
  {X' : Ω → 𝓧} (hX'' : Measurable X')
  {f' : (ι → 𝓧) → ℝ}
  {c' : ι → ℝ}
  (hfι : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : Measurable f')
  {ε : ℝ} (hε : ε ≥ 0)
  {t : ℝ} (ht' : t * ∑ i, (c' i) ^ 2 ≤ 1) :
  (μⁿ (fun ω : ι → Ω ↦ (f' (X' ∘ ω)) - μⁿ[fun ω : ι → Ω ↦ f' (X' ∘ ω)] ≥ ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp := by
  let X : ι → (ι → Ω) → 𝓧 := fun i ω ↦ X' (ω i)
  have hX : ∀ i, Measurable (X i) := fun i ↦ by measurability
  have hX' : iIndepFun X μⁿ := pi_comp_eval_iIndepFun hX''
  exact mcdiarmid_inequality_pos X hX hX' hfι hf'' hε ht'

theorem mcdiarmid_inequality_neg'
  {X' : Ω → 𝓧} (hX'' : Measurable X')
  {f' : (ι → 𝓧) → ℝ}
  {c' : ι → ℝ}
  (hfι : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : Measurable f')
  {ε : ℝ} (hε : ε ≥ 0)
  {t : ℝ} (ht' : t * ∑ i, (c' i) ^ 2 ≤ 1) :
  (μⁿ (fun ω : ι → Ω ↦ (f' (X' ∘ ω)) -
    μⁿ[fun ω : ι → Ω ↦ f' (X' ∘ ω)] ≤ -ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp := by
  let X : ι → (ι → Ω) → 𝓧 := fun i ω ↦ X' (ω i)
  have hX : ∀ i, Measurable (X i) := fun i ↦ by measurability
  have hX' : iIndepFun X μⁿ := pi_comp_eval_iIndepFun hX''
  exact mcdiarmid_inequality_neg X hX hX' f' c' hfι hf'' _ hε _ ht'

/--
Upper-tail McDiarmid inequality for an i.i.d. sample when every coordinate
has the same bounded-difference constant `c`.

The hypothesis `t * |ι| * c^2 ≤ 1` is the constant-sensitivity form of
`t * ∑ i, (c i)^2 ≤ 1`.
-/
theorem mcdiarmid_inequality_pos_iid_of_const
  {X' : Ω → 𝓧} (hX : Measurable X')
  {f' : (ι → 𝓧) → ℝ} {c : ℝ}
  (hf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧),
    |f' x - f' (Function.update x i x')| ≤ c)
  (hf_meas : Measurable f')
  {ε : ℝ} (hε : 0 ≤ ε)
  {t : ℝ} (ht : t * (Fintype.card ι : ℝ) * c ^ 2 ≤ 1) :
  (μⁿ (fun ω : ι → Ω ↦
    f' (X' ∘ ω) - μⁿ[fun ω : ι → Ω ↦ f' (X' ∘ ω)] ≥ ε)).toReal ≤
      (-2 * ε ^ 2 * t).exp := by
  apply mcdiarmid_inequality_pos' hX hf hf_meas hε
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_assoc] using ht

/--
Lower-tail McDiarmid inequality for an i.i.d. sample when every coordinate
has the same bounded-difference constant `c`.
-/
theorem mcdiarmid_inequality_neg_iid_of_const
  {X' : Ω → 𝓧} (hX : Measurable X')
  {f' : (ι → 𝓧) → ℝ} {c : ℝ}
  (hf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧),
    |f' x - f' (Function.update x i x')| ≤ c)
  (hf_meas : Measurable f')
  {ε : ℝ} (hε : 0 ≤ ε)
  {t : ℝ} (ht : t * (Fintype.card ι : ℝ) * c ^ 2 ≤ 1) :
  (μⁿ (fun ω : ι → Ω ↦
    f' (X' ∘ ω) - μⁿ[fun ω : ι → Ω ↦ f' (X' ∘ ω)] ≤ -ε)).toReal ≤
      (-2 * ε ^ 2 * t).exp := by
  apply mcdiarmid_inequality_neg' hX hf hf_meas hε
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_assoc] using ht
