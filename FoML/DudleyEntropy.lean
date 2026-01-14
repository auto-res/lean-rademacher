import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import FoML.Defs
import FoML.PseudoMetric
import FoML.Massart
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Base

universe v u
open scoped BigOperators
open Classical ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

theorem component_le_sum_of_nonneg (m : ℕ) (j : Fin m) (f : Fin m → ℝ) (h0 : ∀ j, 0 ≤ f j) :
  f j ≤ ∑ i : Fin m, f i := by
  classical
  have hj : j ∈ (Finset.univ : Finset (Fin m)) := by simp
  have hsum :
      (Finset.univ.erase j).sum (fun i : Fin m => f i) + f j =
        ∑ i : Fin m, f i := by
    simp
  have h_nonneg :
      0 ≤ (Finset.univ.erase j).sum (fun i : Fin m => f i) := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact h0 i
  have h_le :
      f j ≤ (Finset.univ.erase j).sum (fun i : Fin m => f i) + f j := by
    simpa [add_comm] using add_le_add_left h_nonneg (f j)
  apply le_trans h_le
  simp


variable {c : ℝ}
  -- c/2^jサイズの近傍, 被覆集合, 被覆数を定義
private noncomputable abbrev ej (c : ℝ) : ℕ → ℝ := fun j ↦ c/(2^j : ℝ)

private lemma ej_pos (c_pos : 0 < c) : ∀ j, (ej c j > 0) := by
  intro j
  dsimp [ej]
  simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos, div_pos_iff_of_pos_right]
  exact c_pos

private noncomputable abbrev cj (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (j : ℕ)
  := coveringFinset h (ej_pos c_pos j)
  -- Factor out commonly used expressions
private noncomputable abbrev signs_card_inv (m : ℕ) : ℝ := (Fintype.card (Signs m) : ℝ)⁻¹

private lemma ej_nonneg (c_pos : 0 < c): ∀ j, (0 ≤ ej c j) := fun j ↦ le_of_lt (ej_pos c_pos j)
private lemma e_nonempty :
    (Set.univ : Set (EmpiricalFunctionSpace F S)).Nonempty := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact ⟨⟨i⟩, by simp⟩

omit [Nonempty ι] in
private lemma p' (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (fh : ι) (j : ℕ) :
  ∃ f_j : EmpiricalFunctionSpace F S, f_j ∈ cj c_pos h j ∧ empiricalDist S (F fh) f_j ≤ ej c j := by
  have : ⟨fh⟩ ∈ ⋃ y ∈ coveringFinset h (ej_pos c_pos j), Metric.ball y (ej c j)
    := coveringFinset_cover h (ej_pos c_pos j) (Set.mem_univ fh)
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp this
  obtain ⟨hy', hy''⟩ := Set.mem_iUnion.mp hy
  use ⟨y.index⟩
  constructor
  · exact hy'
  · exact le_of_lt hy''

private noncomputable def Q (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) : ι → ℕ → EmpiricalFunctionSpace F S :=
    fun fh j => Classical.choose (p' c_pos h fh j)

omit [Nonempty ι] in
private lemma Q_mem_cj (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : Q c_pos h fh j ∈ cj c_pos h j := by
  classical
  exact (Classical.choose_spec (p' c_pos h fh j)).1

omit [Nonempty ι] in
private lemma Q_empiricalDist_le (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : empiricalDist S (F fh) (Q c_pos h fh j) ≤ ej c j := by
  classical
  exact (Classical.choose_spec (p' c_pos h fh j)).2

private noncomputable def G (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) : ι → ℕ → Z → ℝ :=
    fun fh j => if j = 0 then 0 else (Q c_pos h fh j : Z → ℝ)

omit [Nonempty ι] in
private lemma G_def (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))): ∀ fh j, G c_pos h fh j = if j = 0 then 0 else (Q c_pos h fh j : Z → ℝ) := by
    intro fh j
    dsimp [G]

omit [Nonempty ι] in
private lemma G_succ (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : G c_pos h fh (j + 1) = (Q c_pos h fh (j + 1) : Z → ℝ) := by
  simp [G]

omit [Nonempty ι] in
private lemma chain (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (fh : ι) (n : ℕ):
      F fh = F fh - G c_pos h fh n + ∑ j : Fin n, (G c_pos h fh ((j : ℕ) + 1) - G c_pos h fh ((j : ℕ))) := by
  induction n with
  | zero => simp [G]
  | succ n hn =>
    nth_rewrite 1 [hn]
    rw [Fin.sum_univ_castSucc]
    simp
    ring_nf

omit [Nonempty ι] in
private lemma w4 (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i : Fin m) (hm_pos : 0 < m) :
    ∀ (f : ι), |F f (S i)| ≤ √↑m * c := by
  intro f
  dsimp [empiricalNorm] at cs
  have fcs := cs f
  -- from a finite-sample ℓ₂ bound to a pointwise bound via the coordinate projection inequality
  have hm_pos : 0 < (m : ℝ) := by norm_cast
  have hm_sqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hm_pos
  have hproj := empiricalDist_proj (S := S) (f := F f) (i := i)
  have hcancel : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt hm_sqrt_pos
  have h1 : |F f (S i)| ≤ √↑m * empiricalNorm S (F f) := by
    have hproj' := mul_le_mul_of_nonneg_left hproj (le_of_lt hm_sqrt_pos)
    -- simplify the left side using positivity of √m
    have hleft : √↑m * (|F f (S i)| / √↑m) = |F f (S i)| := by
      field_simp [hcancel]
    simpa [hleft] using hproj'
  calc
    |F f (S i)| ≤ √↑m * empiricalNorm S (F f) := h1
    _ ≤ √↑m * c := by
      apply mul_le_mul_of_nonneg_left fcs
      exact le_of_lt hm_sqrt_pos

private lemma w1 (c_pos : 0 < c) (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i_1 : ℕ) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ (i_2 : Fin m) (a : ι), |G c_pos h a i_1 (S i_2)| ≤ √↑m * c := by
  dsimp [G]
  by_cases h0 : i_1 = 0
  · rw [h0]
    simp
    intro i_2
    have : 0 ≤ √↑m := by simp
    exact (mul_nonneg_iff_of_pos_right c_pos).mpr this
  · simp [h0]
    intro i_2
    apply w4
    intro f
    apply cs
    exact m_pos

private lemma w0 (c_pos : 0 < c) (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i_1 : ℕ) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ (i_2 : Fin m) (a : ι), |G c_pos h a (i_1 + 1) (S i_2) - G c_pos h a (i_1) (S i_2)| ≤ 2 * (√↑m * c) := by
  intro i_2 a
  calc
  _ ≤ |G c_pos h a (i_1 + 1) (S i_2)| + |G c_pos h a i_1 (S i_2)| := by
    exact abs_sub (G c_pos h a (i_1 + 1) (S i_2)) (G c_pos h a i_1 (S i_2))
  _ ≤ √↑m * c + √↑m * c := by
    apply add_le_add
    apply w1
    exact m_pos
    exact cs
    apply w1
    exact m_pos
    exact cs
  _ = _ := by ring

theorem a0.bddAbove_main_term {c_pos : 0 < c} (cs : ∀ (f : ι), empiricalNorm S (F f) ≤ c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (m_pos : ¬m = 0)
  (i : Signs m):
  BddAbove (Set.range fun fh ↦ ∑ i_1, ↑↑(i i_1) * (F fh (S i_1) - G c_pos h fh n (S i_1))) := by
  rw [bddAbove_def]
  classical
  refine ⟨m * (2 * (Real.sqrt (m : ℝ) * c)), ?_⟩
  intro y hy
  rcases hy with ⟨fh, rfl⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero m_pos
  calc
    (∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1)))
        ≤ ∑ i_1, |(i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1))| := by
          refine Finset.sum_le_sum ?_
          intro _ _
          exact le_abs_self _
    _ = ∑ i_1, |F fh (S i_1) - G c_pos h fh n (S i_1)| := by
          apply Finset.sum_congr rfl
          intro _ _
          simp [abs_mul]
    _ ≤ ∑ i_1, (|F fh (S i_1)| + |G c_pos h fh n (S i_1)|) := by
          refine Finset.sum_le_sum ?_
          intro i_1 _
          have htri : |F fh (S i_1) - G c_pos h fh n (S i_1)|
              ≤ |F fh (S i_1)| + |G c_pos h fh n (S i_1)| := by
            exact abs_sub (F fh (S i_1)) (G c_pos h fh n (S i_1))
          exact htri
    _ ≤ ∑ i_1, (Real.sqrt (m : ℝ) * c + Real.sqrt (m : ℝ) * c) := by
          refine Finset.sum_le_sum ?_
          intro i_1 _
          have hF : |F fh (S i_1)| ≤ Real.sqrt (m : ℝ) * c := w4 cs i_1 hmpos fh
          have hG : |G c_pos h fh n (S i_1)| ≤ Real.sqrt (m : ℝ) * c := w1 c_pos hmpos cs n h i_1 fh
          have : |F fh (S i_1)| + |G c_pos h fh n (S i_1)| ≤ Real.sqrt (m : ℝ) * c + Real.sqrt (m : ℝ) * c := by
            nlinarith
          exact this
    _ = m * (2 * (Real.sqrt (m : ℝ) * c)) := by
      simp
      grind

theorem a0.bddAbove_increment_term {c_pos : 0 < c} (cs : ∀ (f : ι), empiricalNorm S (F f) ≤ c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (m_pos : ¬m = 0)
  (i : Signs m) :
  BddAbove
    (Set.range fun fh ↦
      ∑ x_1 : Fin n, ∑ i_1, ↑↑(i i_1) * (G c_pos h fh (↑x_1 + 1) (S i_1) - G c_pos h fh (↑x_1) (S i_1))) := by
  rw [bddAbove_def]
  classical
  refine ⟨(n : ℝ) * m * (2 * (Real.sqrt (m : ℝ) * c)), ?_⟩
  intro y hy
  rcases hy with ⟨fh, rfl⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero m_pos
  calc
    (∑ x_1 : Fin n, ∑ i_1, (i i_1 : ℝ) * (G c_pos h fh (↑x_1 + 1) (S i_1) - G c_pos h fh (↑x_1) (S i_1)))
        ≤ ∑ x_1 : Fin n, ∑ i_1, |(i i_1 : ℝ) * (G c_pos h fh (↑x_1 + 1) (S i_1) - G c_pos h fh (↑x_1) (S i_1))| := by
          refine Finset.sum_le_sum ?_
          intro _ _
          refine Finset.sum_le_sum ?_
          intro _ _
          exact le_abs_self _
        _ = ∑ x_1 : Fin n, ∑ i_1, |G c_pos h fh (↑x_1 + 1) (S i_1) - G c_pos h fh (↑x_1) (S i_1)| := by
          apply Finset.sum_congr rfl
          intro _ _
          apply Finset.sum_congr rfl
          intro i_1 _
          obtain ⟨v, hv⟩ := i i_1
          simp at hv
          cases hv with
          | inl hv => simp [hv]; rw [<- abs_neg]; apply congrArg; linarith
          | inr hv => simp [hv]
        _ ≤ ∑ x_1 : Fin n, ∑ i_1, 2 * (Real.sqrt (m : ℝ) * c) := by
              refine Finset.sum_le_sum ?_
              intro x_1 _
              refine Finset.sum_le_sum ?_
              intro i_1 _
              have hdiff : |G c_pos h fh (↑x_1 + 1) (S i_1) - G c_pos h fh (↑x_1) (S i_1)| ≤ 2 * (Real.sqrt (m : ℝ) * c) :=
                w0 c_pos hmpos cs (↑x_1) h i_1 fh
              nlinarith
        _ = (n : ℝ) * m * (2 * (Real.sqrt (m : ℝ) * c)) := by
              simp [Finset.sum_const, Finset.card_univ, mul_assoc, mul_left_comm, mul_comm]

  -- パートAとパートBの左辺で命題の左辺を抑える
private lemma a0 {c_pos : 0 < c} (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) :
  empiricalRademacherComplexity_without_abs m F S ≤
    ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((F fh (S i)) - G c_pos h fh n (S i)))) +
    ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * (G c_pos h fh (j+1) (S i) - G c_pos h fh j (S i)))) := by
  by_cases m_pos : m = 0
  · simp [m_pos]
    subst m_pos
    dsimp [empiricalRademacherComplexity_without_abs]
    simp
  · calc
    _ = signs_card_inv m * ((m : ℝ)⁻¹ * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i)))) := by
      dsimp [empiricalRademacherComplexity_without_abs, signs_card_inv]
      apply congrArg
      rw [Finset.mul_sum]
      apply congrArg
      ext σ
      let H : ι → ℝ := fun i => ∑ k : Fin m, (σ k : ℝ) * F i (S k)
      change ⨆ i, (↑m)⁻¹ * H i = (↑m)⁻¹ * ⨆ i, H i
      refine Eq.symm (Real.mul_iSup_of_nonneg (by simp) H)
    _ = (m : ℝ)⁻¹ * (signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i)))) := by
      ring
    _ = (m : ℝ)⁻¹ * (signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (((F fh) (S i) - G c_pos h fh n (S i)) +
        (∑ j : Fin n, (G c_pos h fh ((j : ℕ) + 1) (S i) - G c_pos h fh ((j : ℕ)) (S i)))))) := by
      repeat apply congrArg
      ext σ
      repeat apply congrArg
      ext fh
      apply congrArg
      ext i
      apply congrArg
      symm
      have h := congrArg (fun (h : Z → ℝ) => h (S i)) (chain c_pos h fh n)
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at h
      symm
      exact h
    _ ≤ (m : ℝ)⁻¹ * ((signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - G c_pos h fh n (S i)))) +
      signs_card_inv m * ∑ j : Fin n, (∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (G c_pos h fh (j+1) (S i) - G c_pos h fh j (S i))))) := by
      rw [<- left_distrib]
      rw [Finset.sum_comm]
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · have w : (∑ σ : Signs m, ⨆ fh, ∑ i, (σ i : ℝ) * (F fh (S i) - G c_pos h fh n (S i))) + ∑ y : Signs m, ∑ x : Fin n, ⨆ fh, ∑ i,(y i : ℝ) * (G c_pos h fh (↑x + 1) (S i) - G c_pos h fh (↑x) (S i))
              = ∑ σ : Signs m, ((⨆ fh, ∑ i, (σ i : ℝ) * (F fh (S i) - G c_pos h fh n (S i))) + (∑ x : Fin n, ⨆ fh, ∑ i, (σ i : ℝ) * (G c_pos h fh (↑x + 1) (S i) - G c_pos h fh (↑x) (S i)))) := by
            let w0 (σ : Signs m) := ⨆ fh, ∑ i, (σ i : ℝ) * (F fh (S i) - G c_pos h fh n (S i))
            let w1 (y : Signs m) := ∑ x : Fin n, ⨆ fh, ∑ i,(y i : ℝ) * (G c_pos h fh (↑x + 1) (S i) - G c_pos h fh (↑x) (S i))
            have w' : ∑ σ : Signs m, w0 σ + ∑ y : Signs m, w1 y = ∑ σ : Signs m, (w0 σ + w1 σ) := Eq.symm Finset.sum_add_distrib
            dsimp [w0, w1] at w'
            exact w'
          rw [w]
          apply Finset.sum_le_sum
          intro i hi
          have q : ⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1) + ∑ j : Fin n, (G c_pos h fh ((j : ℕ) + 1) (S i_1) - G c_pos h fh ((j : ℕ)) (S i_1))) ≤
            (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1))) +
              ⨆ fh, ∑ x : Fin n, ∑ i_1, (i i_1 : ℝ) * (G c_pos h fh (↑x + 1) (S i_1) - G c_pos h fh (↑x) (S i_1)) := by
            apply ciSup_le
            intro x
            -- split the inner sum into a constant part and the telescoping part
            have hx_split :
                (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - G c_pos h x n (S i_1) +
                  ∑ j : Fin n, (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1))))
                = (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - G c_pos h x n (S i_1))) +
                  (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1)))) := by
              -- distribute the product over the inner addition and split the outer sum
              simp [mul_add, Finset.sum_add_distrib]
            -- bound each part by the respective suprema
            have hx1 : (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - G c_pos h x n (S i_1))) ≤
                ⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1)) := by
                  apply le_ciSup_of_le
                  · exact a0.bddAbove_main_term cs h n m_pos i
                  · exact Preorder.le_refl (∑ i_1, ↑↑(i i_1) * (F x (S i_1) - G c_pos h x n (S i_1)))
            calc
              (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - G c_pos h x n (S i_1) + ∑ j : Fin n, (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1))))
                  = _ := hx_split
              _ ≤ (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1))) +
                  (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1)))) := by
                nlinarith
              _ ≤ (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - G c_pos h fh n (S i_1))) +
                  (⨆ fh, ∑ x : Fin n, ∑ i_1, (i i_1 : ℝ) * (G c_pos h fh (↑x + 1) (S i_1) - G c_pos h fh (↑x) (S i_1))) := by
                -- rewrite the second sum as a double sum and take fh = x in the supremum
                have hx2_swap :
                    (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1))))
                    = ∑ j : Fin n, ∑ i_1, (i i_1 : ℝ) * (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1)) := by
                  -- expand the outer product into an inner sum and then swap the summations
                  have h_expand : (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1))))
                      = ∑ i_1, ∑ j : Fin n, (i i_1 : ℝ) * (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1)) := by
                    apply Finset.sum_congr rfl
                    intro i1 hi1
                    -- move the scalar inside the inner sum
                    rw [Finset.mul_sum]
                  rw [h_expand]
                  rw [Finset.sum_comm]
                have hx2 : (∑ j : Fin n, ∑ i_1, (i i_1 : ℝ) * (G c_pos h x ((j : ℕ) + 1) (S i_1) - G c_pos h x ((j : ℕ)) (S i_1))) ≤
                    ⨆ fh, ∑ x_1 : Fin n, ∑ i_1, (i i_1 : ℝ) * (G c_pos h fh (↑x_1 + 1) (S i_1) - G c_pos h fh (↑x_1) (S i_1)) := by
                  apply le_ciSup_of_le
                  · exact a0.bddAbove_increment_term cs h n m_pos i
                  · apply Preorder.le_refl
                -- combine both bounds
                rw [hx2_swap]
                apply add_le_add_right
                exact hx2
          apply le_trans q
          rw [add_le_add_iff_left]
          apply ciSup_le
          intro x'
          apply Finset.sum_le_sum
          intro i_1 hi_1
          apply le_ciSup_of_le
          · rw [bddAbove_def]
            use m * (2 * (√↑m * c))
            simp
            intro a
            calc
            _ ≤ ∑ i_2, |(i i_2 : ℝ) * (G c_pos h a (↑i_1 + 1) (S i_2) - G c_pos h a (↑i_1) (S i_2))| := Finset.sum_le_sum (fun i_2 hi_2 ↦  le_abs_self ((i i_2 : ℝ) * (G c_pos h a (↑i_1 + 1) (S i_2) - G c_pos h a (↑i_1) (S i_2))))
            _ ≤ ∑ i_2 : Fin m, 2 * (√↑m * c) := by
              apply Finset.sum_le_sum
              intro i_2 hi_2

              rw [abs_mul]
              simp
              apply w0
              · apply Nat.pos_of_ne_zero m_pos
              · exact cs
            _ = _ := by simp
          · change ∑ i_1_1, (i i_1_1 : ℝ) * (G c_pos h x' (↑i_1 + 1) (S i_1_1) - G c_pos h x' (↑i_1) (S i_1_1)) ≤ ∑ i_2, (i i_2 : ℝ) * (G c_pos h x' (↑i_1 + 1) (S i_2) - G c_pos h x' (↑i_1) (S i_2))
            simp
        · dsimp [signs_card_inv]
          simp
      · simp
    _ = (m : ℝ)⁻¹ * ((signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - G c_pos h fh n (S i)))) +
      ∑ j : Fin n, ( signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (G c_pos h fh (j+1) (S i) - G c_pos h fh j (S i))))) := by
      simp
      left
      simp [Finset.mul_sum]
    _ = ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - G c_pos h fh n (S i)))) +
      (m : ℝ)⁻¹ * ∑ j : Fin n, ( signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (G c_pos h fh (j+1) (S i) - G c_pos h fh j (S i)))) := by
      rw [mul_add]
      rw [mul_assoc]
    _ = _ := by
      simp only [add_right_inj]
      simp [Finset.mul_sum, mul_assoc]

omit [Nonempty ι] in
private lemma DistFG (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (fh : ι) (n : ℕ)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalDist S (F fh) (G c_pos h fh n) ≤ c / 2 ^ n := by
  by_cases h' : n = 0
  · simpa [G_def c_pos h, h'] using cs fh
  · simpa [G_def c_pos h, h'] using (Classical.choose_spec (p' c_pos h fh n)).2

private lemma sigma_sum_le_dist (f g : Z → ℝ) (σ : Signs m) :
  ∑ i : Fin m, (σ i : ℝ) * (f (S i) - g (S i)) ≤ m * empiricalDist S f g := by
  calc
  _ = @inner ℝ (EuclideanSpace ℝ (Fin m)) _ (WithLp.toLp 2 fun i ↦ (σ i : ℝ)) (WithLp.toLp 2 fun i ↦ f (S i) - g (S i)) := by
    simp [inner]
    congr
    ext _
    rw [mul_comm]
  -- Use Cauchy-Schwarz inequality
  _ ≤ (@norm (EuclideanSpace ℝ (Fin m)) _ (WithLp.toLp 2 fun i ↦ (σ i : ℝ))) * (@norm (EuclideanSpace ℝ (Fin m)) _ (WithLp.toLp 2 fun i ↦ f (S i) - g (S i))) :=
    @real_inner_le_norm (EuclideanSpace ℝ (Fin m)) _ _ (WithLp.toLp 2 fun i ↦ (σ i : ℝ)) (WithLp.toLp 2 fun i ↦ f (S i) - g (S i))
  _ = m * empiricalDist S f g := by
    simp [norm, empiricalNorm]
    have : (∑ i, (σ i : ℝ) ^ 2) = m := by
      have : (∑ i, (σ i : ℝ) ^ 2) = (∑ i : Fin m, 1) := by
        congr
        ext i
        obtain ⟨σi, hσi⟩ := σ i
        simp at hσi
        simp
        cases hσi with
        | inl h1 => right; rw [h1]; norm_num
        | inr h2 => left; rw [h2]
      rw [this]
      apply (Finset.sum_const 1).trans
      simp
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ←mul_assoc]
    congr
    · rw [←Real.rpow_neg (by simp), ←Real.rpow_one_add' (by simp) (by norm_num)]
      congr
      norm_num
    · norm_num

-- パートA
omit [Nonempty ι] in
private lemma aA (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (n : ℕ) : ∀ (σ : Signs m) (fh : ι),
  ((∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - G c_pos h fh n (S i))) ≤ (m : ℝ) * (ej c n)) := by
  intro σ fh
  unfold ej
  apply le_trans (sigma_sum_le_dist (F fh) (G c_pos h fh n) σ)
  apply mul_le_mul_of_nonneg_left _ (by simp)
  exact DistFG c_pos h fh n cs
  -- パートB (途中でmassartの補題が必要)
  -- 園田さんのノートを参考にする部分
    /- $G := \{ (p_j(f)-p_{j-1}(f) \mid f \in F\},
    G' := \{ (p_j(f),p_{j-1}(f)) \mid f \in F\}$ とおく．$|G| \le |G'| \le |C_j||C_{j-1}|$ である．
    -/
private noncomputable def K (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := {G c_pos h fh (j + 1) - G c_pos h fh j | fh : ι}

private noncomputable def K' (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := {(G c_pos h fh (j + 1), G c_pos h fh j) | fh : ι}

private lemma g0 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  {G c_pos h' fh j | fh : ι}.Finite := by
  dsimp [G]
  by_cases h : (j : ℕ) = 0
  · rw [h]
    simp
  · simp [h]
    dsimp [Q]
    have finite_F_image : {F f.index | f ∈ cj c_pos h' (j : ℕ)}.Finite := by
      have : (SetLike.coe (cj c_pos h' (j : ℕ))).Finite := Finset.finite_toSet _
      exact this.image (fun f => F f.index)
    apply finite_F_image.subset
    intro p hp
    simp at hp
    obtain ⟨r, hpr⟩ := hp
    simp
    use choose (p' c_pos h' r (j : ℕ))
    constructor
    · rcases Classical.choose_spec (p' c_pos h' r (j : ℕ)) with ⟨hmem, hle⟩
      exact hmem
    · exact hpr

private noncomputable def A (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :=
  {G c_pos h' fh (j + 1) | fh : ι}

private noncomputable def B (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :=
  {G c_pos h' fh j | fh : ι}

private noncomputable def AB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :=
  (A c_pos h' n j) ×ˢ (B c_pos h' n j)

private lemma hA (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (A c_pos h' n j).Finite := g0 c_pos h' (n+1) ⟨j + 1, by simp⟩

private lemma hB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (B c_pos h' n j).Finite := g0 c_pos h' n j

private lemma hAB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  ((A c_pos h' n j) ×ˢ (B c_pos h' n j)).Finite := (hA c_pos h' n j).prod (hB c_pos h' n j)

omit [Nonempty ι] in
private lemma hAB_subset_K' (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
    (K' c_pos h' n j) ⊆ (AB c_pos h' n j) := by
  intro f hf
  obtain ⟨f0, hg⟩ := hf
  rw [<- hg]
  refine Set.mk_mem_prod (by use f0) (by use f0)

private lemma k1 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (K' c_pos h' n j).Finite := by
  unfold K'
  refine (hAB c_pos h' n j).subset ?_
  apply hAB_subset_K'

private lemma k0 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (K c_pos h' n j).Finite := by
  unfold K
  let f : (Z → ℝ) × (Z → ℝ) → (Z → ℝ) := fun p => p.1 - p.2
  have : {G c_pos h' fh (j + 1) - G c_pos h' fh j | fh : ι} = f '' K' c_pos h' n j := by
    ext x
    simp [K']
    constructor
    · rintro ⟨fh, rfl⟩
      use fh
    · rintro ⟨w', hw⟩
      use w'
  rw [this]
  exact (k1 c_pos h' n j).image f

private noncomputable def KA (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (hA c_pos h' n j)

private noncomputable def KB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (hB c_pos h' n j)

private noncomputable def KF (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (k0 c_pos h' n j)

private noncomputable def KF' (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (k1 c_pos h' n j)

private noncomputable def KAB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (hAB c_pos h' n j)

private lemma k00 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (KF c_pos h' n j).Nonempty := by
  dsimp [KF]
  simp only [Set.Finite.toFinset_nonempty]
  exact ⟨_, ⟨Classical.arbitrary ι, rfl⟩⟩

private lemma k01 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (KF' c_pos h' n j).Nonempty := by
  dsimp [KF']
  simp only [Set.Finite.toFinset_nonempty]
  exact ⟨_, ⟨Classical.arbitrary ι, rfl⟩⟩

private lemma k2 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (KF c_pos h' n j).card ≤ (KF' c_pos h' n j).card := by
  unfold KF KF'
  let f : (Z → ℝ) × (Z → ℝ) → (Z → ℝ) := fun p => p.1 - p.2
  apply Finset.card_le_card_of_surjOn f
  dsimp [Set.SurjOn]
  intro e es
  simp at es
  simp
  rcases es with ⟨fh, rfl⟩
  refine ⟨_, _, ?_, rfl⟩
  exact ⟨fh, rfl⟩

private lemma k20 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
    (KF' c_pos h' n j).card ≤ (KAB c_pos h' n j).card := by
  unfold KF' KAB
  refine Finset.card_le_card ?_
  refine Set.Finite.toFinset_subset_toFinset.mpr ?_
  apply hAB_subset_K'

private lemma k21 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (KAB c_pos h' n j).card = (KA c_pos h' n j).card * (KB c_pos h' n j).card := by
  rw [<- Finset.card_product]
  refine Finset.card_eq_of_equiv ?_
  simp
  dsimp [KA, KAB, KB]
  simp
  exact Equiv.refl _

private lemma k22 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (KA c_pos h' n j).card ≤ (cj c_pos h' ((j : ℕ) + 1)).card := by
  -- expand `KA`: it is the finset of functions of the form `G c_pos h' fh (j+1)`
  -- coming from the cover at scale `j+1`.
  dsimp [KA]
  classical
  -- image of the cover under coercion to functions
  -- coerce elements of the cover to functions before taking the image
  let T : Finset (Z → ℝ) := (cj c_pos h' ((j : ℕ) + 1)).image (fun q : EmpiricalFunctionSpace F S => (q : Z → ℝ))
  -- every element of `KA` comes from this image via `Q_mem_cj`
  have hsubset : Set.Finite.toFinset (hA c_pos h' n j) ⊆ T := by
    intro x hx
    have hxA : x ∈ A c_pos h' n j := by
      simpa [KA] using hx
    rcases hxA with ⟨fh, rfl⟩
    -- rewrite G at successor
    have hG : G c_pos h' fh ((j : ℕ) + 1) = (Q c_pos h' fh ((j : ℕ) + 1) : Z → ℝ) := by
      simp [G_succ]
    -- show the corresponding `Q` lies in the cover
    have hmem : Q c_pos h' fh ((j : ℕ) + 1) ∈ cj c_pos h' ((j : ℕ) + 1) := by
      apply Q_mem_cj
    -- build membership in the image finset
    -- membership in the image finset
    have hQmem : (Q c_pos h' fh ((j : ℕ) + 1) : Z → ℝ) ∈ T := by
      -- unfold `T` and register the element explicitly
      dsimp [T]
      refine Finset.mem_image.mpr ?_
      refine ⟨Q c_pos h' fh ((j : ℕ) + 1), hmem, rfl⟩
    simpa [hG] using hQmem
  have hcard_le_T : (Set.Finite.toFinset (hA c_pos h' n j)).card ≤ T.card := by
    exact Finset.card_le_card hsubset
  have hT_le : T.card ≤ (cj c_pos h' ((j : ℕ) + 1)).card := Finset.card_image_le
  exact hcard_le_T.trans hT_le

private lemma k23 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)  (n_pos : 0 < n) :
  (KB c_pos h' n j).card ≤ (cj c_pos h' (j : ℕ)).card := by
  -- expand `KB`: functions of the form `G … fh j` live in the cover at scale `j`
  dsimp [KB]
  classical
  -- image of the cover under coercion to functions
  let T : Finset (Z → ℝ) := (cj c_pos h' ((j : ℕ))).image (fun q : EmpiricalFunctionSpace F S => (q : Z → ℝ))
  -- every element of `KB` comes from this image via `Q_mem_cj`, with a small case split on `(j : ℕ) = 0`
  by_cases hzero : ((j : ℕ)) = 0
  · -- when j = 0, G = 0 so KB has card 1 ≤ card of the cover (nonempty via Q_mem_cj)
    rw [hzero]
    -- KB card is 1
    have hKB : (KB c_pos h' n ⟨0, by
      -- j.isLt : ((j : ℕ)) < n; with hzero we get 0 < n
      have := j.isLt
      simpa [hzero] using this⟩).card = 1 := by
      -- B is {0}, so its toFinset has one element
      simp [KB, B, G]
    -- cover at scale 0 is nonempty: use any fh
    classical
    obtain ⟨fh0⟩ := (inferInstance : Nonempty ι)
    have hcov : (cj c_pos h' 0).Nonempty := by
      exact ⟨Q c_pos h' fh0 0, Q_mem_cj c_pos h' fh0 0⟩
    have hcover_card : 1 ≤ (cj c_pos h' 0).card := by
      simpa [Nat.succ_le_iff, Finset.card_pos] using hcov
    -- rewrite j to ⟨0, _⟩ to align indices and conclude
    have hj : j = ⟨0, by
      have := j.isLt
      simpa [hzero] using this⟩ := by
      cases j with
      | mk jv jlt =>
        cases hzero
        rfl
    rw [hj]
    -- relate the left card to 1 using hKB, then compare with the cover card
    have hBcard : (Set.Finite.toFinset (hB c_pos h' n ⟨0, n_pos⟩)).card = 1 := by
      -- KB is exactly this toFinset
      simpa [KB] using hKB
    have : (Set.Finite.toFinset (hB c_pos h' n ⟨0, n_pos⟩)).card ≤ (cj c_pos h' 0).card := by
      -- rewrite the left card to 1 and use the cover-card lower bound
      simpa [hBcard] using hcover_card
    exact this
  · -- j ≠ 0: use G_succ and Q_mem_cj to build the subset/image argument
    have hsubset : Set.Finite.toFinset (hB c_pos h' n j) ⊆ T := by
      intro x hx
      have hxB : x ∈ B c_pos h' n j := by simpa [KB] using hx
      rcases hxB with ⟨fh, rfl⟩
      have hG : G c_pos h' fh ((j : ℕ)) = (Q c_pos h' fh ((j : ℕ)) : Z → ℝ) := by
        have : ∃ k, (j : ℕ) = k + 1 := Nat.exists_eq_succ_of_ne_zero hzero
        rcases this with ⟨k, hk⟩
        rw [hk]
        simp [G_succ]
      have hmem : Q c_pos h' fh ((j : ℕ)) ∈ cj c_pos h' ((j : ℕ)) := Q_mem_cj c_pos h' fh ((j : ℕ))
      have hQmem : (Q c_pos h' fh ((j : ℕ)) : Z → ℝ) ∈ T := by
        dsimp [T]
        refine Finset.mem_image.mpr ?_
        exact ⟨Q c_pos h' fh ((j : ℕ)), hmem, rfl⟩
      simpa [hG] using hQmem
    have hcard_le_T : (Set.Finite.toFinset (hB c_pos h' n j)).card ≤ T.card := by
      exact Finset.card_le_card hsubset
    have hT_le : T.card ≤ (cj c_pos h' ((j : ℕ))).card := Finset.card_image_le
    exact hcard_le_T.trans hT_le

private lemma k3 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) (n_pos : 0 < n):
  (KF' c_pos h' n j).card ≤ (cj c_pos h' (j+1)).card * (cj c_pos h' j).card := by
  calc
  _ ≤ (KAB c_pos h' n j).card := by
    apply k20
  _ = (KA c_pos h' n j).card * (KB c_pos h' n j).card := by
    apply k21
  _ ≤ _ := by
    apply mul_le_mul
    apply k22
    apply k23
    exact n_pos
    simp
    simp

omit [Nonempty ι] in
private lemma G_bounded (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (j : ℕ)
  (σ : Signs m) (fh : ι) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ∑ i : Fin m, (σ i : ℝ) * (G c_pos h' fh (j + 1) - G c_pos h' fh j) (S i) ≤ m * (c / 2 ^ (j+1) + c / 2 ^ j) := by
  calc
  _ ≤ m * empiricalDist S (G c_pos h' fh (j + 1)) (G c_pos h' fh j) := by
    apply sigma_sum_le_dist (G c_pos h' fh (j + 1)) (G c_pos h' fh j) σ
  _ ≤ _ := by
    apply mul_le_mul_of_nonneg_left _ (by simp)
    calc
    _ ≤ empiricalDist S (G c_pos h' fh (j + 1)) (F fh) + empiricalDist S (F fh) (G c_pos h' fh j) := by
      apply @dist_triangle _ (empiricalPMet S) (G c_pos h' fh (j + 1)) (F fh) (G c_pos h' fh j)
    _ ≤ _ := by
      rw [←empiricalDist_comm S (F fh) (G c_pos h' fh (j+1))]
      apply add_le_add
      · exact DistFG c_pos h' fh (j+1) cs
      · exact DistFG c_pos h' fh j cs

private lemma aC00 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((G c_pos h' fh (j+1) - G c_pos h' fh j) (S i))))
  ≤ ((KF c_pos h' n j).sup' (k00 c_pos h' n j) fun j ↦ √(∑ i, (|j (S i)|) ^ 2)) * (√(2 * Real.log ((Set.Finite.toFinset (k0 c_pos h' n j)).card))) / m := by
  let C := ((KF c_pos h' n j).sup' (k00 c_pos h' n j) fun j ↦ √(∑ i, (|j (S i)|) ^ 2))
  calc
  _ = ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ (fh : {x // x ∈ KF c_pos h' n j}),
    (∑ i : Fin m, (σ i : ℝ) * (fh.val (S i)))) := by
    congr
    ext σ
    apply le_antisymm
    · apply ciSup_le
      intro fh
      let hfh : {x // x ∈ KF c_pos h' n j} := by
        use G c_pos h' fh (j + 1) - G c_pos h' fh j
        dsimp [KF, K]
        simp
      convert le_ciSup _ hfh
      · congr
      · use m * (c / 2 ^ (j.1 + 1) + c / 2 ^ j.1)
        rintro x ⟨⟨g, hg'⟩, hg⟩
        rw [<-hg]
        dsimp [KF] at hg'
        simp at hg'
        obtain ⟨fh, hfh⟩ := hg'
        simp
        rw [<-hfh]
        exact G_bounded c_pos h' j.1 σ fh cs
    · have : Nonempty {x // x ∈ KF c_pos h' n j} := by
        obtain ⟨fh⟩ := (by assumption : Nonempty ι)
        use G c_pos h' fh (j + 1) - G c_pos h' fh j
        dsimp [KF, k0, K]
        simp
      apply ciSup_le
      rintro ⟨g, hg⟩
      dsimp [KF] at hg
      simp at hg
      obtain ⟨fh, hfh⟩ := hg
      convert le_ciSup _ fh
      · congr
        ext i
        simp
        rw [<- hfh]
        simp
      · use m * (c / 2 ^ (j.1 + 1) + c / 2 ^ j.1)
        rintro x ⟨fh, hfh⟩
        rw [<-hfh]
        exact G_bounded c_pos h' j.1 σ fh cs
  _ = signs_card_inv m * ∑ σ : Signs m, ⨆ (fh : {x // x ∈ KF c_pos h' n j}),
    ((m : ℝ)⁻¹ * ∑ i : Fin m, (σ i : ℝ) * (fh.val (S i))) := by
    rw [mul_comm (m : ℝ)⁻¹ _, mul_assoc]
    congr
    rw [Finset.mul_sum]
    congr
    ext σ
    apply Real.mul_iSup_of_nonneg
    apply inv_nonneg_of_nonneg
    exact Nat.cast_nonneg' m
  _ = empiricalRademacherComplexity_pmf_without_abs m (F_on (ι:=(Z → ℝ)) (Z:=Z) (fun hk : Z → ℝ => hk) (KF c_pos h' n j)) S := by
    simp only [empiricalRademacherComplexity_pmf_without_abs, signVecPMF,
      Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, Finset.mul_sum,
      PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, smul_eq_mul, signs_card_inv]
    rfl
  _ ≤ C * (√(2 * Real.log ((Set.Finite.toFinset (k0 c_pos h' n j)).card))) / m := by
    apply le_of_le_of_eq
    · apply massart_lemma_pmf
      · exact k00 c_pos h' n j
      · exact m_pos
      · change ∀ i ∈ KF c_pos h' n j, ∀ (j : Fin m), |i (S j)| ≤ C
        intro i hi j
        dsimp [C]
        simp
        use i
        constructor
        · exact hi
        · have hnonneg : ∀ x : Fin m, 0 ≤ i (S x) ^ 2 := by
            intro x
            nlinarith
          have hsq : i (S j) ^ 2 ≤ ∑ x : Fin m, i (S x) ^ 2 := by
            simpa using
              (Finset.single_le_sum
                (s := (Finset.univ : Finset (Fin m)))
                (f := fun x : Fin m => i (S x) ^ 2)
                (a := j)
                (by
                  intro x hx
                  exact hnonneg x)
                (by simp))
          have : Real.sqrt (i (S j) ^ 2) ≤ Real.sqrt (∑ x : Fin m, i (S x) ^ 2) := by
            exact Real.sqrt_le_sqrt hsq
          simpa [Real.sqrt_sq_eq_abs] using this
      · exact k00 c_pos h' n j
    · have : √(2 * Real.log ((Set.Finite.toFinset (k0 c_pos h' n j)).card)) = √(2 * Real.log ↑(KF c_pos h' n j).card) := by
        apply congrArg
        apply congrArg
        apply congrArg
        exact rfl
      rw [this]
      dsimp [C]
      rw [mul_div_right_comm]
      rw [Mathlib.Tactic.LinearCombination.mul_eq_const]
      field_simp
      rw [Finset.mul₀_sup']
      apply congrArg
      ext i
      rw [<- Finset.sum_div]
      simp only [sq_abs, Nat.cast_nonneg, pow_succ_nonneg, Real.sqrt_div', Real.sqrt_sq]
      field_simp
      norm_cast

theorem aB.mem_KF_pair (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (j : Fin n) (hk : (Z → ℝ) × (Z → ℝ))
  (hk0 : hk ∈ KF' c_pos h' n j) : ∃ fh, (G c_pos h' fh ((j : ℕ) + 1), G c_pos h' fh (j : ℕ)) = hk := by
  dsimp [KF'] at hk0
  simp at hk0
  dsimp [K'] at hk0
  exact hk0

private lemma aB0 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (n_pos : 0 < n):
  ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((G c_pos h' fh (j+1) - G c_pos h' fh j) (S i)))) ≤
  ∑ j : Fin n, (Finset.sup' (KF' c_pos h' n j) (k01 c_pos h' n j) fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) * (√(2 * Real.log (coveringNumber h' (ej c (j+1)) * coveringNumber h' (ej c j)))) / ↑m := by
  -- ∑ j : Fin n, Finset.sup' (KF' n j) (k01 n j) √(∑ i : Fin m, ( ((Finset.toSet (KF' n j)).1 - ((Finset.toSet (KF' n j)).2) (S i)) ^ 2) * (√(2 * Real.log (coveringNumber h (ej (j+1)) * coveringNumber h (ej j))))
  -- $\sum_{j=1}^n$ の各項に対して示せばよい．以下では $j \in \mathbb N$ を固定する．
  apply Finset.sum_le_sum
  intro j hj
  /- $p_j, p_{j-1}$ の全射性と$C_j,C_{j-1}$の有限性により，$\sup_{f \in F} [\cdots p_j(f) \cdots p_{j-1}(f)\cdots] = \max_{(h,k) \in \textcolor{red}{G'}}[\cdots h \cdots k \cdots]$ なので，
  $$
  \begin{align}
  \frac{1}{m} \mathbb E_\sigma \left[ \sup_{f\in F} J(p_j(f)- p_{j-1}(f)) \right] =
  &\frac{1}{m} \mathbb E_\sigma \left[ \max_{(h,k) \in \textcolor{red}{G'}} J(h-k) \right] \tag{1a}
  \end{align}
  $$ -/
  calc
  _ ≤ ((KF c_pos h' n j).sup' (k00 c_pos h' n j) fun j ↦ √(∑ i, (|j (S i)|) ^ 2)) * (√(2 * Real.log ((Set.Finite.toFinset (k0 c_pos h' n j)).card))) / m := aC00 c_pos h' n j m_pos cs
  _ ≤ ((Finset.sup' (KF' c_pos h' n j) (k01 c_pos h' n j) fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i) ) ^ 2)) * (√(2 * Real.log ((Set.Finite.toFinset (k0 c_pos h' n j)).card)))) / m := by
    apply div_le_div_of_nonneg_right _ _
    apply mul_le_mul_of_nonneg_right _ _
    apply Finset.sup'_le _ _
    intro hk hk0
    simp only [Set.Finite.mem_toFinset, KF] at hk0
    obtain ⟨fh, hfh⟩ := hk0
    rw [<- hfh]
    have : √(∑ i, |(G c_pos h' fh ((j : ℕ) + 1) - G c_pos h' fh (j : ℕ)) (S i)| ^ 2) = √(∑ i : Fin m, ((G c_pos h' fh ((j : ℕ) + 1) - G c_pos h' fh (j : ℕ)) (S i)) ^ 2) := by
      congr
      ext i
      exact sq_abs _
    rw [this]
    have : ⟨G c_pos h' fh ((j : ℕ) + 1), G c_pos h' fh (j : ℕ)⟩ ∈ KF' c_pos h' n j := by
      simp only [Set.Finite.mem_toFinset, KF', K']
      use fh
    exact Finset.le_sup' (fun hk : (Z → ℝ) × (Z → ℝ) ↦ Real.sqrt (∑ i : Fin m, ((hk.1 - hk.2) (S i) ) ^ 2)) this
    simp
    simp
  _ ≤ _ := by
    refine div_le_div_of_nonneg_right ?_ ?_
    · apply mul_le_mul_of_nonneg_left
      · apply Real.sqrt_le_sqrt
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        apply Real.log_le_log
        · simp; exact (Set.Finite.toFinset_nonempty (k0 c_pos h' n j)).mp (k00 c_pos h' n j)
        · norm_cast
          apply (k2 c_pos h' n j).trans
          convert (k3 c_pos h' n j n_pos)
          <;> rw [coveringFinset_card]
      · obtain ⟨fh⟩ := (by assumption : Nonempty ι)
        have hem : ⟨G c_pos h' fh (j + 1), G c_pos h' fh j⟩ ∈ KF' c_pos h' n j := by
          simp only [Set.Finite.mem_toFinset, KF', K']
          use fh
        apply le_trans _ (Finset.le_sup' _ hem)
        apply Real.sqrt_nonneg
    · simp

private lemma aB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((G c_pos h' fh (j+1) - G c_pos h' fh j) (S i)))) ≤
    ∑ j : Fin n, 6 * (ej c (j+1) - ej c (j+2)) * (√(4 * Real.log (coveringNumber h' (ej c (j+1))))/((Real.sqrt m))) := by
  calc
  _ ≤ ∑ j : Fin n, (Finset.sup' (KF' c_pos h' n j) (k01 c_pos h' n j) fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) * (√(2 * Real.log (coveringNumber h' (ej c (j+1)) * coveringNumber h' (ej c j)))) / ↑m := by
    by_cases n_pos : 0 < n
    · exact aB0 c_pos h' n m_pos cs n_pos
    · simp at n_pos
      rw [n_pos]
      simp
  _ = ∑ j : Fin n, (Finset.sup' (KF' c_pos h' n j) (k01 c_pos h' n j) fun hk ↦ (√(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) / ↑m) * (√(2 * Real.log (coveringNumber h' (ej c (j+1)) * coveringNumber h' (ej c j)))) := by
    apply congrArg
    ext j
    rw [<- div_mul_eq_mul_div]
    rw [Mathlib.Tactic.LinearCombination.mul_eq_const]
    rw [Finset.sup'_div₀]
    norm_cast
  _ ≤ ∑ j : Fin n, ((6 * (ej c (j+1) - ej c (j+2))/ Real.sqrt m) * (√(2 * Real.log ((coveringNumber h' (ej c (j+1))) * (coveringNumber h' (ej c j)))))) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    apply mul_le_mul_of_nonneg_right
      -- where the last inequality uses the fact that周り
    · have r0 (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ KF' c_pos h' n j) : ∃ fh, (G c_pos h' fh (j + 1), G c_pos h' fh j) = hk := by
        dsimp [KF'] at hk0
        simp at hk0
        dsimp [K'] at hk0
        exact hk0
      have fh (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ KF' c_pos h' n j) : ι :=
        Classical.choose (r0 hk hk0)
      suffices ∀ (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ KF' c_pos h' n j), (√(∑ i, ((hk.1 - hk.2) (S i)) ^ 2)) / ↑m ≤ 6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) / Real.sqrt m from by
        rw [Finset.sup'_le_iff]
        exact this
      intro hk hk0
      have hk1 : hk ∈ K' c_pos h' n j := by dsimp [KF'] at hk0; simp at hk0; exact hk0
      dsimp [K'] at hk1
      obtain ⟨x, fhx⟩ := hk1
      have r : √(∑ i, ((hk.1 - hk.2) (S i)) ^ 2) ≤ √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) + √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) := by
        let ai : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun i ↦ (hk.1 - (F x)) (S i)
        let aj : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 fun i ↦ (hk.2 - (F x)) (S i)
        have norm_calc : ‖ai - aj‖ = √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2) := by
          calc
          _ =  √(∑ j : Fin m, ‖ai j - aj j‖ ^ 2) := by exact (EuclideanSpace.norm_eq (ai - aj))
          _ = _ := by dsimp [ai, aj]; simp
        calc
        _ = ‖ai - aj‖ := by
          dsimp [ai, aj, norm]
          simp
          rw [Real.sqrt_eq_rpow];simp
        _ = ‖ai + (-aj)‖ := rfl
        _ ≤ ‖ai‖ + ‖(-aj)‖ := norm_add_le ai (-aj)
        _ = ‖ai‖ + ‖aj‖ := by simp
        _ = _ := by
          apply Mathlib.Tactic.LinearCombination.add_eq_eq
          · dsimp [ai, norm]
            simp
            rw [Real.sqrt_eq_rpow];simp
          · dsimp [aj, norm]
            simp
            rw [Real.sqrt_eq_rpow];simp
      have r' : √(∑ i, ((hk.1 - hk.2) (S i)) ^ 2) / ↑m ≤ √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) / ↑m + √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) / ↑m := by
        have : (√(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) + √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2)) / ↑m =
               √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) / ↑m + √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) / ↑m := by
          ring
        rw [← this]
        exact div_le_div_of_nonneg_right r (Nat.cast_nonneg m)
      apply le_trans r'
      have rp : 6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) / Real.sqrt m = (ej c (j + 1) / Real.sqrt m) + (ej c j / Real.sqrt m) := by
        suffices 6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) = ej c (j + 1) + ej c j from by
          rw [this]
          exact add_div (ej c ((j : ℕ) + 1)) (ej c (j : ℕ)) (Real.sqrt m)
        have t (j : ℕ) : 2 * ej c ((j : ℕ) + 1) = ej c (j : ℕ) := by
          have two_ne_zero' : (2 : ℝ) ≠ 0 := two_ne_zero
          calc
            2 * ej c ((j : ℕ) + 1)
                = 2 * (c / (2 ^ ((j : ℕ) + 1) : ℝ)) := by rfl
            _ = 2 * (c / ((2 ^ (j : ℕ) : ℝ) * 2)) := by
                  simp [pow_succ]
            _ = (2 * c) / ((2 ^ (j : ℕ) : ℝ) * 2) := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using
                    (mul_div_assoc (2 : ℝ) c ((2 ^ (j : ℕ) : ℝ) * 2)).symm
            _ = (c * 2) / ((2 ^ (j : ℕ) : ℝ) * 2) := by
                  simp [mul_comm]
            _ = c / (2 ^ (j : ℕ) : ℝ) := mul_div_mul_right c (2 ^ j) two_ne_zero'
            _ = ej c (j : ℕ) := by
                  simp [ej]
        calc
          _ = 6 * ej c ((j : ℕ) + 1) - 6 * ej c ((j : ℕ) + 2) := by
            simp [mul_sub]
        _ = 6 * ej c ((j : ℕ) + 1) - 3 * ej c ((j : ℕ) + 1) := by
          have ht : 6 * ej c ((j : ℕ) + 2) = 3 * ej c ((j : ℕ) + 1) := by
            have h := t ((j : ℕ) + 1)
            have h' : 2 * ej c ((j : ℕ) + 2) = ej c ((j : ℕ) + 1) := by
              simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using h
            have h'' := congrArg (fun x : ℝ => (3 : ℝ) * x) h'
            calc
              6 * ej c ((j : ℕ) + 2) = 3 * (2 * ej c ((j : ℕ) + 2)) := by ring
              _ = 3 * ej c ((j : ℕ) + 1) := by
                simpa using h''
          simp [ht]
        -- 下で行う区分求積法をしないなら3 * ej ((j : ℕ) + 1)で抑えるというのがゴールになりそう
        _ = 3 * ej c ((j : ℕ) + 1) := by
          linarith
        _ = ej c ((j : ℕ) + 1) + 2 * ej c ((j : ℕ) + 1) := by
          linarith
        _ = _ := by
          refine add_left_cancel_iff.mpr ?_
          rw [t]
      have r0 : √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2) / ↑m ≤ ej c (j + 1) / Real.sqrt m := by
        suffices √(∑ i, ((hk.1 - (F x)) (S i)) ^ 2 / ↑m) ≤ ej c (j + 1) from by
          rw [<- Finset.sum_div] at this
          simp at this
          have u : √(∑ i, (hk.1 - F x) (S i) ^ 2) / ↑m = (√(∑ i, (hk.1 - F x) (S i) ^ 2) / √↑m) / √↑m := by
            field_simp
            congr
            apply Real.sq_sqrt
            exact Nat.cast_nonneg m
          rw [u]
          apply div_le_div_of_nonneg_right this
          simp
        have gh : hk.1 = G c_pos h' x ((j : ℕ) + 1) := by rw [<- fhx]
        rw [gh]
        have : √(∑ i, (G c_pos h' x ((j : ℕ) + 1) - F x) (S i) ^ 2 / ↑m) = empiricalDist S (F x) (G c_pos h' x ((j : ℕ) + 1)) := by
          rw [empiricalDist_comm]
          dsimp [empiricalDist, empiricalNorm]
          apply congrArg
          simp [div_eq_mul_inv, mul_comm]
          exact
            Eq.symm
              (Finset.mul_sum Finset.univ (fun i ↦ (G c_pos h' x (↑j + 1) (S i) - F x (S i)) ^ 2)
                (↑m)⁻¹)
        rw [this]
        dsimp only [ej]
        exact DistFG c_pos h' x ((j : ℕ) + 1) cs
      have r1 : √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2) / ↑m ≤ ej c j / Real.sqrt m := by
        suffices √(∑ i, ((hk.2 - (F x)) (S i)) ^ 2 / ↑m) ≤ ej c j from by
          rw [<- Finset.sum_div] at this
          simp at this
          have u : √(∑ i, (hk.2 - F x) (S i) ^ 2) / ↑m = (√(∑ i, (hk.2 - F x) (S i) ^ 2) / √↑m) / √↑m := by
            field_simp
            congr
            apply Real.sq_sqrt
            exact Nat.cast_nonneg m
          rw [u]
          apply div_le_div_of_nonneg_right this
          simp

        have gh : hk.2 = G c_pos h' x j := by rw [<- fhx]
        rw [gh]
        have : √(∑ i, (G c_pos h' x j - F x) (S i) ^ 2 / ↑m) = empiricalDist S (F x) (G c_pos h' x j) := by
          rw [empiricalDist_comm]
          dsimp [empiricalDist, empiricalNorm]
          apply congrArg
          simp [div_eq_mul_inv, mul_comm]
          exact
            Eq.symm
              (Finset.mul_sum Finset.univ (fun i ↦ (G c_pos h' x (↑j) (S i) - F x (S i)) ^ 2)
                (↑m)⁻¹)
        rw [this]
        dsimp only [ej]
        exact DistFG c_pos h' x j cs
      rw [rp]
      apply add_le_add r0 r1
    · exact
      Real.sqrt_nonneg
        (2 * Real.log (↑(coveringNumber h' (ej c ((j : ℕ) + 1))) * ↑(coveringNumber h' (ej c (j : ℕ)))))
  _ = ∑ j : Fin n, ((6 * (ej c (j+1) - ej c (j+2))) * (√(2 * Real.log ((coveringNumber h' (ej c (j+1))) * (coveringNumber h' (ej c j)))))/(Real.sqrt m)) := by
    apply congrArg
    ext j
    field_simp
  _ ≤ ∑ j : Fin n, ((6 * (ej c (j+1) - ej c (j+2))) * (√(2 * Real.log ((coveringNumber h' (ej c (j+1))) * (coveringNumber h' (ej c (j+1))))))/(Real.sqrt m)):= by
    refine Finset.sum_le_sum ?_
    intro s si
    refine div_le_div_of_nonneg_right ?_ ?_
    · refine mul_le_mul_of_nonneg_left ?_ ?_
      · have NonemptyFS : Nonempty (EmpiricalFunctionSpace F S) := by
          rename_i h
          obtain ⟨i⟩ := h
          use i
        apply Real.sqrt_le_sqrt
        refine (mul_le_mul_iff_of_pos_left (by simp)).mpr ?_
        apply Real.log_le_log
        refine Left.mul_pos ?_ ?_
        repeat (norm_cast; apply coveringNumber_nonzero; simp; apply ej_pos c_pos)
        refine (mul_le_mul_iff_of_pos_left (by norm_cast; apply coveringNumber_nonzero; simp; apply ej_pos c_pos)).mpr ?_
        · norm_cast
          apply converingNumber_antitone
          repeat(apply ej_pos c_pos)
          dsimp [ej]
          refine (div_le_div_iff_of_pos_left c_pos ?_ ?_).mpr ?_
          repeat simp
          refine (pow_le_pow_iff_right₀ ?_).mpr ?_
          repeat simp
      · refine Left.mul_nonneg (by simp) ?_
        simp
        dsimp [ej]
        refine (div_le_div_iff_of_pos_left c_pos ?_ ?_).mpr ?_
        repeat simp
        refine (pow_le_pow_iff_right₀ ?_).mpr ?_
        repeat simp
    simp
  _ = ∑ j : Fin n, 6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) * (√(4 * Real.log ↑(coveringNumber h' (ej c ((j : ℕ) + 1)))) / (Real.sqrt m)) := by
    repeat apply congrArg
    ext j
    -- Factor out the covering number calculation
    have covering_calc : √(Real.log ((coveringNumber h' (ej c ((j : ℕ) + 1))) * (coveringNumber h' (ej c ((j : ℕ) + 1))))) =
        √(2 * Real.log (coveringNumber h' (ej c ((j : ℕ) + 1)))) := by
      calc
      _ = √(Real.log ((coveringNumber h' (ej c ((j : ℕ) + 1))) ^ 2)) := by
        repeat apply congrArg
        symm
        norm_cast
        exact pow_two ↑(coveringNumber h' (ej c (j + 1)))
      _ = √(2 * Real.log (coveringNumber h' (ej c ((j : ℕ) + 1)))) := by
        rw [Real.log_pow]
        norm_cast
      _ = _ := by simp
    have : √(4 * Real.log ↑(coveringNumber h' (ej c ((j : ℕ) + 1)))) = √2 * √(2 * Real.log ↑(coveringNumber h' (ej c ((j : ℕ) + 1)))) := by
      simp
      rw [<- mul_assoc]
      simp
      left
      rw [← (by norm_num : (2 : ℝ) ^ 2 = 4), Real.sqrt_sq]
      simp
    rw [this, <- covering_calc]
    rw [mul_div_assoc]
    apply congrArg
    have : √(2 * Real.log (↑(coveringNumber h' (ej c ((j : ℕ) + 1))) * ↑(coveringNumber h' (ej c ((j : ℕ) + 1))))) =
      √2 * √(Real.log (↑(coveringNumber h' (ej c ((j : ℕ) + 1))) * ↑(coveringNumber h' (ej c ((j : ℕ) + 1))))) := by
      simp
    rw [this]
  -- パートAとパートBの右辺を命題の右辺で抑える
private lemma a1 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalRademacherComplexity_without_abs m F S ≤ (ej c n) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber h' (ej c (j+1)))))) := by
  apply le_trans (a0 cs h' n)
  refine add_le_add ?_ ?_
  · rw [mul_assoc]
    apply inv_mul_le_of_le_mul₀
    · simp
    · apply ej_nonneg c_pos
    · calc
      _ ≤ signs_card_inv m * ∑ (σ : Signs m), ⨆ (fh : ι), (m : ℝ) * (ej c n) := by
        refine inv_mul_le_of_le_mul₀ (by simp) ?_ ?_
        · refine mul_nonneg (by dsimp [signs_card_inv]; simp ) ?_
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          refine mul_nonneg (by simp) ?_
          refine Real.iSup_nonneg' ?_
          simp only [exists_const]
          refine mul_nonneg (by simp) (by apply ej_nonneg c_pos)
        · rw [<- mul_assoc]
          rw [(by refine mul_inv_cancel₀ (by dsimp[Signs]; simp) : (Fintype.card (Signs m) : ℝ) * signs_card_inv m = 1)]
          simp only [one_mul]
          refine Finset.sum_le_sum ?_
          intro i hi
          apply ciSup_mono
          · refine bddAbove_def.mpr ?_
            use m * c
            intro y hy
            simp only [Set.range_const, Set.mem_singleton_iff] at hy
            rw [hy]
            apply mul_le_mul_of_nonneg_left _ (by simp)
            · dsimp [ej]
              refine div_le_self (le_of_lt c_pos) ?_
              · norm_cast
                apply Nat.one_le_pow
                simp
          intro x
          apply aA c_pos h' cs
      _ = signs_card_inv m * ∑ σ, (m : ℝ) * ej c n := by
        repeat apply congrArg
        ext σ
        simp
      _ = signs_card_inv m * ((Fintype.card (Signs m) : ℝ) * ((m : ℝ) * ej c n)) := by
        apply congrArg
        simp
      _ = _ := by
        rw [<- mul_assoc]
        have t : signs_card_inv m * (Fintype.card (Signs m) : ℝ) = 1 := by
          refine inv_mul_cancel₀ ?_
          dsimp [Signs]
          simp
        rw [t]
        simp
  · apply le_of_le_of_eq
    · exact aB c_pos h' n m_pos cs
    · rw [Finset.mul_sum]
      apply congrArg
      ext j
      calc
      _ = (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) * (6 * (√(4 * Real.log ↑(coveringNumber h' (ej c ((j : ℕ) + 1)))) / (Real.sqrt m))) := by ring
      _ = ((ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) * ((12 / (Real.sqrt m)) * √(Real.log ↑(coveringNumber h' (ej c ((j : ℕ) + 1)))))) := by
        apply congrArg
        calc
        _ = 6 * (2 * √(Real.log ↑(coveringNumber h' (ej c ((j : ℕ) + 1)))) / (Real.sqrt m)) := by
          apply congrArg
          field_simp
          simp only [Nat.ofNat_nonneg, Real.sqrt_mul, mul_eq_mul_right_iff]
          left
          suffices √(2 * 2) = 2 from by
            rw [<- this]
            rw [Real.sqrt_inj]
            linarith
            linarith
            linarith
          simp
        _ = _ := by ring
      _ = _ := by ring

theorem MonotoneOn.integral_le_sum_Ico0 (n : ℕ) (f : ℕ → ℝ) (g : ℝ → ℝ)
    (hf : Monotone f) (hg : AntitoneOn g (Set.Icc (f 0) (f n))) (j : Fin n):
    (f (j+1) - f j) * g (f (j+1)) ≤ ∫ (x : ℝ) in (f j)..(f (j+1)), g x := by
  calc
  _ = ∫ (x : ℝ) in (f j)..(f (j+1)), g (f (j+1)) := by
    simp
  _ ≤ _ := by
    apply intervalIntegral.integral_mono_on
    · apply hf
      simp
    · apply AntitoneOn.intervalIntegrable
      exact antitoneOn_const
    · apply AntitoneOn.intervalIntegrable
      refine antitoneOn_iff_forall_lt.mpr ?_
      intro a ha b hb hab
      apply hg
      · suffices Set.uIcc (f (j : ℕ)) (f ((j : ℕ) + 1)) ⊆ Set.Icc (f 0) (f n) from by
          grind
        refine Set.uIcc_subset_Icc ?_ ?_
        · constructor
          · apply hf
            simp
          · apply hf
            simp
        · constructor
          · apply hf
            simp
          · apply hf
            refine Order.add_one_le_of_lt ?_; simp
      · suffices Set.uIcc (f (j : ℕ)) (f ((j : ℕ) + 1)) ⊆ Set.Icc (f 0) (f n) from by
          grind
        refine Set.uIcc_subset_Icc ?_ ?_
        · constructor
          · apply hf
            simp
          · apply hf
            simp
        · constructor
          · apply hf
            simp
          · apply hf
            refine Order.add_one_le_of_lt ?_; simp
      exact le_of_lt hab
    intro x hx
    simp at hx
    apply hg
    · constructor
      · have : f 0 ≤ f (j : ℕ) := by apply hf; simp
        linarith
      · have : f ((j : ℕ) + 1) ≤ f n := by apply hf; refine Order.add_one_le_of_lt ?_; simp
        linarith
    · constructor
      · apply hf
        simp
      · apply hf
        refine Order.add_one_le_of_lt ?_; simp
    exact hx.2

theorem AntitoneOn.integral_le_sum_Ico' (n : ℕ) (f : ℕ → ℝ) (g : ℝ → ℝ)
    (hf : Antitone f) (hg : AntitoneOn g (Set.Icc (f n) (f 0))):
    ∑ j : Fin n, (f j - f (j+1)) * g (f j) ≤ ∫ (x : ℝ) in (f n)..(f 0), g x := by
  by_cases hnpos : 0 < n
  · let h (p : ℕ) := f (n-p)
    have s0 : f n = h 0 := by dsimp [h]
    have s1 : f 0 = h n := by dsimp [h]; simp
    have hh' : Monotone h := by
      dsimp [h]
      change Monotone (f ∘ (fun p ↦ (n - p)))
      apply Antitone.comp
      exact hf
      exact antitone_const_tsub
    rw [s0, s1]
    rw [<- intervalIntegral.sum_integral_adjacent_intervals]
    have t : ∑ j : Fin n, (f (j : ℕ) - f ((j : ℕ) + 1)) * g (f (j : ℕ)) = ∑ j : Fin n, (h ((j : ℕ) + 1) - h (j : ℕ)) * g (h ((j : ℕ) + 1)) := by
      let φ : Fin n ≃ Fin n :=
        { toFun := fun j =>
            ⟨n - 1 - j, by
              have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hnpos)
              exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
          invFun := fun j =>
            ⟨n - 1 - j, by
              have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hnpos)
              exact lt_of_le_of_lt (Nat.sub_le _ _) hlt⟩
          left_inv := by
            intro j
            apply Fin.ext
            have hjle : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
            have : n - 1 - (n - 1 - j) = j := by grind
            simp [this]
          right_inv := by
            intro j
            apply Fin.ext
            have hjle : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
            have : n - 1 - (n - 1 - j) = j := by grind
            simp [this] }

      have tsum := (Equiv.sum_comp φ (fun j : Fin n => (f j - f (j + 1)) * g (f j)))
      -- simp the rewritten sum to expose `h`
      refine tsum.symm.trans ?_
      refine Finset.sum_congr rfl ?_
      intro j _
      -- unpack φ and h
      change (f (φ j) - f (φ j + 1)) * g (f (φ j)) = (h (j + 1) - h j) * g (h (j + 1))
      dsimp [φ, h]
      -- arithmetic on naturals
      have hjle : (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt j.is_lt
      simp [Nat.sub_sub, Nat.add_comm]
      left
      apply congrArg
      grind
    rw [t]
    have u : ∑ k ∈ Finset.range n, ∫ (x : ℝ) in h k..h (k + 1), g x = ∑ k : Fin n, ∫ (x : ℝ) in h k..h (k + 1), g x := by
      exact Finset.sum_range fun i ↦ ∫ (x : ℝ) in h i..h (i + 1), g x
    rw [u]
    apply Finset.sum_le_sum
    intro i yi
    apply MonotoneOn.integral_le_sum_Ico0
    · exact hh'
    · rw [<-s0]
      rw [<-s1]
      exact hg
    intro k kn
    apply AntitoneOn.intervalIntegrable
    rw [s0] at hg
    rw [s1] at hg
    apply hg.mono
    refine Set.uIcc_subset_Icc ?_ ?_
    constructor
    · apply hh'
      simp
    · apply hh'
      linarith
    constructor
    · apply hh'
      simp
    · apply hh'
      linarith
  · have n_zero : n = 0 := by linarith
    rw [n_zero]
    simp

private lemma ej_antitone (c_nonneg : 0 ≤ c) : Antitone (fun n : ℕ ↦ ej c n) := by
  dsimp [ej]
  refine Antitone.const_mul ?_ ?_
  refine inv_pow_anti ?_
  norm_num
  exact c_nonneg

private lemma a2 (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalRademacherComplexity_without_abs m F S ≤ 2 * (ej c (n+1)) + 12 / (Real.sqrt m)*(∫ (x : ℝ) in (ej c (n+1))..(c/2),√(Real.log (coveringNumber h' x))) := by
  calc
  _ ≤ (ej c n) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber h' (ej c (j+1)))))) := a1 c_pos h' n m_pos cs
  _ = 2 * (ej c (n+1)) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber h' (ej c (j+1)))))) := by
    refine add_right_cancel_iff.mpr ?_
    dsimp [ej]
    grind
  _ ≤ _ := by
    suffices (∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber h' (ej c (j+1)))))) ≤ (∫ (x : ℝ) in (ej c (n + 1))..(c/2),√(Real.log (coveringNumber h' x))) from by
      refine (add_le_add_iff_left (2 * ej c (n + 1))).mpr ?_
      apply mul_le_mul_of_nonneg_left
      exact this
      refine div_nonneg ?_ ?_
      simp
      simp
    let f := fun (x : ℕ) ↦ ej c (x + 1)
    have : c / 2 = ej c 1 := by
      dsimp [ej]
      simp
    rw [this]
    let g := fun x ↦ √(Real.log ↑(coveringNumber h' x))
    suffices ∑ j : Fin n, (f j - f (j + 1)) * g (f j) ≤ ∫ (x : ℝ) in f n..f 0, g x from by
      dsimp [f, g] at this
      have p (j : Fin n) : (j : ℕ) + 1 + 1 = (j : ℕ) + 2 := by ring
      apply le_of_eq_of_le rfl
      exact this
    have s : 0 < f n := by
      dsimp [f]
      dsimp [ej]
      simp
      exact c_pos
    apply AntitoneOn.integral_le_sum_Ico'
    · dsimp [f]
      refine Antitone.covariant_of_const' ?_ 1
      apply ej_antitone
      apply le_of_lt c_pos
    · dsimp [g]
      have f0 : Monotone (fun x ↦ √x) := by apply Real.sqrt_le_sqrt
      apply Monotone.comp_antitoneOn f0
      refine antitoneOn_iff_forall_lt.mpr ?_
      intro a ha b hb hab
      apply Real.log_le_log
      · apply Nat.cast_pos.mpr
        apply coveringNumber_nonzero
        · exact e_nonempty
        simp at hb
        linarith
      norm_cast
      apply converingNumber_antitone
      simp
      simp at ha
      linarith
      simp
      simp at hb
      linarith
      apply le_of_lt hab

omit [Nonempty ι] in
private lemma w (ε : ℝ) (ε_pos : 0 < ε) (c_ε : ε < c / 2) :
  ∃ n, (ε < (ej c (n+1))) ∧ ((ej c (n+1)) ≤ 2 * ε) := by
  dsimp [ej]
  suffices ∃ n : ℕ, n < Real.logb 2 (c / ε) ∧ Real.logb 2 (c / ε) ≤ n + 1 from by
    obtain ⟨m0, ⟨hm1, hm2⟩⟩ := this
    rw [Real.logb_le_iff_le_rpow] at hm2
    rw [Real.lt_logb_iff_rpow_lt] at hm1
    have r : 0 < m0 := by
      have r0 : 2 < c / ε := by
        have r00 : 2 * ε < c := by
          refine (lt_div_iff₀' ?_).mp c_ε
          norm_num
        exact (lt_div_iff₀ ε_pos).mpr r00
      have r1 : (2 : ℝ) < (2 : ℝ) ^ (↑m0 + 1) := by
        norm_cast at hm2
        apply lt_of_lt_of_le r0
        norm_cast
      simp at r1
      have r2 : (2 ^ 1 : ℝ) < 2 ^ (m0 + 1) := by
        norm_num
        exact r1
      have r3 : (1 : ℝ) < (m0 + 1) := by
        norm_cast
        norm_cast at r2
        rw [<- Nat.pow_lt_pow_iff_right]
        exact r2
        norm_cast
      norm_cast at r3
      linarith
    have p0 : ε < c / 2 ^ (↑m0) := by
      have htmp := mul_lt_mul_of_pos_right hm1 ε_pos
      have htmp' : ε * 2 ^ (↑m0) < c := by
        field_simp at htmp
        simp at htmp
        rw [mul_comm]
        exact htmp
      have hpowpos : 0 < (2 : ℝ) ^ (↑m0) := pow_pos (by norm_num) _
      have := mul_lt_mul_of_pos_right htmp' (inv_pos.mpr hpowpos)
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
    have p1 : c / 2 ^ (↑m0) ≤ 2 * ε := by
      have htmp : c ≤ ε * 2 ^ (↑m0 + 1) := by
        have := mul_le_mul_of_nonneg_left hm2 (le_of_lt ε_pos)
        field_simp at this
        norm_cast at this
        norm_cast
      have hpowpos : 0 < (2 : ℝ) ^ (↑m0) := pow_pos (by norm_num) _
      have hpow_ne : (2 : ℝ) ^ (↑m0) ≠ 0 := by exact ne_of_gt hpowpos
      calc
        c / 2 ^ (↑m0) = c * ((2 : ℝ) ^ (↑m0))⁻¹ := by
          simp [div_eq_mul_inv]
        _ ≤ (ε * 2 ^ (↑m0 + 1)) * ((2 : ℝ) ^ (↑m0))⁻¹ := by
          exact mul_le_mul_of_nonneg_right htmp (inv_nonneg.mpr (le_of_lt hpowpos))
        _ = ε * 2 := by
          simp [pow_succ, mul_comm, mul_assoc, hpow_ne]
        _ = 2 * ε := by ring
    use (m0 - 1)
    have : m0 - 1 + 1 = m0 := by
      grind
    rw [this]
    exact ⟨p0, p1⟩
    · norm_num
    · field_simp
      linarith
    · norm_num
    · field_simp
      linarith
  use Int.toNat (Int.ceil (Real.logb 2 (c / ε))) - 1
  have h3 : 0 < Real.logb 2 (c / ε) := by
    refine Real.logb_pos (by linarith) ?_
    refine (one_lt_div₀ ε_pos).mpr ?_
    apply lt_trans c_ε
    linarith
  have h2 :
      ((⌈Real.logb 2 (c / ε)⌉ : ℤ) : ℝ) =
      ((⌈Real.logb 2 (c / ε)⌉.toNat : ℕ) : ℝ) := by
        norm_cast
        refine Int.eq_natCast_toNat.mpr ?_
        exact Int.ceil_nonneg (le_of_lt h3)
  have : (1 : ℤ) ≤ ⌈Real.logb 2 (c / ε)⌉ := by
    simpa using Int.one_le_ceil_iff.mpr h3
  have hceil_nonneg : 0 ≤ ⌈Real.logb 2 (c / ε)⌉ := Int.ceil_nonneg (le_of_lt h3)
  have hcast : Int.ofNat (⌈Real.logb 2 (c / ε)⌉.toNat) = ⌈Real.logb 2 (c / ε)⌉ :=
    Int.toNat_of_nonneg hceil_nonneg
  have h_nat : 1 ≤ ⌈Real.logb 2 (c / ε)⌉.toNat := by
    have : (Int.ofNat 1) ≤ Int.ofNat (⌈Real.logb 2 (c / ε)⌉.toNat) := by
      simpa [hcast] using this
    exact (Int.ofNat_le).1 this
  constructor
  · rw [Nat.cast_sub]
    rw [<- h2]
    simp
    rw [<- Int.le_ceil_iff]
    simpa using h_nat
  · norm_cast
    have : ⌈Real.logb 2 (c / ε)⌉.toNat - 1 + 1 = ⌈Real.logb 2 (c / ε)⌉.toNat := by
      exact Nat.sub_add_cancel h_nat
    rw [this]
    rw [<- h2]
    exact Int.le_ceil (Real.logb 2 (c / ε))

theorem dudley_entropy_integral' {ε : ℝ} (ε_pos : 0 < ε) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
  (ε_le_c_div_2 : ε < c/2) :
    empiricalRademacherComplexity_without_abs m F S ≤
    (4 * ε + (12 / (Real.sqrt m)) *
    (∫ (x : ℝ) in ε..(c/2),√(Real.log (coveringNumber h' x)))) := by
  obtain ⟨n, ⟨nw1, nw2⟩⟩ := w ε ε_pos ε_le_c_div_2
  have ε_c : ε ≤ c := by linarith
  have c_pos : 0 < c := lt_of_le_of_lt' ε_c ε_pos
  apply le_trans (a2 c_pos h' n m_pos cs)
  apply add_le_add
  · linarith
  · apply mul_le_mul_of_nonneg_left
    · apply intervalIntegral.integral_mono_interval (le_of_lt nw1)
      · dsimp [ej]
        rw [div_le_div_iff_of_pos_left]
        · have := Nat.one_lt_two_pow' n
          rw [<- Nat.add_one_le_iff] at this
          simp only [Nat.reduceAdd] at this
          norm_cast
        · exact c_pos
        · simp
        · simp
      · simp
      · filter_upwards
        intro a
        simp
      · apply AntitoneOn.intervalIntegrable
        have f0 : Monotone (fun x ↦ √x) := by apply Real.sqrt_le_sqrt
        apply Monotone.comp_antitoneOn f0
        refine antitoneOn_iff_forall_lt.mpr ?_
        intro a ha b hb hab
        dsimp [Set.uIcc] at ha
        dsimp [Set.Icc] at ha
        have : min ε (c / 2) = ε := by
          simp
          linarith
        rw [this] at ha
        dsimp [Set.uIcc] at hb
        dsimp [Set.Icc] at hb
        rw [this] at hb
        apply Real.log_le_log
        · apply Nat.cast_pos.mpr
          apply coveringNumber_nonzero
          · exact e_nonempty
          linarith
        · norm_cast
          apply converingNumber_antitone
          · simp
            linarith
          · simp
            linarith
          · exact le_of_lt hab
    · refine div_nonneg ?_ ?_
      · simp
      · norm_cast
        simp
