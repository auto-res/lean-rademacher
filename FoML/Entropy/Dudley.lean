import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import FoML.Defs
import FoML.Entropy.PseudoMetric
import FoML.Entropy.Massart
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Base
import FoML.ForMathlib.Analysis.SumIntegralComparisons

universe v u
open scoped BigOperators
open Classical ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

private def signSymmetrizationPosMap :
    EmpiricalFunctionSpace F S →
      EmpiricalFunctionSpace (signSymmetrization F) S :=
  fun q ↦ ⟨(q.index, true)⟩

private def signSymmetrizationNegMap :
    EmpiricalFunctionSpace F S →
      EmpiricalFunctionSpace (signSymmetrization F) S :=
  fun q ↦ ⟨(q.index, false)⟩

omit [Nonempty ι] in
private lemma signSymmetrizationPosMap_isometry :
    Isometry (signSymmetrizationPosMap (F := F) (S := S)) := by
  apply Isometry.of_dist_eq
  intro q r
  rfl

omit [Nonempty ι] in
private lemma signSymmetrizationNegMap_isometry :
    Isometry (signSymmetrizationNegMap (F := F) (S := S)) := by
  apply Isometry.of_dist_eq
  intro q r
  exact empiricalDist_neg_neg S (F q.index) (F r.index)

omit [Nonempty ι] in
/-- Total boundedness is preserved when a class is enlarged by all of its negatives. -/
theorem signSymmetrization_totallyBounded
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace (signSymmetrization F) S)) := by
  have hpos :
      TotallyBounded
        (signSymmetrizationPosMap (F := F) (S := S) ''
          (Set.univ : Set (EmpiricalFunctionSpace F S))) :=
    h.image signSymmetrizationPosMap_isometry.uniformContinuous
  have hneg :
      TotallyBounded
        (signSymmetrizationNegMap (F := F) (S := S) ''
          (Set.univ : Set (EmpiricalFunctionSpace F S))) :=
    h.image signSymmetrizationNegMap_isometry.uniformContinuous
  rw [show
    (Set.univ : Set (EmpiricalFunctionSpace (signSymmetrization F) S)) =
      signSymmetrizationPosMap (F := F) (S := S) ''
          (Set.univ : Set (EmpiricalFunctionSpace F S)) ∪
        signSymmetrizationNegMap (F := F) (S := S) ''
          (Set.univ : Set (EmpiricalFunctionSpace F S)) by
    ext q
    constructor
    · intro _
      rcases q with ⟨⟨i, b⟩⟩
      cases b
      · right
        exact ⟨⟨i⟩, Set.mem_univ _, rfl⟩
      · left
        exact ⟨⟨i⟩, Set.mem_univ _, rfl⟩
    · simp]
  exact hpos.union hneg

omit [Nonempty ι] in
/--
Adjoining pointwise negatives increases a positive-radius covering number by
at most a factor of two.
-/
lemma coveringNumber_signSymmetrization_le_two_mul
    (h : TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace F S)))
    {ε : ℝ} (hε : 0 < ε) :
    coveringNumber
        (signSymmetrization_totallyBounded (F := F) (S := S) h) ε ≤
      2 * coveringNumber h ε := by
  let t := coveringFinset h hε
  let tpos :=
    t.image (signSymmetrizationPosMap (F := F) (S := S))
  let tneg :=
    t.image (signSymmetrizationNegMap (F := F) (S := S))
  let centers := tpos ∪ tneg
  have hcard : centers.card ≤ 2 * coveringNumber h ε := by
    calc
      centers.card ≤ tpos.card + tneg.card := by
        dsimp only [centers]
        exact Finset.card_union_le _ _
      _ ≤ t.card + t.card :=
        add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * coveringNumber h ε := by
        rw [coveringFinset_card h hε]
        ring
  refine (coveringNumber_le_card_of_cover
    (signSymmetrization_totallyBounded (F := F) (S := S) h)
    hε centers ?_).trans hcard
  intro q _
  rcases q with ⟨⟨i, b⟩⟩
  have hcover := coveringFinset_cover h hε
    (show (⟨i⟩ : EmpiricalFunctionSpace F S) ∈ Set.univ by simp)
  simp only [Set.mem_iUnion] at hcover ⊢
  obtain ⟨y, hyt, hyball⟩ := hcover
  cases b
  · let center :=
      signSymmetrizationNegMap (F := F) (S := S) y
    refine ⟨center, ?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, hyt, rfl⟩)
    · change dist
        (signSymmetrizationNegMap (F := F) (S := S)
          (⟨i⟩ : EmpiricalFunctionSpace F S)) center < ε
      calc
        dist
            (signSymmetrizationNegMap (F := F) (S := S)
              (⟨i⟩ : EmpiricalFunctionSpace F S)) center =
            dist (⟨i⟩ : EmpiricalFunctionSpace F S) y := by
          dsimp only [center]
          exact (signSymmetrizationNegMap_isometry
            (F := F) (S := S)).dist_eq _ _
        _ < ε := Metric.mem_ball.mp hyball
  · let center :=
      signSymmetrizationPosMap (F := F) (S := S) y
    refine ⟨center, ?_, ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨y, hyt, rfl⟩)
    · change dist
        (signSymmetrizationPosMap (F := F) (S := S)
          (⟨i⟩ : EmpiricalFunctionSpace F S)) center < ε
      calc
        dist
            (signSymmetrizationPosMap (F := F) (S := S)
              (⟨i⟩ : EmpiricalFunctionSpace F S)) center =
            dist (⟨i⟩ : EmpiricalFunctionSpace F S) y := by
          dsimp only [center]
          exact (signSymmetrizationPosMap_isometry
            (F := F) (S := S)).dist_eq _ _
        _ < ε := Metric.mem_ball.mp hyball

variable {c : ℝ}
  -- Dyadic radius sequence, associated cover, and cover cardinality.
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
private lemma exists_cover_approximation (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
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

private noncomputable def coverApprox (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) : ι → ℕ → EmpiricalFunctionSpace F S :=
    fun fh j => Classical.choose (exists_cover_approximation c_pos h fh j)

omit [Nonempty ι] in
private lemma coverApprox_mem_cover (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : coverApprox c_pos h fh j ∈ cj c_pos h j := by
  classical
  exact (Classical.choose_spec (exists_cover_approximation c_pos h fh j)).1

omit [Nonempty ι] in
private lemma empiricalDist_coverApprox_le_radius (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : empiricalDist S (F fh) (coverApprox c_pos h fh j) ≤ ej c j := by
  classical
  exact (Classical.choose_spec (exists_cover_approximation c_pos h fh j)).2

private noncomputable def chainApprox (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) : ι → ℕ → Z → ℝ :=
    fun fh j => if j = 0 then 0 else (coverApprox c_pos h fh j : Z → ℝ)

omit [Nonempty ι] in
private lemma chainApprox_def (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))): ∀ fh j, chainApprox c_pos h fh j = if j = 0 then 0 else (coverApprox c_pos h fh j : Z → ℝ) := by
    intro fh j
    dsimp [chainApprox]

omit [Nonempty ι] in
private lemma chainApprox_succ (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (fh : ι) (j : ℕ) : chainApprox c_pos h fh (j + 1) = (coverApprox c_pos h fh (j + 1) : Z → ℝ) := by
  simp [chainApprox]

omit [Nonempty ι] in
private lemma chain_decomposition (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (fh : ι) (n : ℕ):
      F fh = F fh - chainApprox c_pos h fh n + ∑ j : Fin n, (chainApprox c_pos h fh ((j : ℕ) + 1) - chainApprox c_pos h fh ((j : ℕ))) := by
  induction n with
  | zero => simp [chainApprox]
  | succ n hn =>
    nth_rewrite 1 [hn]
    rw [Fin.sum_univ_castSucc]
    simp
    ring_nf

omit [Nonempty ι] in
private lemma pointwise_bound_from_empirical_norm (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i : Fin m) (hm_pos : 0 < m) :
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

private lemma chainApprox_pointwise_bound (c_pos : 0 < c) (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i_1 : ℕ) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ (i_2 : Fin m) (a : ι), |chainApprox c_pos h a i_1 (S i_2)| ≤ √↑m * c := by
  dsimp [chainApprox]
  by_cases h0 : i_1 = 0
  · rw [h0]
    simp
    intro i_2
    have : 0 ≤ √↑m := by simp
    exact (mul_nonneg_iff_of_pos_right c_pos).mpr this
  · simp [h0]
    intro i_2
    apply pointwise_bound_from_empirical_norm
    intro f
    apply cs
    exact m_pos

private lemma chainApprox_increment_bound (c_pos : 0 < c) (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (i_1 : ℕ) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) :
    ∀ (i_2 : Fin m) (a : ι), |chainApprox c_pos h a (i_1 + 1) (S i_2) - chainApprox c_pos h a (i_1) (S i_2)| ≤ 2 * (√↑m * c) := by
  intro i_2 a
  calc
  _ ≤ |chainApprox c_pos h a (i_1 + 1) (S i_2)| + |chainApprox c_pos h a i_1 (S i_2)| := by
    exact abs_sub (chainApprox c_pos h a (i_1 + 1) (S i_2)) (chainApprox c_pos h a i_1 (S i_2))
  _ ≤ √↑m * c + √↑m * c := by
    apply add_le_add
    apply chainApprox_pointwise_bound
    exact m_pos
    exact cs
    apply chainApprox_pointwise_bound
    exact m_pos
    exact cs
  _ = _ := by ring

private theorem splitBound.bddAbove_main_term {c_pos : 0 < c} (cs : ∀ (f : ι), empiricalNorm S (F f) ≤ c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (m_pos : ¬m = 0)
  (i : Signs m):
  BddAbove (Set.range fun fh ↦ ∑ i_1, ↑↑(i i_1) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) := by
  rw [bddAbove_def]
  classical
  refine ⟨m * (2 * (Real.sqrt (m : ℝ) * c)), ?_⟩
  intro y hy
  rcases hy with ⟨fh, rfl⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero m_pos
  calc
    (∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1)))
        ≤ ∑ i_1, |(i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))| := by
          refine Finset.sum_le_sum ?_
          intro _ _
          exact le_abs_self _
    _ = ∑ i_1, |F fh (S i_1) - chainApprox c_pos h fh n (S i_1)| := by
          apply Finset.sum_congr rfl
          intro _ _
          simp [abs_mul]
    _ ≤ ∑ i_1, (|F fh (S i_1)| + |chainApprox c_pos h fh n (S i_1)|) := by
          refine Finset.sum_le_sum ?_
          intro i_1 _
          have htri : |F fh (S i_1) - chainApprox c_pos h fh n (S i_1)|
              ≤ |F fh (S i_1)| + |chainApprox c_pos h fh n (S i_1)| := by
            exact abs_sub (F fh (S i_1)) (chainApprox c_pos h fh n (S i_1))
          exact htri
    _ ≤ ∑ i_1, (Real.sqrt (m : ℝ) * c + Real.sqrt (m : ℝ) * c) := by
          refine Finset.sum_le_sum ?_
          intro i_1 _
          have hF : |F fh (S i_1)| ≤ Real.sqrt (m : ℝ) * c := pointwise_bound_from_empirical_norm cs i_1 hmpos fh
          have hG : |chainApprox c_pos h fh n (S i_1)| ≤ Real.sqrt (m : ℝ) * c := chainApprox_pointwise_bound c_pos hmpos cs n h i_1 fh
          have : |F fh (S i_1)| + |chainApprox c_pos h fh n (S i_1)| ≤ Real.sqrt (m : ℝ) * c + Real.sqrt (m : ℝ) * c := by
            nlinarith
          exact this
    _ = m * (2 * (Real.sqrt (m : ℝ) * c)) := by
      simp
      grind

private theorem splitBound.bddAbove_increment_term {c_pos : 0 < c} (cs : ∀ (f : ι), empiricalNorm S (F f) ≤ c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (m_pos : ¬m = 0)
  (i : Signs m) :
  BddAbove
    (Set.range fun fh ↦
      ∑ x_1 : Fin n, ∑ i_1, ↑↑(i i_1) * (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) - chainApprox c_pos h fh (↑x_1) (S i_1))) := by
  rw [bddAbove_def]
  classical
  refine ⟨(n : ℝ) * m * (2 * (Real.sqrt (m : ℝ) * c)), ?_⟩
  intro y hy
  rcases hy with ⟨fh, rfl⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero m_pos
  calc
    (∑ x_1 : Fin n, ∑ i_1, (i i_1 : ℝ) * (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) - chainApprox c_pos h fh (↑x_1) (S i_1)))
        ≤ ∑ x_1 : Fin n, ∑ i_1, |(i i_1 : ℝ) * (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) - chainApprox c_pos h fh (↑x_1) (S i_1))| := by
          refine Finset.sum_le_sum ?_
          intro _ _
          refine Finset.sum_le_sum ?_
          intro _ _
          exact le_abs_self _
        _ = ∑ x_1 : Fin n, ∑ i_1, |chainApprox c_pos h fh (↑x_1 + 1) (S i_1) - chainApprox c_pos h fh (↑x_1) (S i_1)| := by
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
              have hdiff : |chainApprox c_pos h fh (↑x_1 + 1) (S i_1) - chainApprox c_pos h fh (↑x_1) (S i_1)| ≤ 2 * (Real.sqrt (m : ℝ) * c) :=
                chainApprox_increment_bound c_pos hmpos cs (↑x_1) h i_1 fh
              nlinarith
        _ = (n : ℝ) * m * (2 * (Real.sqrt (m : ℝ) * c)) := by
              simp [Finset.sum_const, Finset.card_univ, mul_assoc, mul_left_comm, mul_comm]

  -- Split the target into the main term and the increment term.
private lemma split_main_and_increment_terms {c_pos : 0 < c} (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) :
  empiricalRademacherComplexity_without_abs m F S ≤
    ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((F fh (S i)) - chainApprox c_pos h fh n (S i)))) +
    ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * (chainApprox c_pos h fh (j+1) (S i) - chainApprox c_pos h fh j (S i)))) := by
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
      (∑ i : Fin m, (σ i : ℝ) * (((F fh) (S i) - chainApprox c_pos h fh n (S i)) +
        (∑ j : Fin n, (chainApprox c_pos h fh ((j : ℕ) + 1) (S i) - chainApprox c_pos h fh ((j : ℕ)) (S i)))))) := by
      repeat apply congrArg
      ext σ
      repeat apply congrArg
      ext fh
      apply congrArg
      ext i
      apply congrArg
      symm
      have h := congrArg (fun (h : Z → ℝ) => h (S i)) (chain_decomposition c_pos h fh n)
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at h
      symm
      exact h
    _ ≤ (m : ℝ)⁻¹ * ((signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i)))) +
      signs_card_inv m * ∑ j : Fin n, (∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (chainApprox c_pos h fh (j+1) (S i) - chainApprox c_pos h fh j (S i))))) := by
      rw [<- left_distrib]
      rw [Finset.sum_comm]
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · have w : (∑ σ : Signs m, ⨆ fh, ∑ i, (σ i : ℝ) * (F fh (S i) - chainApprox c_pos h fh n (S i))) + ∑ y : Signs m, ∑ x : Fin n, ⨆ fh, ∑ i,(y i : ℝ) * (chainApprox c_pos h fh (↑x + 1) (S i) - chainApprox c_pos h fh (↑x) (S i))
              = ∑ σ : Signs m, ((⨆ fh, ∑ i, (σ i : ℝ) * (F fh (S i) - chainApprox c_pos h fh n (S i))) + (∑ x : Fin n, ⨆ fh, ∑ i, (σ i : ℝ) * (chainApprox c_pos h fh (↑x + 1) (S i) - chainApprox c_pos h fh (↑x) (S i)))) := by
            let chainApprox_increment_bound (σ : Signs m) := ⨆ fh, ∑ i, (σ i : ℝ) * (F fh (S i) - chainApprox c_pos h fh n (S i))
            let chainApprox_pointwise_bound (y : Signs m) := ∑ x : Fin n, ⨆ fh, ∑ i,(y i : ℝ) * (chainApprox c_pos h fh (↑x + 1) (S i) - chainApprox c_pos h fh (↑x) (S i))
            have w' : ∑ σ : Signs m, chainApprox_increment_bound σ + ∑ y : Signs m, chainApprox_pointwise_bound y = ∑ σ : Signs m, (chainApprox_increment_bound σ + chainApprox_pointwise_bound σ) := Eq.symm Finset.sum_add_distrib
            dsimp [chainApprox_increment_bound, chainApprox_pointwise_bound] at w'
            exact w'
          rw [w]
          apply Finset.sum_le_sum
          intro i hi
          have q : ⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1) + ∑ j : Fin n, (chainApprox c_pos h fh ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h fh ((j : ℕ)) (S i_1))) ≤
            (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) +
              ⨆ fh, ∑ x : Fin n, ∑ i_1, (i i_1 : ℝ) * (chainApprox c_pos h fh (↑x + 1) (S i_1) - chainApprox c_pos h fh (↑x) (S i_1)) := by
            apply ciSup_le
            intro x
            -- split the inner sum into a constant part and the telescoping part
            have hx_split :
                (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1) +
                  ∑ j : Fin n, (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                = (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1))) +
                  (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1)))) := by
              -- distribute the product over the inner addition and split the outer sum
              simp [mul_add, Finset.sum_add_distrib]
            -- bound each part by the respective suprema
            have hx1 : (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1))) ≤
                ⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1)) := by
                  apply le_ciSup_of_le
                  · exact splitBound.bddAbove_main_term cs h n m_pos i
                  · exact Preorder.le_refl (∑ i_1, ↑↑(i i_1) * (F x (S i_1) - chainApprox c_pos h x n (S i_1)))
            calc
              (∑ i_1, (i i_1 : ℝ) * (F x (S i_1) - chainApprox c_pos h x n (S i_1) + ∑ j : Fin n, (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                  = _ := hx_split
              _ ≤ (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) +
                  (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1)))) := by
                nlinarith
              _ ≤ (⨆ fh, ∑ i_1, (i i_1 : ℝ) * (F fh (S i_1) - chainApprox c_pos h fh n (S i_1))) +
                  (⨆ fh, ∑ x : Fin n, ∑ i_1, (i i_1 : ℝ) * (chainApprox c_pos h fh (↑x + 1) (S i_1) - chainApprox c_pos h fh (↑x) (S i_1))) := by
                -- rewrite the second sum as a double sum and take fh = x in the supremum
                have hx2_swap :
                    (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                    = ∑ j : Fin n, ∑ i_1, (i i_1 : ℝ) * (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1)) := by
                  -- expand the outer product into an inner sum and then swap the summations
                  have h_expand : (∑ i_1, (i i_1 : ℝ) * (∑ j : Fin n, (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1))))
                      = ∑ i_1, ∑ j : Fin n, (i i_1 : ℝ) * (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1)) := by
                    apply Finset.sum_congr rfl
                    intro i1 hi1
                    -- move the scalar inside the inner sum
                    rw [Finset.mul_sum]
                  rw [h_expand]
                  rw [Finset.sum_comm]
                have hx2 : (∑ j : Fin n, ∑ i_1, (i i_1 : ℝ) * (chainApprox c_pos h x ((j : ℕ) + 1) (S i_1) - chainApprox c_pos h x ((j : ℕ)) (S i_1))) ≤
                    ⨆ fh, ∑ x_1 : Fin n, ∑ i_1, (i i_1 : ℝ) * (chainApprox c_pos h fh (↑x_1 + 1) (S i_1) - chainApprox c_pos h fh (↑x_1) (S i_1)) := by
                  apply le_ciSup_of_le
                  · exact splitBound.bddAbove_increment_term cs h n m_pos i
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
            _ ≤ ∑ i_2, |(i i_2 : ℝ) * (chainApprox c_pos h a (↑i_1 + 1) (S i_2) - chainApprox c_pos h a (↑i_1) (S i_2))| := Finset.sum_le_sum (fun i_2 hi_2 ↦  le_abs_self ((i i_2 : ℝ) * (chainApprox c_pos h a (↑i_1 + 1) (S i_2) - chainApprox c_pos h a (↑i_1) (S i_2))))
            _ ≤ ∑ i_2 : Fin m, 2 * (√↑m * c) := by
              apply Finset.sum_le_sum
              intro i_2 hi_2

              rw [abs_mul]
              simp
              apply chainApprox_increment_bound
              · apply Nat.pos_of_ne_zero m_pos
              · exact cs
            _ = _ := by simp
          · change ∑ i_1_1, (i i_1_1 : ℝ) * (chainApprox c_pos h x' (↑i_1 + 1) (S i_1_1) - chainApprox c_pos h x' (↑i_1) (S i_1_1)) ≤ ∑ i_2, (i i_2 : ℝ) * (chainApprox c_pos h x' (↑i_1 + 1) (S i_2) - chainApprox c_pos h x' (↑i_1) (S i_2))
            simp
        · dsimp [signs_card_inv]
          simp
      · simp
    _ = (m : ℝ)⁻¹ * ((signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i)))) +
      ∑ j : Fin n, ( signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (chainApprox c_pos h fh (j+1) (S i) - chainApprox c_pos h fh j (S i))))) := by
      simp
      left
      simp [Finset.mul_sum]
    _ = ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i)))) +
      (m : ℝ)⁻¹ * ∑ j : Fin n, ( signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
      (∑ i : Fin m, (σ i : ℝ) * (chainApprox c_pos h fh (j+1) (S i) - chainApprox c_pos h fh j (S i)))) := by
      rw [mul_add]
      rw [mul_assoc]
    _ = _ := by
      simp only [add_right_inj]
      simp [Finset.mul_sum, mul_assoc]

omit [Nonempty ι] in
private lemma empiricalDist_to_chainApprox_le_ej (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (fh : ι) (n : ℕ)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalDist S (F fh) (chainApprox c_pos h fh n) ≤ c / 2 ^ n := by
  by_cases h' : n = 0
  · simpa [chainApprox_def c_pos h, h'] using cs fh
  · simp [chainApprox_def c_pos h, h']
    exact (Classical.choose_spec (exists_cover_approximation c_pos h fh n)).2

private lemma signed_sum_le_empiricalDist (f g : Z → ℝ) (σ : Signs m) :
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

-- Part A
omit [Nonempty ι] in
private lemma partA_sup_bound (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (n : ℕ) : ∀ (σ : Signs m) (fh : ι),
  ((∑ i : Fin m, (σ i : ℝ) * ((F fh) (S i) - chainApprox c_pos h fh n (S i))) ≤ (m : ℝ) * (ej c n)) := by
  intro σ fh
  unfold ej
  apply le_trans (signed_sum_le_empiricalDist (F fh) (chainApprox c_pos h fh n) σ)
  apply mul_le_mul_of_nonneg_left _ (by simp)
  exact empiricalDist_to_chainApprox_le_ej c_pos h fh n cs
  -- Part B (uses Massart's finite-class bound)
  -- We compare increments via the paired class:
  -- {(p_j(f), p_{j-1}(f)) | f ∈ F}.
private noncomputable def incrementSet (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := {chainApprox c_pos h fh (j + 1) - chainApprox c_pos h fh j | fh : ι}

private noncomputable def incrementPairSet (c_pos : 0 < c) (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := {(chainApprox c_pos h fh (j + 1), chainApprox c_pos h fh j) | fh : ι}

private lemma finite_chainApprox_image (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  {chainApprox c_pos h' fh j | fh : ι}.Finite := by
  dsimp [chainApprox]
  by_cases h : (j : ℕ) = 0
  · rw [h]
    simp
  · simp [h]
    dsimp [coverApprox]
    have finite_F_image : {F f.index | f ∈ cj c_pos h' (j : ℕ)}.Finite := by
      have : (SetLike.coe (cj c_pos h' (j : ℕ))).Finite := Finset.finite_toSet _
      exact this.image (fun f => F f.index)
    apply finite_F_image.subset
    intro p hp
    simp at hp
    obtain ⟨r, hpr⟩ := hp
    simp
    use choose (exists_cover_approximation c_pos h' r (j : ℕ))
    constructor
    · rcases Classical.choose_spec (exists_cover_approximation c_pos h' r (j : ℕ)) with ⟨hmem, hle⟩
      exact hmem
    · exact hpr

private noncomputable def nextApproxSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :=
  {chainApprox c_pos h' fh (j + 1) | fh : ι}

private noncomputable def currApproxSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :=
  {chainApprox c_pos h' fh j | fh : ι}

private noncomputable def approxPairSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :=
  (nextApproxSet c_pos h' n j) ×ˢ (currApproxSet c_pos h' n j)

private lemma finite_nextApproxSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (nextApproxSet c_pos h' n j).Finite := finite_chainApprox_image c_pos h' (n+1) ⟨j + 1, by simp⟩

private lemma finite_currApproxSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (currApproxSet c_pos h' n j).Finite := finite_chainApprox_image c_pos h' n j

private lemma finite_approxPairSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  ((nextApproxSet c_pos h' n j) ×ˢ (currApproxSet c_pos h' n j)).Finite := (finite_nextApproxSet c_pos h' n j).prod (finite_currApproxSet c_pos h' n j)

omit [Nonempty ι] in
private lemma incrementPairSet_subset_approxPairSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
    (incrementPairSet c_pos h' n j) ⊆ (approxPairSet c_pos h' n j) := by
  intro f hf
  obtain ⟨f0, hg⟩ := hf
  rw [<- hg]
  refine Set.mk_mem_prod (by use f0) (by use f0)

private lemma finite_incrementPairSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (incrementPairSet c_pos h' n j).Finite := by
  unfold incrementPairSet
  refine (finite_approxPairSet c_pos h' n j).subset ?_
  apply incrementPairSet_subset_approxPairSet

private lemma finite_incrementSet (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (incrementSet c_pos h' n j).Finite := by
  unfold incrementSet
  let f : (Z → ℝ) × (Z → ℝ) → (Z → ℝ) := fun p => p.1 - p.2
  have : {chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j | fh : ι} = f '' incrementPairSet c_pos h' n j := by
    ext x
    simp [incrementPairSet]
    constructor
    · rintro ⟨fh, rfl⟩
      use fh
    · rintro ⟨w', hw⟩
      use w'
  rw [this]
  exact (finite_incrementPairSet c_pos h' n j).image f

private noncomputable def nextApproxFinset (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (finite_nextApproxSet c_pos h' n j)

private noncomputable def currApproxFinset (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (finite_currApproxSet c_pos h' n j)

private noncomputable def incrementFinset (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (finite_incrementSet c_pos h' n j)

private noncomputable def incrementPairFinset (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (finite_incrementPairSet c_pos h' n j)

private noncomputable def approxPairFinset (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)
  := Set.Finite.toFinset (finite_approxPairSet c_pos h' n j)

private lemma incrementFinset_nonempty (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (incrementFinset c_pos h' n j).Nonempty := by
  dsimp [incrementFinset]
  simp only [Set.Finite.toFinset_nonempty]
  exact ⟨_, ⟨Classical.arbitrary ι, rfl⟩⟩

private lemma incrementPairFinset_nonempty (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (incrementPairFinset c_pos h' n j).Nonempty := by
  dsimp [incrementPairFinset]
  simp only [Set.Finite.toFinset_nonempty]
  exact ⟨_, ⟨Classical.arbitrary ι, rfl⟩⟩

private lemma incrementFinset_card_le_incrementPairFinset_card (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (incrementFinset c_pos h' n j).card ≤ (incrementPairFinset c_pos h' n j).card := by
  unfold incrementFinset incrementPairFinset
  let f : (Z → ℝ) × (Z → ℝ) → (Z → ℝ) := fun p => p.1 - p.2
  apply Finset.card_le_card_of_surjOn f
  dsimp [Set.SurjOn]
  intro e es
  simp at es
  simp
  rcases es with ⟨fh, rfl⟩
  refine ⟨_, _, ?_, rfl⟩
  exact ⟨fh, rfl⟩

private lemma incrementPairFinset_card_le_approxPairFinset_card (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
    (incrementPairFinset c_pos h' n j).card ≤ (approxPairFinset c_pos h' n j).card := by
  unfold incrementPairFinset approxPairFinset
  refine Finset.card_le_card ?_
  refine Set.Finite.toFinset_subset_toFinset.mpr ?_
  apply incrementPairSet_subset_approxPairSet

private lemma approxPairFinset_card_eq_product (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (approxPairFinset c_pos h' n j).card = (nextApproxFinset c_pos h' n j).card * (currApproxFinset c_pos h' n j).card := by
  rw [<- Finset.card_product]
  refine Finset.card_eq_of_equiv ?_
  simp
  dsimp [nextApproxFinset, approxPairFinset, currApproxFinset]
  simp
  exact Equiv.refl _

private lemma nextApproxFinset_card_le_cover_card (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) :
  (nextApproxFinset c_pos h' n j).card ≤ (cj c_pos h' ((j : ℕ) + 1)).card := by
  -- expand `nextApproxFinset`: it is the finset of functions of the form `chainApprox c_pos h' fh (j+1)`
  -- coming from the cover at scale `j+1`.
  dsimp [nextApproxFinset]
  classical
  -- image of the cover under coercion to functions
  -- coerce elements of the cover to functions before taking the image
  let T : Finset (Z → ℝ) := (cj c_pos h' ((j : ℕ) + 1)).image (fun q : EmpiricalFunctionSpace F S => (q : Z → ℝ))
  -- every element of `nextApproxFinset` comes from this image via `coverApprox_mem_cover`
  have hsubset : Set.Finite.toFinset (finite_nextApproxSet c_pos h' n j) ⊆ T := by
    intro x hx
    have hxA : x ∈ nextApproxSet c_pos h' n j := by
      simpa [nextApproxFinset] using hx
    rcases hxA with ⟨fh, rfl⟩
    -- rewrite chainApprox at successor
    have hG : chainApprox c_pos h' fh ((j : ℕ) + 1) = (coverApprox c_pos h' fh ((j : ℕ) + 1) : Z → ℝ) := by
      simp [chainApprox_succ]
    -- show the corresponding `coverApprox` lies in the cover
    have hmem : coverApprox c_pos h' fh ((j : ℕ) + 1) ∈ cj c_pos h' ((j : ℕ) + 1) := by
      apply coverApprox_mem_cover
    -- build membership in the image finset
    -- membership in the image finset
    have hQmem : (coverApprox c_pos h' fh ((j : ℕ) + 1) : Z → ℝ) ∈ T := by
      -- unfold `T` and register the element explicitly
      dsimp [T]
      refine Finset.mem_image.mpr ?_
      refine ⟨coverApprox c_pos h' fh ((j : ℕ) + 1), hmem, rfl⟩
    simpa [hG] using hQmem
  have hcard_le_T : (Set.Finite.toFinset (finite_nextApproxSet c_pos h' n j)).card ≤ T.card := by
    exact Finset.card_le_card hsubset
  have hT_le : T.card ≤ (cj c_pos h' ((j : ℕ) + 1)).card := Finset.card_image_le
  exact hcard_le_T.trans hT_le

private lemma currApproxFinset_card_le_cover_card (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n)  (n_pos : 0 < n) :
  (currApproxFinset c_pos h' n j).card ≤ (cj c_pos h' (j : ℕ)).card := by
  -- expand `currApproxFinset`: functions of the form `chainApprox … fh j` live in the cover at scale `j`
  dsimp [currApproxFinset]
  classical
  -- image of the cover under coercion to functions
  let T : Finset (Z → ℝ) := (cj c_pos h' ((j : ℕ))).image (fun q : EmpiricalFunctionSpace F S => (q : Z → ℝ))
  -- every element of `currApproxFinset` comes from this image via `coverApprox_mem_cover`, with a small case split on `(j : ℕ) = 0`
  by_cases hzero : ((j : ℕ)) = 0
  · -- when j = 0, chainApprox = 0 so currApproxFinset has card 1 ≤ card of the cover (nonempty via coverApprox_mem_cover)
    rw [hzero]
    -- currApproxFinset card is 1
    have hKB : (currApproxFinset c_pos h' n ⟨0, by
      -- j.isLt : ((j : ℕ)) < n; with hzero we get 0 < n
      have := j.isLt
      simpa [hzero] using this⟩).card = 1 := by
      -- currApproxSet is {0}, so its toFinset has one element
      simp [currApproxFinset, currApproxSet, chainApprox]
    -- cover at scale 0 is nonempty: use any fh
    classical
    obtain ⟨fh0⟩ := (inferInstance : Nonempty ι)
    have hcov : (cj c_pos h' 0).Nonempty := by
      exact ⟨coverApprox c_pos h' fh0 0, coverApprox_mem_cover c_pos h' fh0 0⟩
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
    have hBcard : (Set.Finite.toFinset (finite_currApproxSet c_pos h' n ⟨0, n_pos⟩)).card = 1 := by
      -- currApproxFinset is exactly this toFinset
      simpa [currApproxFinset] using hKB
    have : (Set.Finite.toFinset (finite_currApproxSet c_pos h' n ⟨0, n_pos⟩)).card ≤ (cj c_pos h' 0).card := by
      -- rewrite the left card to 1 and use the cover-card lower bound
      simpa [hBcard] using hcover_card
    exact this
  · -- j ≠ 0: use chainApprox_succ and coverApprox_mem_cover to build the subset/image argument
    have hsubset : Set.Finite.toFinset (finite_currApproxSet c_pos h' n j) ⊆ T := by
      intro x hx
      have hxB : x ∈ currApproxSet c_pos h' n j := by simpa [currApproxFinset] using hx
      rcases hxB with ⟨fh, rfl⟩
      have hG : chainApprox c_pos h' fh ((j : ℕ)) = (coverApprox c_pos h' fh ((j : ℕ)) : Z → ℝ) := by
        have : ∃ k, (j : ℕ) = k + 1 := Nat.exists_eq_succ_of_ne_zero hzero
        rcases this with ⟨k, hk⟩
        rw [hk]
        simp [chainApprox_succ]
      have hmem : coverApprox c_pos h' fh ((j : ℕ)) ∈ cj c_pos h' ((j : ℕ)) := coverApprox_mem_cover c_pos h' fh ((j : ℕ))
      have hQmem : (coverApprox c_pos h' fh ((j : ℕ)) : Z → ℝ) ∈ T := by
        dsimp [T]
        refine Finset.mem_image.mpr ?_
        exact ⟨coverApprox c_pos h' fh ((j : ℕ)), hmem, rfl⟩
      simpa [hG] using hQmem
    have hcard_le_T : (Set.Finite.toFinset (finite_currApproxSet c_pos h' n j)).card ≤ T.card := by
      exact Finset.card_le_card hsubset
    have hT_le : T.card ≤ (cj c_pos h' ((j : ℕ))).card := Finset.card_image_le
    exact hcard_le_T.trans hT_le

private lemma incrementPairFinset_card_le_cover_product_card (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) (n_pos : 0 < n):
  (incrementPairFinset c_pos h' n j).card ≤ (cj c_pos h' (j+1)).card * (cj c_pos h' j).card := by
  calc
  _ ≤ (approxPairFinset c_pos h' n j).card := by
    apply incrementPairFinset_card_le_approxPairFinset_card
  _ = (nextApproxFinset c_pos h' n j).card * (currApproxFinset c_pos h' n j).card := by
    apply approxPairFinset_card_eq_product
  _ ≤ _ := by
    apply mul_le_mul
    apply nextApproxFinset_card_le_cover_card
    apply currApproxFinset_card_le_cover_card
    exact n_pos
    simp
    simp

omit [Nonempty ι] in
private lemma chainApprox_increment_signed_sum_bound (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (j : ℕ)
  (σ : Signs m) (fh : ι) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ∑ i : Fin m, (σ i : ℝ) * (chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j) (S i) ≤ m * (c / 2 ^ (j+1) + c / 2 ^ j) := by
  calc
  _ ≤ m * empiricalDist S (chainApprox c_pos h' fh (j + 1)) (chainApprox c_pos h' fh j) := by
    apply signed_sum_le_empiricalDist (chainApprox c_pos h' fh (j + 1)) (chainApprox c_pos h' fh j) σ
  _ ≤ _ := by
    apply mul_le_mul_of_nonneg_left _ (by simp)
    calc
    _ ≤ empiricalDist S (chainApprox c_pos h' fh (j + 1)) (F fh) + empiricalDist S (F fh) (chainApprox c_pos h' fh j) := by
      apply @dist_triangle _ (empiricalPMet S) (chainApprox c_pos h' fh (j + 1)) (F fh) (chainApprox c_pos h' fh j)
    _ ≤ _ := by
      rw [←empiricalDist_comm S (F fh) (chainApprox c_pos h' fh (j+1))]
      apply add_le_add
      · exact empiricalDist_to_chainApprox_le_ej c_pos h' fh (j+1) cs
      · exact empiricalDist_to_chainApprox_le_ej c_pos h' fh j cs

private lemma massart_bound_for_increment_term (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (j : Fin n) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((chainApprox c_pos h' fh (j+1) - chainApprox c_pos h' fh j) (S i))))
  ≤ ((incrementFinset c_pos h' n j).sup' (incrementFinset_nonempty c_pos h' n j) fun j ↦ √(∑ i, (|j (S i)|) ^ 2)) * (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card))) / m := by
  let C := ((incrementFinset c_pos h' n j).sup' (incrementFinset_nonempty c_pos h' n j) fun j ↦ √(∑ i, (|j (S i)|) ^ 2))
  calc
  _ = ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ (fh : {x // x ∈ incrementFinset c_pos h' n j}),
    (∑ i : Fin m, (σ i : ℝ) * (fh.val (S i)))) := by
    congr
    ext σ
    apply le_antisymm
    · apply ciSup_le
      intro fh
      let hfh : {x // x ∈ incrementFinset c_pos h' n j} := by
        use chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j
        dsimp [incrementFinset, incrementSet]
        simp
      convert le_ciSup _ hfh
      · congr
      · use m * (c / 2 ^ (j.1 + 1) + c / 2 ^ j.1)
        rintro x ⟨⟨g, hg'⟩, hg⟩
        rw [<-hg]
        dsimp [incrementFinset] at hg'
        simp at hg'
        obtain ⟨fh, hfh⟩ := hg'
        simp
        rw [<-hfh]
        exact chainApprox_increment_signed_sum_bound c_pos h' j.1 σ fh cs
    · have : Nonempty {x // x ∈ incrementFinset c_pos h' n j} := by
        obtain ⟨fh⟩ := (by assumption : Nonempty ι)
        use chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j
        dsimp [incrementFinset, finite_incrementSet, incrementSet]
        simp
      apply ciSup_le
      rintro ⟨g, hg⟩
      dsimp [incrementFinset] at hg
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
        exact chainApprox_increment_signed_sum_bound c_pos h' j.1 σ fh cs
  _ = signs_card_inv m * ∑ σ : Signs m, ⨆ (fh : {x // x ∈ incrementFinset c_pos h' n j}),
    ((m : ℝ)⁻¹ * ∑ i : Fin m, (σ i : ℝ) * (fh.val (S i))) := by
    rw [mul_comm (m : ℝ)⁻¹ _, mul_assoc]
    congr
    rw [Finset.mul_sum]
    congr
    ext σ
    apply Real.mul_iSup_of_nonneg
    apply inv_nonneg_of_nonneg
    exact Nat.cast_nonneg' m
  _ = empiricalRademacherComplexity_pmf_without_abs m (F_on (ι:=(Z → ℝ)) (Z:=Z) (fun hk : Z → ℝ => hk) (incrementFinset c_pos h' n j)) S := by
    simp only [empiricalRademacherComplexity_pmf_without_abs, signVecPMF,
      Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, Finset.mul_sum,
      PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, smul_eq_mul, signs_card_inv]
    rfl
  _ ≤ C * (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card))) / m := by
    apply le_of_le_of_eq
    · apply massart_lemma_pmf
      · exact incrementFinset_nonempty c_pos h' n j
      · exact m_pos
      · change ∀ i ∈ incrementFinset c_pos h' n j, ∀ (j : Fin m), |i (S j)| ≤ C
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
    · have : √(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card)) = √(2 * Real.log ↑(incrementFinset c_pos h' n j).card) := by
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
      positivity

private lemma partB_sum_bound_via_massart (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (n_pos : 0 < n):
  ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((chainApprox c_pos h' fh (j+1) - chainApprox c_pos h' fh j) (S i)))) ≤
  ∑ j : Fin n, (Finset.sup' (incrementPairFinset c_pos h' n j) (incrementPairFinset_nonempty c_pos h' n j) fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) * (√(2 * Real.log (coveringNumber h' (ej c (j+1)) * coveringNumber h' (ej c j)))) / ↑m := by
  -- It suffices to prove the bound term-by-term in the finite sum over j.
  apply Finset.sum_le_sum
  intro j hj
  -- Replace the supremum over f with a finite supremum over the paired class.
  calc
  _ ≤ ((incrementFinset c_pos h' n j).sup' (incrementFinset_nonempty c_pos h' n j) fun j ↦ √(∑ i, (|j (S i)|) ^ 2)) * (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card))) / m := massart_bound_for_increment_term c_pos h' n j m_pos cs
  _ ≤ ((Finset.sup' (incrementPairFinset c_pos h' n j) (incrementPairFinset_nonempty c_pos h' n j) fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i) ) ^ 2)) * (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card)))) / m := by
    apply div_le_div_of_nonneg_right _ _
    apply mul_le_mul_of_nonneg_right _ _
    apply Finset.sup'_le _ _
    intro hk hk0
    simp only [Set.Finite.mem_toFinset, incrementFinset] at hk0
    obtain ⟨fh, hfh⟩ := hk0
    rw [<- hfh]
    have : √(∑ i, |(chainApprox c_pos h' fh ((j : ℕ) + 1) - chainApprox c_pos h' fh (j : ℕ)) (S i)| ^ 2) = √(∑ i : Fin m, ((chainApprox c_pos h' fh ((j : ℕ) + 1) - chainApprox c_pos h' fh (j : ℕ)) (S i)) ^ 2) := by
      congr
      ext i
      exact sq_abs _
    rw [this]
    have : ⟨chainApprox c_pos h' fh ((j : ℕ) + 1), chainApprox c_pos h' fh (j : ℕ)⟩ ∈ incrementPairFinset c_pos h' n j := by
      simp only [Set.Finite.mem_toFinset, incrementPairFinset, incrementPairSet]
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
        · simp; exact (Set.Finite.toFinset_nonempty (finite_incrementSet c_pos h' n j)).mp (incrementFinset_nonempty c_pos h' n j)
        · norm_cast
          apply (incrementFinset_card_le_incrementPairFinset_card c_pos h' n j).trans
          refine (incrementPairFinset_card_le_cover_product_card c_pos h' n j n_pos).trans_eq ?_
          rw [coveringFinset_card, coveringFinset_card]
      · obtain ⟨fh⟩ := (by assumption : Nonempty ι)
        have hem : ⟨chainApprox c_pos h' fh (j + 1), chainApprox c_pos h' fh j⟩ ∈ incrementPairFinset c_pos h' n j := by
          simp only [Set.Finite.mem_toFinset, incrementPairFinset, incrementPairSet]
          use fh
        apply le_trans _ (Finset.le_sup' _ hem)
        apply Real.sqrt_nonneg
    · simp

private lemma partB_bound (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) * ((chainApprox c_pos h' fh (j+1) - chainApprox c_pos h' fh j) (S i)))) ≤
    ∑ j : Fin n, 6 * (ej c (j+1) - ej c (j+2)) * (√(4 * Real.log (coveringNumber h' (ej c (j+1))))/((Real.sqrt m))) := by
  calc
  _ ≤ ∑ j : Fin n, (Finset.sup' (incrementPairFinset c_pos h' n j) (incrementPairFinset_nonempty c_pos h' n j) fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) * (√(2 * Real.log (coveringNumber h' (ej c (j+1)) * coveringNumber h' (ej c j)))) / ↑m := by
    by_cases n_pos : 0 < n
    · exact partB_sum_bound_via_massart c_pos h' n m_pos cs n_pos
    · simp at n_pos
      rw [n_pos]
      simp
  _ = ∑ j : Fin n, (Finset.sup' (incrementPairFinset c_pos h' n j) (incrementPairFinset_nonempty c_pos h' n j) fun hk ↦ (√(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) / ↑m) * (√(2 * Real.log (coveringNumber h' (ej c (j+1)) * coveringNumber h' (ej c j)))) := by
    apply congrArg
    ext j
    rw [<- div_mul_eq_mul_div]
    rw [Mathlib.Tactic.LinearCombination.mul_eq_const]
    rw [Finset.sup'_div₀]
    norm_cast
    positivity
  _ ≤ ∑ j : Fin n, ((6 * (ej c (j+1) - ej c (j+2))/ Real.sqrt m) * (√(2 * Real.log ((coveringNumber h' (ej c (j+1))) * (coveringNumber h' (ej c j)))))) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    apply mul_le_mul_of_nonneg_right
      -- The remaining estimate follows from the pair-class representation.
    · have r0 (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ incrementPairFinset c_pos h' n j) : ∃ fh, (chainApprox c_pos h' fh (j + 1), chainApprox c_pos h' fh j) = hk := by
        dsimp [incrementPairFinset] at hk0
        simp at hk0
        dsimp [incrementPairSet] at hk0
        exact hk0
      have fh (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ incrementPairFinset c_pos h' n j) : ι :=
        Classical.choose (r0 hk hk0)
      suffices ∀ (hk : (Z → ℝ) × (Z → ℝ)) (hk0 : hk ∈ incrementPairFinset c_pos h' n j), (√(∑ i, ((hk.1 - hk.2) (S i)) ^ 2)) / ↑m ≤ 6 * (ej c ((j : ℕ) + 1) - ej c ((j : ℕ) + 2)) / Real.sqrt m from by
        rw [Finset.sup'_le_iff]
        exact this
      intro hk hk0
      have hk1 : hk ∈ incrementPairSet c_pos h' n j := by dsimp [incrementPairFinset] at hk0; simp at hk0; exact hk0
      dsimp [incrementPairSet] at hk1
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
        -- Equivalent dyadic-expression rewrite used in the integral comparison step.
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
        have gh : hk.1 = chainApprox c_pos h' x ((j : ℕ) + 1) := by rw [<- fhx]
        rw [gh]
        have : √(∑ i, (chainApprox c_pos h' x ((j : ℕ) + 1) - F x) (S i) ^ 2 / ↑m) = empiricalDist S (F x) (chainApprox c_pos h' x ((j : ℕ) + 1)) := by
          rw [empiricalDist_comm]
          dsimp [empiricalDist, empiricalNorm]
          apply congrArg
          simp [div_eq_mul_inv, mul_comm]
          exact
            Eq.symm
              (Finset.mul_sum Finset.univ (fun i ↦ (chainApprox c_pos h' x (↑j + 1) (S i) - F x (S i)) ^ 2)
                (↑m)⁻¹)
        rw [this]
        dsimp only [ej]
        exact empiricalDist_to_chainApprox_le_ej c_pos h' x ((j : ℕ) + 1) cs
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

        have gh : hk.2 = chainApprox c_pos h' x j := by rw [<- fhx]
        rw [gh]
        have : √(∑ i, (chainApprox c_pos h' x j - F x) (S i) ^ 2 / ↑m) = empiricalDist S (F x) (chainApprox c_pos h' x j) := by
          rw [empiricalDist_comm]
          dsimp [empiricalDist, empiricalNorm]
          apply congrArg
          simp [div_eq_mul_inv, mul_comm]
          exact
            Eq.symm
              (Finset.mul_sum Finset.univ (fun i ↦ (chainApprox c_pos h' x (↑j) (S i) - F x (S i)) ^ 2)
                (↑m)⁻¹)
        rw [this]
        dsimp only [ej]
        exact empiricalDist_to_chainApprox_le_ej c_pos h' x j cs
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
          apply coveringNumber_antitone
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
  -- Convert the Part A/Part B bound into the final finite-sum expression.
private lemma combine_partA_partB (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalRademacherComplexity_without_abs m F S ≤ (ej c n) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber h' (ej c (j+1)))))) := by
  apply le_trans (split_main_and_increment_terms cs h' n)
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
          apply partA_sup_bound c_pos h' cs
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
    · exact partB_bound c_pos h' n m_pos cs
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

private lemma ej_antitone (c_nonneg : 0 ≤ c) : Antitone (fun n : ℕ ↦ ej c n) := by
  dsimp [ej]
  refine Antitone.const_mul ?_ ?_
  refine inv_pow_anti ?_
  norm_num
  exact c_nonneg

private lemma entropy_sum_to_integral_bound (c_pos : 0 < c) (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  empiricalRademacherComplexity_without_abs m F S ≤ 2 * (ej c (n+1)) + 12 / (Real.sqrt m)*(∫ (x : ℝ) in (ej c (n+1))..(c/2),√(Real.log (coveringNumber h' x))) := by
  calc
  _ ≤ (ej c n) + 12 / (Real.sqrt m)*(∑ j : Fin n, ((ej c (j+1) - ej c (j+2))*√(Real.log (coveringNumber h' (ej c (j+1)))))) := combine_partA_partB c_pos h' n m_pos cs
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
    apply AntitoneOn.leftRiemann_sum_le_integral
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
      apply coveringNumber_antitone
      simp
      simp at ha
      linarith
      simp
      simp at hb
      linarith
      apply le_of_lt hab

omit [Nonempty ι] in
private lemma choose_dyadic_scale_for_epsilon (ε : ℝ) (ε_pos : 0 < ε) (c_ε : ε < c / 2) :
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
      rcases Nat.eq_zero_or_pos m0 with hm0 | hm0
      · subst hm0
        simp only [Nat.cast_zero, zero_add, Real.rpow_one] at hm2
        linarith
      · exact hm0
    have p0 : ε < c / 2 ^ (↑m0) := by
      have htmp := mul_lt_mul_of_pos_right hm1 ε_pos
      have htmp_mul : ε * 2 ^ (↑m0) < c := by
        field_simp at htmp
        simp at htmp
        rw [mul_comm]
        exact htmp
      have hpowpos : 0 < (2 : ℝ) ^ (↑m0) := pow_pos (by norm_num) _
      have := mul_lt_mul_of_pos_right htmp_mul (inv_pos.mpr hpowpos)
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
  obtain ⟨n, ⟨nw1, nw2⟩⟩ := choose_dyadic_scale_for_epsilon ε ε_pos ε_le_c_div_2
  have ε_c : ε ≤ c := by linarith
  have c_pos : 0 < c := lt_of_le_of_lt' ε_c ε_pos
  apply le_trans (entropy_sum_to_integral_bound c_pos h' n m_pos cs)
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
          apply coveringNumber_antitone
          · simp
            linarith
          · simp
            linarith
          · exact le_of_lt hab
    · refine div_nonneg ?_ ?_
      · simp
      · norm_cast
        simp

omit [Nonempty ι] in
private lemma abs_apply_le_mul_sqrt_of_empiricalNorm_le
    (m_pos : 0 < m) (cs : ∀ i : ι, empiricalNorm S (F i) ≤ c)
    (i : ι) (j : Fin m) :
    |F i (S j)| ≤ c * Real.sqrt m := by
  have hsqrt : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr m_pos)
  have hdiv : |F i (S j)| / Real.sqrt m ≤ c :=
    (empiricalDist_proj S (F i) j).trans (cs i)
  exact (div_le_iff₀ hsqrt).mp hdiv

/--
Absolute empirical Rademacher complexity satisfies Dudley's entropy-integral
estimate after adjoining the pointwise negatives of the class.
-/
theorem dudley_entropy_integral_abs {ε : ℝ} (ε_pos : 0 < ε)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
    (ε_le_c_div_2 : ε < c / 2) :
    empiricalRademacherComplexity m F S ≤
      (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c / 2),
          √(Real.log (coveringNumber
            (signSymmetrization_totallyBounded (F := F) (S := S) h') x)))) := by
  have c_pos : 0 < c := by linarith
  have hsample : ∀ i j, |F i (S j)| ≤ c * Real.sqrt m :=
    abs_apply_le_mul_sqrt_of_empiricalNorm_le m_pos cs
  rw [empiricalRademacherComplexity_eq_without_abs_signSymmetrization
    m F S (c * Real.sqrt m)
    (mul_nonneg (le_of_lt c_pos) (Real.sqrt_nonneg _)) hsample]
  apply dudley_entropy_integral'
    (F := signSymmetrization F)
    (h' := signSymmetrization_totallyBounded (F := F) (S := S) h')
    ε_pos m_pos
  · rintro ⟨i, b⟩
    cases b
    · change empiricalNorm S (-F i) ≤ c
      simpa using cs i
    · change empiricalNorm S (F i) ≤ c
      exact cs i
  · exact ε_le_c_div_2

/--
For a class closed under pointwise negation, Dudley's original covering
numbers already estimate the absolute empirical Rademacher complexity.
-/
theorem dudley_entropy_integral_abs_of_neg_closed {ε : ℝ}
    (ε_pos : 0 < ε)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (m_pos : 0 < m) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c)
    (ε_le_c_div_2 : ε < c / 2) (hneg : IsNegClosed F) :
    empiricalRademacherComplexity m F S ≤
      (4 * ε + (12 / Real.sqrt m) *
        (∫ (x : ℝ) in ε..(c / 2),
          √(Real.log (coveringNumber h' x)))) := by
  have c_pos : 0 < c := by linarith
  have hsample : ∀ i j, |F i (S j)| ≤ c * Real.sqrt m :=
    abs_apply_le_mul_sqrt_of_empiricalNorm_le m_pos cs
  rw [empiricalRademacherComplexity_eq_without_abs_of_neg_closed
    m F S (c * Real.sqrt m)
    (mul_nonneg (le_of_lt c_pos) (Real.sqrt_nonneg _)) hsample hneg]
  exact dudley_entropy_integral' ε_pos h' m_pos cs ε_le_c_div_2
