import FoML.Entropy.Dudley
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Explicit entropy bounds for one-dimensional Lipschitz families

This module covers the parameter interval `[-W,W]` by an equally spaced grid.
If the represented functions are `L`-Lipschitz in the parameter with respect
to empirical distance, the grid yields

`N(F, ε) ≤ ceil (2 W L / ε) + 1`.
-/

noncomputable section

universe u

open MeasureTheory Real

variable {n : ℕ} {𝒳 : Type u}

/--
An equally spaced grid in `[-W,W]`, with the final point clamped at `W`.
-/
private noncomputable def intervalGrid
    (W ρ : ℝ) (hW : 0 ≤ W) (hρ : 0 < ρ) :
    Finset (Set.Icc (-W) W) := by
  classical
  exact (Finset.range (Nat.ceil (2 * W / ρ) + 1)).image fun (j : ℕ) ↦
    ⟨min W (-W + (j : ℝ) * ρ), by
      constructor
      · apply le_min
        · linarith
        · have : 0 ≤ (j : ℝ) * ρ :=
            mul_nonneg (Nat.cast_nonneg j) hρ.le
          linarith
      · exact min_le_left _ _⟩

private lemma intervalGrid_card_le
    (W ρ : ℝ) (hW : 0 ≤ W) (hρ : 0 < ρ) :
    (intervalGrid W ρ hW hρ).card ≤ Nat.ceil (2 * W / ρ) + 1 := by
  classical
  simpa only [intervalGrid, Finset.card_range] using
    (Finset.card_image_le :
      ((Finset.range (Nat.ceil (2 * W / ρ) + 1)).image
        (fun (j : ℕ) ↦
          (⟨min W (-W + (j : ℝ) * ρ), by
            constructor
            · apply le_min
              · linarith
              · have : 0 ≤ (j : ℝ) * ρ :=
                  mul_nonneg (Nat.cast_nonneg j) hρ.le
                linarith
            · exact min_le_left _ _⟩ :
            Set.Icc (-W) W))).card ≤
        (Finset.range (Nat.ceil (2 * W / ρ) + 1)).card)

/--
Every point of `[-W,W]` lies strictly within `ρ` of a grid point.
-/
private lemma intervalGrid_cover
    (W ρ : ℝ) (hW : 0 ≤ W) (hρ : 0 < ρ) :
    (Set.univ : Set (Set.Icc (-W) W)) ⊆
      ⋃ y ∈ intervalGrid W ρ hW hρ, Metric.ball y ρ := by
  classical
  intro t _
  let q : ℝ := (t.1 + W) / ρ
  let j : ℕ := Nat.ceil q
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact div_nonneg (by linarith [t.2.1]) hρ.le
  have hqtop : q ≤ 2 * W / ρ := by
    dsimp only [q]
    exact (div_le_div_iff_of_pos_right hρ).2 (by linarith [t.2.2])
  have hjle : j ≤ Nat.ceil (2 * W / ρ) := by
    exact Nat.ceil_mono hqtop
  have hjmem : j ∈ Finset.range (Nat.ceil (2 * W / ρ) + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le hjle)
  let y : Set.Icc (-W) W :=
    ⟨min W (-W + (j : ℝ) * ρ), by
      constructor
      · apply le_min
        · linarith
        · have : 0 ≤ (j : ℝ) * ρ :=
            mul_nonneg (Nat.cast_nonneg j) hρ.le
          linarith
      · exact min_le_left _ _⟩
  have hymem : y ∈ intervalGrid W ρ hW hρ := by
    exact Finset.mem_image.2 ⟨j, hjmem, rfl⟩
  have hqceil : q ≤ (j : ℝ) := Nat.le_ceil q
  have ht_raw : t.1 ≤ -W + (j : ℝ) * ρ := by
    change (t.1 + W) / ρ ≤ (j : ℝ) at hqceil
    have := (div_le_iff₀ hρ).1 hqceil
    linarith
  have hceil : (j : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0
  have hraw_lt : -W + (j : ℝ) * ρ < t.1 + ρ := by
    have hrewrite : q + 1 = (t.1 + W + ρ) / ρ := by
      dsimp only [q]
      field_simp [hρ.ne']
    rw [hrewrite] at hceil
    have hmul := (lt_div_iff₀ hρ).1 hceil
    linarith
  have ht_y : t.1 ≤ y.1 := by
    dsimp only [y]
    exact le_min t.2.2 ht_raw
  have hy_lt : y.1 < t.1 + ρ := by
    dsimp only [y]
    exact (min_le_right _ _).trans_lt hraw_lt
  simp only [Set.mem_iUnion]
  refine ⟨y, ⟨hymem, ?_⟩⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.2 ht_y)]
  linarith

/--
Pointwise parameter Lipschitzness implies empirical-distance Lipschitzness.
-/
theorem empiricalDist_le_mul_abs_parameter_sub
    (hn : 0 < n) {W L : ℝ} (hL : 0 ≤ L)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (S : Fin n → 𝒳) (t s : Set.Icc (-W) W) :
    empiricalDist S (F t) (F s) ≤ L * |t.1 - s.1| := by
  apply empiricalDist_le_of_abs_sub_le hn S (F t) (F s)
    (mul_nonneg hL (abs_nonneg _))
  intro k
  exact hF t s (S k)

/--
The empirical function space of a Lipschitz family on `[-W,W]` is totally
bounded.  The proof uses compactness of the parameter interval.
-/
theorem lipschitzParameter_empiricalFunctionSpace_totallyBounded
    (hn : 0 < n) {W L : ℝ} (hL : 0 ≤ L)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (S : Fin n → 𝒳) :
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace F S)) := by
  let q : Set.Icc (-W) W → EmpiricalFunctionSpace F S := fun t ↦ ⟨t⟩
  have hq : LipschitzWith ⟨L, hL⟩ q := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    change empiricalDist S (F t) (F s) ≤ L * dist t s
    rw [Subtype.dist_eq, Real.dist_eq]
    exact empiricalDist_le_mul_abs_parameter_sub hn hL F hF S t s
  letI : CompactSpace (Set.Icc (-W) W) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hcompact : IsCompact (Set.range q) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hq.continuous
  have hrange :
      Set.range q = (Set.univ : Set (EmpiricalFunctionSpace F S)) := by
    apply Set.eq_univ_of_forall
    intro f
    exact ⟨f.index, by cases f; rfl⟩
  rw [hrange] at hcompact
  exact hcompact.totallyBounded

/--
Explicit covering-number estimate for a one-dimensional Lipschitz family:

`N(F, ε) ≤ ceil (2 W L / ε) + 1`.
-/
theorem coveringNumber_lipschitzParameter_le
    (hn : 0 < n) {W L ε : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hε : 0 < ε)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (S : Fin n → 𝒳) :
    coveringNumber
        (lipschitzParameter_empiricalFunctionSpace_totallyBounded
          hn hL.le F hF S) ε ≤
      Nat.ceil (2 * W * L / ε) + 1 := by
  classical
  let ρ : ℝ := ε / L
  have hρ : 0 < ρ := div_pos hε hL
  let grid : Finset (Set.Icc (-W) W) := intervalGrid W ρ hW hρ
  let centers : Finset (EmpiricalFunctionSpace F S) :=
    grid.image fun t ↦ ⟨t⟩
  have hcenters_card :
      centers.card ≤ Nat.ceil (2 * W * L / ε) + 1 := by
    calc
      centers.card ≤ grid.card := Finset.card_image_le
      _ ≤ Nat.ceil (2 * W / ρ) + 1 :=
        intervalGrid_card_le W ρ hW hρ
      _ = Nat.ceil (2 * W * L / ε) + 1 := by
        congr 2
        dsimp only [ρ]
        field_simp [hL.ne', hε.ne']
  refine (coveringNumber_le_card_of_cover
    (lipschitzParameter_empiricalFunctionSpace_totallyBounded
      hn hL.le F hF S) hε centers ?_).trans hcenters_card
  intro q _
  have hparam :=
    intervalGrid_cover W ρ hW hρ (Set.mem_univ q.index)
  simp only [Set.mem_iUnion] at hparam
  obtain ⟨t, htgrid, htball⟩ := hparam
  let center : EmpiricalFunctionSpace F S := ⟨t⟩
  have hcenter : center ∈ centers := by
    exact Finset.mem_image.2 ⟨t, htgrid, rfl⟩
  simp only [Set.mem_iUnion]
  refine ⟨center, ⟨hcenter, ?_⟩⟩
  rw [Metric.mem_ball]
  change empiricalDist S (F q.index) (F t) < ε
  have hdist : |q.index.1 - t.1| < ρ := by
    simpa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using htball
  calc
    empiricalDist S (F q.index) (F t) ≤
        L * |q.index.1 - t.1| :=
      empiricalDist_le_mul_abs_parameter_sub
        hn hL.le F hF S q.index t
    _ < L * ρ := mul_lt_mul_of_pos_left hdist hL
    _ = ε := by
      dsimp only [ρ]
      field_simp [hL.ne']

/--
An explicit Dudley expression for a one-dimensional Lipschitz family.
-/
noncomputable def lipschitzParameterDudleyEstimate
    (n : ℕ) (W L α c : ℝ) : ℝ :=
  4 * α + (12 / Real.sqrt n) * (c / 2 - α) *
    Real.sqrt
      (Real.log (2 * (Nat.ceil (2 * W * L / α) + 1)))

private lemma lipschitzParameter_entropy_integral_le
    (hn : 0 < n) {W L α c : ℝ}
    (hW : 0 ≤ W) (hL : 0 < L) (hα : 0 < α) (hαc : α < c / 2)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (S : Fin n → 𝒳) :
    let htb :=
      lipschitzParameter_empiricalFunctionSpace_totallyBounded
        hn hL.le F hF S
    (∫ x : ℝ in α..(c / 2),
      Real.sqrt (Real.log (coveringNumber
        (signSymmetrization_totallyBounded
          (F := F) (S := S) htb) x))) ≤
      (c / 2 - α) *
        Real.sqrt
          (Real.log (2 * (Nat.ceil (2 * W * L / α) + 1))) := by
  letI : Nonempty (Set.Icc (-W) W) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  let htb :=
    lipschitzParameter_empiricalFunctionSpace_totallyBounded
      hn hL.le F hF S
  let hstb :=
    signSymmetrization_totallyBounded (F := F) (S := S) htb
  let g : ℝ → ℝ :=
    fun x ↦ Real.sqrt (Real.log (coveringNumber hstb x))
  let C : ℝ :=
    Real.sqrt
      (Real.log (2 * (Nat.ceil (2 * W * L / α) + 1)))
  have hcoverα :
      coveringNumber hstb α ≤
        2 * (Nat.ceil (2 * W * L / α) + 1) := by
    calc
      coveringNumber hstb α ≤ 2 * coveringNumber htb α :=
        coveringNumber_signSymmetrization_le_two_mul htb hα
      _ ≤ 2 * (Nat.ceil (2 * W * L / α) + 1) := by
        gcongr
        exact coveringNumber_lipschitzParameter_le
          hn hW hL hα F hF S
  have hanti : AntitoneOn g (Set.uIcc α (c / 2)) := by
    intro a ha b hb hab
    rw [Set.uIcc_of_lt hαc] at ha hb
    have ha0 : 0 < a := hα.trans_le ha.1
    have hb0 : 0 < b := ha0.trans_le hab
    dsimp only [g]
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log
    · exact_mod_cast coveringNumber_nonzero
        (Set.univ_nonempty :
          (Set.univ :
            Set (EmpiricalFunctionSpace (signSymmetrization F) S)).Nonempty)
        hstb hb0
    · exact_mod_cast coveringNumber_antitone hstb ha0 hb0 hab
  have hg : IntervalIntegrable g MeasureTheory.volume α (c / 2) :=
    hanti.intervalIntegrable
  calc
    (∫ x : ℝ in α..(c / 2),
        Real.sqrt (Real.log (coveringNumber
          (signSymmetrization_totallyBounded
            (F := F) (S := S) htb) x))) =
        ∫ x : ℝ in α..(c / 2), g x := rfl
    _ ≤ ∫ _x : ℝ in α..(c / 2), C := by
      apply intervalIntegral.integral_mono_on
        (le_of_lt hαc) hg intervalIntegrable_const
      intro x hx
      dsimp only [g, C]
      apply Real.sqrt_le_sqrt
      apply Real.log_le_log
      · exact_mod_cast coveringNumber_nonzero
          (Set.univ_nonempty :
            (Set.univ :
              Set (EmpiricalFunctionSpace (signSymmetrization F) S)).Nonempty)
          hstb (hα.trans_le hx.1)
      · exact_mod_cast
          (coveringNumber_antitone hstb hα
            (hα.trans_le hx.1) hx.1).trans hcoverα
    _ = (c / 2 - α) * C := by simp
    _ = (c / 2 - α) *
        Real.sqrt
          (Real.log (2 * (Nat.ceil (2 * W * L / α) + 1))) := rfl

/--
Dudley's estimate for a one-dimensional Lipschitz parameter family, with no
remaining covering number.
-/
theorem empiricalRademacherComplexity_le_lipschitzParameterDudleyEstimate
    (hn : 0 < n) {W L α c : ℝ}
    (hW : 0 ≤ W) (hL : 0 < L) (hα : 0 < α) (hαc : α < c / 2)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (S : Fin n → 𝒳)
    (hNorm : ∀ t, empiricalNorm S (F t) ≤ c) :
    empiricalRademacherComplexity n F S ≤
      lipschitzParameterDudleyEstimate n W L α c := by
  letI : Nonempty (Set.Icc (-W) W) :=
    ⟨⟨0, by constructor <;> linarith⟩⟩
  let htb :=
    lipschitzParameter_empiricalFunctionSpace_totallyBounded
      hn hL.le F hF S
  calc
    empiricalRademacherComplexity n F S ≤
        4 * α + (12 / Real.sqrt n) *
          (∫ x : ℝ in α..(c / 2),
            Real.sqrt (Real.log (coveringNumber
              (signSymmetrization_totallyBounded
                (F := F) (S := S) htb) x))) :=
      dudley_entropy_integral_abs hα htb hn hNorm hαc
    _ ≤ lipschitzParameterDudleyEstimate n W L α c := by
      dsimp only [lipschitzParameterDudleyEstimate]
      rw [show
        (12 / Real.sqrt ↑n) * (c / 2 - α) *
              Real.sqrt
                (Real.log (2 * (↑⌈2 * W * L / α⌉₊ + 1))) =
            (12 / Real.sqrt ↑n) *
              ((c / 2 - α) *
                Real.sqrt
                  (Real.log (2 * (↑⌈2 * W * L / α⌉₊ + 1)))) by ring]
      apply add_le_add
      · rfl
      · apply mul_le_mul_of_nonneg_left
        · exact lipschitzParameter_entropy_integral_le
            hn hW hL hα hαc F hF S
        · exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

end
