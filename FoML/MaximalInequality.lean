import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Independence.Integration
import FoML.Hoeffding
import FoML.Defs

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {ι : Type*} [DecidableEq ι]

private theorem convexon_exp (t : ℝ) : ConvexOn ℝ Set.univ fun x ↦ rexp (t * x) := by
  rw [(by funext; simp : (fun x ↦ rexp (t * x)) = rexp ∘ (fun x ↦ (t * x)))]
  apply ConvexOn.comp
  simp only [Set.image_univ]
  by_cases h : t = 0
  case pos =>
    rw [h]
    simp only [zero_mul, Set.range_const]
    constructor
    intro x hx
    intro y hy a b ha hb hab
    simp only [Set.mem_singleton_iff] at hx
    simp only [Set.mem_singleton_iff] at hy
    simp only [smul_eq_mul, Set.mem_singleton_iff]
    rw [hx, hy]
    simp only [mul_zero, add_zero]
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_singleton_iff] at hx
    simp only [Set.mem_singleton_iff] at hy
    rw [hx, hy]
    simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one]
    rw [hab]
  case neg =>
    suffices (Set.range fun x ↦ t * x) = Set.univ from by
      rw [this]
      exact convexOn_exp
    apply Function.Surjective.range_eq
    exact mul_left_surjective₀ h
  dsimp [ConvexOn]
  constructor
  exact convex_univ
  intro x hx y hy a b ha hb hab
  rw [(by ring : t * (a * x + b * y) = a * (t * x) + b * (t * y))]
  simp only [Set.image_univ]
  intro a ha b hb hab
  exact exp_le_exp.mpr hab

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
theorem integrable_of_subgaussian (X : ι → Ω → ℝ) (j : ι) (r : ℝ)
  (p : ∀ (t : ℝ), ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ ≤ ENNReal.ofReal (rexp (t ^ 2 * r ^ 2 / 2)))
  (q : AEMeasurable (X j) μ) : Integrable (X j) μ := by
  constructor
  exact aestronglyMeasurable_iff_aemeasurable.mpr q
  dsimp [HasFiniteIntegral]
  calc
  _ ≤ ∫⁻ (a : Ω), ENNReal.ofReal (rexp (|X j a|)) ∂μ := by
    apply lintegral_mono
    intro a
    simp only
    rw [enorm_eq_ofReal_abs (X j a)]
    rw [ENNReal.ofReal_le_ofReal_iff]
    exact le_trans (by linarith) (add_one_le_exp |X j a|)
    exact exp_nonneg |X j a|
  _ ≤ ∫⁻ (a : Ω), ENNReal.ofReal (rexp (-(X j a)) + rexp (X j a)) ∂μ := by
    apply lintegral_mono
    intro a
    simp only
    rw [ENNReal.ofReal_le_ofReal_iff]
    by_cases h : 0 ≤ X j a
    case pos =>
      rw [(by simp only [abs_eq_self]; exact h : |X j a| = X j a)]
      linarith [exp_nonneg (-X j a)]
    case neg =>
      rw [(by simp only [abs_eq_neg_self]; linarith [h] : |X j a| = - X j a)]
      linarith [exp_nonneg (X j a)]
    refine Left.add_nonneg ?hfg.ha ?hfg.hb
    exact exp_nonneg (-X j a)
    exact exp_nonneg (X j a)
  _ = ∫⁻ (a : Ω), ENNReal.ofReal (rexp (-(X j a))) + ENNReal.ofReal (rexp (X j a)) ∂μ := by
    apply lintegral_congr
    intro a
    refine ENNReal.ofReal_add (exp_nonneg (-X j a)) (exp_nonneg (X j a))
  _ = (∫⁻ (a : Ω), ENNReal.ofReal (rexp (-(X j a))) ∂μ) + ∫⁻ (a : Ω), ENNReal.ofReal (rexp ((X j a))) ∂μ := by
    rw [MeasureTheory.lintegral_add_left']
    refine AEMeasurable.ennreal_ofReal (Measurable.comp_aemeasurable' measurable_exp (AEMeasurable.neg q))
  _ ≤ ENNReal.ofReal (rexp (r ^ 2 / 2)) + ENNReal.ofReal (rexp (r ^ 2 / 2)) := by
    have p0 := p 1
    simp only [one_mul, one_pow] at p0
    have p1 := p (-1)
    simp only [neg_mul, one_mul, even_two, Even.neg_pow, one_pow] at p1
    apply add_le_add p1 p0
  _ < ⊤ := Batteries.compareOfLessAndEq_eq_lt.mp rfl

omit [IsProbabilityMeasure μ] in
private lemma measurable_expt' (X : Ω → ℝ) (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω => rexp (t * (X ω))) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <| measurable_exp.comp_aemeasurable' (hX.const_mul t)

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
private theorem integrable_exp_of_subgaussian
  (X : ι → Ω → ℝ) (j : ι) (r : ℝ)
  (p : ∀ (t : ℝ), ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ ≤ ENNReal.ofReal (rexp (t ^ 2 * r ^ 2 / 2)))
  (t : ℝ) (q : AEMeasurable (X j) μ) :
  Integrable (fun x ↦ rexp (t * X j x)) μ := by
  constructor
  refine measurable_expt' μ (X j) t ?left.hX
  exact q
  dsimp [HasFiniteIntegral]
  rw [lintegral_congr (by intro a; rw [enorm_eq_ofReal_abs]; simp : ∀ a, ‖rexp (t * X j a)‖ₑ = ENNReal.ofReal (rexp (t * X j a)))]
  exact trans (p t) ENNReal.ofReal_lt_top

private lemma enorm_mono (a b : ℝ) (p : a ≤ b) (q : 0 ≤ a):
    ‖a‖ₑ ≤ ‖b‖ₑ := by
  rw [<- ofReal_norm_eq_enorm]
  rw [<- ofReal_norm_eq_enorm]
  rw [ENNReal.ofReal_le_ofReal_iff]
  simp only [norm_eq_abs]
  exact abs_le_abs_of_nonneg q p
  exact norm_nonneg b

private lemma enorm_nonneg (a : ℝ) : 0 ≤ ‖a‖ₑ := by
  rw [<- ofReal_norm_eq_enorm]
  exact zero_le (ENNReal.ofReal ‖a‖)

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
private theorem Finset.aemeasurable_sup' {s : Finset ι} (hs : s.Nonempty) {f : ι → Ω → ℝ}
    (hf : ∀ n ∈ s, AEMeasurable (f n) μ) : AEMeasurable (s.sup' hs f) μ  := by
  let p (x : Ω → ℝ) := AEMeasurable x μ
  change p (s.sup' hs f)
  apply Finset.sup'_induction
  intro a_1
  intro r
  intro a_2
  intro r0
  exact AEMeasurable.sup' r r0
  exact hf

omit [IsProbabilityMeasure μ] [DecidableEq ι] in
private lemma aemeasurable_sup_pointwise
  {s : Finset ι} (H : s.Nonempty) {X : ι → Ω → ℝ}
  (hX : ∀ i ∈ s, AEMeasurable (X i) μ) :
  AEMeasurable (fun ω ↦ s.sup' H (fun j ↦ X j ω)) μ := by
  have hEq : (fun ω ↦ s.sup' H (fun j ↦ X j ω)) = s.sup' H X := by
    funext ω
    exact Eq.symm (Finset.sup'_apply H X ω)
  rw [hEq]
  apply Finset.aemeasurable_sup'
  exact hX

omit [DecidableEq ι] in
lemma maximal_inequality_finset (n : ℕ) (s : Finset ι) (n_car : s.card = n) (X : ι → Ω → ℝ) (r : ℝ)
    (n_pos : 1 < n) (r_pos : 0 < r) (H : s.Nonempty)
    (p : ∀ j ∈ s, ∀ t, ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * ((X j) ω))) ∂μ ≤ ENNReal.ofReal (Real.exp (t ^ 2 * r ^ 2 / 2)))
    (q7 : ∀ j ∈ s, AEMeasurable (X j) μ):
    ∫ (ω : Ω), Finset.sup' s H (fun j => (X j) ω) ∂μ ≤ r * Real.sqrt (2 * Real.log n) := by
  have l'' : AEStronglyMeasurable (fun ω ↦ s.sup' H fun j ↦ X j ω) μ := by
    apply AEMeasurable.aestronglyMeasurable
    change AEMeasurable (fun ω ↦ s.sup' H fun j ↦ X j ω) μ
    apply aemeasurable_sup_pointwise
    exact q7
  have q : ∀ j ∈ s, Integrable (X j) μ := fun j hj ↦ integrable_of_subgaussian μ X j r (p j hj) (q7 j hj)
  have p9 : 0 < √(2 * log ↑n) / r := by
    apply div_pos
    simp only [Nat.ofNat_nonneg, sqrt_mul, sqrt_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    refine log_pos ?ha.hx
    norm_cast
    exact r_pos
  have qq : ∀ t x, 0 ≤ t → rexp (s.sup' H fun j ↦ t * X j x) = s.sup' H fun j ↦ rexp (t * X j x) := by
    intro t x ht
    have s0 : rexp (s.sup' H fun j ↦ t * X j x) ≤ s.sup' H fun j ↦ rexp (t * X j x) := by
      rw [Finset.le_sup'_iff]
      have s0' : ∃ i ∈ s, (s.sup' H fun j ↦ X j x) = X i x := by
        apply Finset.exists_mem_eq_sup'
      obtain ⟨i, ⟨v, w⟩⟩ := s0'
      use i
      constructor
      exact v
      rw [<- w]
      simp only [exp_le_exp, Finset.sup'_le_iff]
      intro g gs
      apply mul_le_mul_of_nonneg_left
      rw [Finset.le_sup'_iff]
      use g
      exact ht
    have s1 : (s.sup' H fun j ↦ rexp (t * X j x)) ≤ rexp (s.sup' H fun j ↦ t * X j x) := by
      rw [Finset.sup'_le_iff]
      intro b bs
      rw [Real.exp_le_exp]
      rw [Finset.le_sup'_iff]
      use b
    apply LE.le.antisymm s0 s1
  have p0 : ∀ t , 0 ≤ t → Real.exp (t * ∫ (ω : Ω), Finset.sup' s H (fun j => (X j) ω) ∂μ) ≤
            n * Real.exp (t ^ 2 * r ^ 2 / 2) := by
    intro t ht
    calc
    _ ≤ ∫ (ω : Ω), Real.exp (t * Finset.sup' s H (fun j => (X j) ω)) ∂μ := by
      set g := fun x => rexp (t * x)
      set f := fun (ω : Ω) => s.sup' H fun j ↦ X j ω
      suffices g (∫ (ω : Ω), f ω ∂μ) ≤ ∫ (ω : Ω), g (f ω) ∂μ from by
        exact this
      apply ConvexOn.map_integral_le
      dsimp [g]
      exact (by apply convexon_exp)
      dsimp [g]
      apply ContinuousOn.rexp
      apply ContinuousOn.mul
      exact continuousOn_const
      exact continuousOn_id' Set.univ
      simp only [isClosed_univ]
      simp only [Set.mem_univ, Filter.eventually_true]
      · constructor
        · dsimp [f]
          exact l''
        · dsimp [f]
          dsimp [HasFiniteIntegral]
          calc
          _ ≤ ∫⁻ (a : Ω), s.sup' H fun j ↦ ‖X j a‖ₑ ∂μ := by
            apply lintegral_mono
            refine Pi.le_def.mpr ?_
            intro i
            refine (Finset.le_sup'_iff H).mpr ?_
            obtain ⟨b, hb⟩ := Finset.exists_mem_eq_sup' H fun j ↦ X j i
            use b
            constructor
            exact hb.1
            rw [hb.2]
          _ ≤ ∫⁻ (a : Ω), ∑ j ∈ s, ‖X j a‖ₑ ∂μ := by
            apply lintegral_mono
            refine Pi.le_def.mpr ?_
            intro i
            suffices ∀ j ∈ s, ‖X j i‖ₑ ≤ ∑ j ∈ s, ‖X j i‖ₑ from by
              exact Finset.sup'_le H (fun j ↦ ‖X j i‖ₑ) this
            intro j hj
            let f := fun j => ‖X j i‖ₑ
            suffices f j ≤ ∑ j ∈ s, f j from by
              exact this
            apply Finset.single_le_sum
            intro i is
            dsimp [f]
            simp only [zero_le, *]
            exact hj
          _ = ∑ j ∈ s, ∫⁻ (a : Ω), ‖X j a‖ₑ ∂μ := by
            refine lintegral_finset_sum' s ?_
            intro b bs
            exact AEMeasurable.enorm (q7 b bs)
          _ < ⊤ := by
            refine ENNReal.sum_lt_top.mpr ?_
            intro a as
            refine hasFiniteIntegral_iff_enorm.mp ?_
            exact Integrable.hasFiniteIntegral (q a as)
      · constructor
        · change AEStronglyMeasurable (fun x => g (f x)) μ
          apply Continuous.comp_aestronglyMeasurable
          · subst n_car
            simp_all only [Nat.ofNat_nonneg, sqrt_mul, div_pos_iff_of_pos_right, sqrt_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left,
              f, g]
            apply Continuous.comp'
            · apply Real.continuous_exp
            · apply continuous_mul_left
          · exact l''
        · dsimp [HasFiniteIntegral]
          dsimp [g, f]
          have q' : ∫⁻ (a : Ω), ‖rexp (t * s.sup' H fun j ↦ X j a)‖ₑ ∂μ < ⊤ := by
            calc
            _ ≤ ∫⁻ (a : Ω), s.sup' H fun j ↦ ‖rexp (t * X j a)‖ₑ ∂μ := by
              apply lintegral_mono
              refine Pi.le_def.mpr ?_
              intro i
              rw [Finset.le_sup'_iff]
              obtain ⟨b,bs,w0⟩ := Finset.exists_mem_eq_sup' H fun j ↦ X j i
              use b
              constructor
              exact bs
              rw [w0]
            _ ≤ ∫⁻ (a : Ω), ∑ j ∈ s, ‖rexp (t * X j a)‖ₑ ∂μ := by
              apply lintegral_mono
              refine Pi.le_def.mpr ?_
              intro i
              have v : ∀ k ∈ s, ‖rexp (t * X k i)‖ₑ ≤ ∑ j ∈ s, ‖rexp (t * X j i)‖ₑ := by
                intro k ks
                let y (k : ι) := ‖rexp (t * X k i)‖ₑ
                have v0 : y k ≤ ∑ j ∈ s, y j := by
                  apply Finset.single_le_sum
                  intro i' is
                  dsimp [y]
                  apply enorm_nonneg
                  exact ks
                exact v0
              exact Finset.sup'_le H (fun j ↦ ‖rexp (t * X j i)‖ₑ) v
            _ = ∑ j ∈ s, ∫⁻ (a : Ω), ‖rexp (t * X j a)‖ₑ ∂μ := by
              refine lintegral_finset_sum' s ?_
              intro b bs
              subst n_car
              simp_all only [Nat.ofNat_nonneg, sqrt_mul, div_pos_iff_of_pos_right, sqrt_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_left,f]
              apply AEMeasurable.coe_nnreal_ennreal
              apply AEMeasurable.nnnorm
              apply AEMeasurable.exp
              apply AEMeasurable.const_mul
              simp_all only
            _ ≤ ∑ j ∈ s, ‖rexp (t ^ 2 * r ^ 2 / 2)‖ₑ := by
              refine Finset.sum_le_sum ?_
              intro i is
              have q0 : ∀ s, ‖rexp s‖ₑ = ENNReal.ofReal (rexp s) := by
                intro s
                rw [Real.enorm_eq_ofReal]
                exact exp_nonneg s
              rw [q0]
              have q1 : ∫⁻ (a : Ω), ‖rexp (t * X i a)‖ₑ ∂μ = ∫⁻ (a : Ω), ENNReal.ofReal (rexp (t * X i a)) ∂μ := by
                apply lintegral_congr
                intro a
                exact q0 (t * X i a)
              rw [q1]
              exact p i is t
            _ < ⊤ := by
              refine ENNReal.sum_lt_top.mpr ?_
              intro a as
              exact enorm_lt_top
          assumption
    _ = ∫ (ω : Ω), Real.exp (Finset.sup' s H (fun j => t * (X j) ω)) ∂μ := by
      apply congrArg
      funext x
      apply congrArg
      have s0 : (t * s.sup' H fun j ↦ X j x) ≤ s.sup' H fun j ↦ t * X j x := by
        rw [Finset.le_sup'_iff]
        have s0' : ∃ i ∈ s, (s.sup' H fun j ↦ X j x) = X i x := by
          apply Finset.exists_mem_eq_sup'
        obtain ⟨i, ⟨v, w⟩⟩ := s0'
        rw [w]
        use i
      have s1 : (s.sup' H fun j ↦ t * X j x) ≤ (t * s.sup' H fun j ↦ X j x) := by
        rw [Finset.sup'_le_iff]
        intro b bs
        suffices X b x ≤ s.sup' H fun j ↦ X j x from by
          exact mul_le_mul_of_nonneg_left this ht
        rw [Finset.le_sup'_iff]
        use b
      linarith
    _ = ∫ (ω : Ω), Finset.sup' s H (fun j => Real.exp (t * (X j) ω)) ∂μ := by
      apply congrArg
      funext x
      exact qq t x ht
    _ ≤ ∫ (ω : Ω), ∑ j ∈ s, Real.exp (t * (X j) ω) ∂μ := by
      have w : ∀ ω, Finset.sup' s H (fun j => Real.exp (t * (X j) ω)) ≤ ∑ j ∈ s, rexp (t * X j ω) := by
        intro ω
        suffices ∀ k ∈ s, (rexp (t * X k ω) ≤ ∑ j ∈ s, (rexp (t * X j ω))) from by
          rw [Finset.sup'_le_iff]
          intro b xb
          exact this b xb
        intro k hk
        let f := rexp ∘ (fun j => t * X j ω)
        have g : f k ≤ ∑ j ∈ s, f j := by
          apply Finset.single_le_sum ?_ hk
          intro i hi
          exact exp_nonneg (t * X i ω)
        exact g
      apply integral_mono_of_nonneg
      filter_upwards
      intro a
      simp only [Pi.zero_apply]
      · rw [Finset.le_sup'_iff]
        have ⟨x, H'⟩ := Finset.Nonempty.exists_mem H
        use x
        constructor
        exact H'
        exact exp_nonneg (t * X x a)
      · refine integrable_finset_sum s ?hgi.hf
        intro i hi
        exact ProbabilityTheory.integrable_exp_of_subgaussian μ X i r (p i hi) t (q7 i hi)
      · filter_upwards
        intro a
        exact w a
    _ = (∑ j ∈ s, ∫ (ω : Ω), Real.exp (t * (X j) ω) ∂μ) := by
      refine integral_finset_sum s ?_
      intro i hi
      exact ProbabilityTheory.integrable_exp_of_subgaussian μ X i r (p i hi) t (q7 i hi)
    _ ≤ (∑ j ∈ s, Real.exp (t ^ 2 * r ^ 2 / 2)) := by
      apply Finset.sum_le_sum
      intro j js
      suffices ENNReal.ofReal (∫ (ω : Ω), rexp (t * X j ω) ∂μ) ≤ ENNReal.ofReal (rexp (t ^ 2 * r ^ 2 / 2)) from by
        rw [ENNReal.ofReal_le_ofReal_iff] at this
        exact this
        exact exp_nonneg (t ^ 2 * r ^ 2 / 2)
      have w : ENNReal.ofReal (∫ (ω : Ω), rexp (t * X j ω) ∂μ) = ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ := by
        apply ofReal_integral_eq_lintegral_ofReal
        exact ProbabilityTheory.integrable_exp_of_subgaussian μ X j r (p j js) t (q7 j js)
        filter_upwards
        intro a
        simp only [Pi.zero_apply]
        exact exp_nonneg (t * X j a)
      rw [w]
      exact p j js t
    _ = n * Real.exp (t ^ 2 * r ^ 2 / 2) := by
      norm_cast
      rw [Finset.sum_const]
      simp
      exact n_car
  have p1 : ∀ t, 0 ≤ t → t * ∫ (ω : Ω),Finset.sup' s H (fun j => (X j) ω) ∂μ ≤ t * ((Real.log n) / t + (t * r ^ 2 / 2)) := by
    intro t ht
    by_cases h : t = 0
    case pos =>
      rw [h]
      simp
    case neg =>
      have h' : 0 < t := by
        apply lt_of_le_of_ne
        exact ht
        symm
        intro q
        exact h q
      suffices ∫ (ω : Ω), Finset.sup' s H (fun j => (X j) ω) ∂μ ≤ (log ↑n / t + t * r ^ 2 / 2) from by
        exact (mul_le_mul_iff_of_pos_left h').mpr this
      have p1' := p0 t ht
      have p1'' : (t * ∫ (ω : Ω), Finset.sup' s H (fun j => (X j) ω) ∂μ) ≤ Real.log (↑n * rexp (t ^ 2 * r ^ 2 / 2)) := by
        rw [Real.le_log_iff_exp_le]
        exact p1'
        apply mul_pos
        norm_cast
        linarith [n_pos]
        exact exp_pos (t ^ 2 * r ^ 2 / 2)
      have p1''' : Real.log (↑n * rexp (t ^ 2 * r ^ 2 / 2)) = Real.log ↑n + t ^ 2 * r ^ 2 / 2 := by
        calc
        _ = Real.log ↑n + Real.log (rexp (t ^ 2 * r ^ 2 / 2)) := by
          apply Real.log_mul
          norm_cast
          linarith
          exact exp_ne_zero (t ^ 2 * r ^ 2 / 2)
        _ = Real.log ↑n + t ^ 2 * r ^ 2 / 2 := by rw [Real.log_exp]
      rw [p1'''] at p1''
      have p1'''' : t * ((Real.log ↑n) / t + (t * r ^ 2 / 2)) = Real.log ↑n + t ^ 2 * r ^ 2 / 2 := by
        calc
        _ = t * Real.log ↑n / t + t * t * r ^ 2 / 2 := by ring
        _ = Real.log ↑n + t * t * r ^ 2 / 2 := by
          rw [add_right_cancel_iff]
          field_simp
        _ = Real.log ↑n + t ^ 2 * r ^ 2 / 2 := by ring
      rw [<- p1''''] at p1''
      apply le_of_mul_le_mul_left
      exact p1''
      exact h'
  have p2 : ((Real.sqrt (2 * Real.log n)) / r) * ∫ (ω : Ω), Finset.sup' s H (fun j => (X j) ω) ∂μ ≤
          ((Real.sqrt (2 * Real.log n)) / r) * (log ↑n / ((Real.sqrt (2 * Real.log n)) / r) +
          ((Real.sqrt (2 * Real.log n)) / r) * ↑r ^ 2 / 2) := by
    apply p1
    suffices 0 ≤ √(2 * log ↑n) from by
      apply div_nonneg
      exact this
      exact le_of_lt r_pos
    simp
  have p3 : log ↑n / (√(2 * log ↑n) / ↑r) + √(2 * log ↑n) / ↑r * ↑r ^ 2 / 2
            = ↑r * √(2 * log ↑n) := by
    have p3' : log ↑n / (√(2 * log ↑n) / ↑r) = ↑r * √(log ↑n) / √2 := by
      calc
      _ = (log ↑n / √(2 * log ↑n)) * ↑r := by field_simp
      _ = ↑r * (log ↑n) / √(2 * log ↑n) := by ring
      _ = ↑r * (log ↑n) / (√2 * √(log ↑n)) := by simp
      _ = (↑r / √2) * (log ↑n / √(log ↑n)) := by ring
      _ = ↑r / √2 * √(log ↑n) := by simp
      _ = ↑r * √(log ↑n) / √2 := by ring
    have p3'' : √(2 * log ↑n) / ↑r * ↑r ^ 2 / 2 = ↑r * √(log ↑n) / √2 := by
      calc
      _ = √2 * √(log ↑n) / ↑r * ↑r ^ 2 / 2 := by simp
      _ = (√(log ↑n) / ↑r * ↑r ^ 2) * (√2 / 2) := by ring
      _ = (√(log ↑n) / ↑r * ↑r ^ 2) * (1 / √2) := by
        have p3''' : √2 / 2 = 1 / √2 := by field_simp; simp
        rw [p3''']
      _ = √(log ↑n) / ↑r * ↑r ^ 2 / √2 := by ring
      _ = √(log ↑n) * (↑r ^ 2 / ↑r) / √2 := by ring
      _ = √(log ↑n) * ↑r / √2 := by
        have p3'''' : ↑r ^ 2 / ↑r = ↑r :=
          calc
          _ = ↑r * ↑r / ↑r := by ring
          _ = ↑r := by simp
        rw [p3'''']
      _ = ↑r * √(log ↑n) / √2 := by ring
    rw [p3', p3'']
    calc
    _ = 2 * ↑r * √(log ↑n) / √2 := by ring
    _ = (2 / √2) * ↑r * √(log ↑n) := by ring
    _ = √2 * ↑r * √(log ↑n) := by simp
    _ = ↑r * (√2 * √(log ↑n)) := by ring
    _ = ↑r * √(2 * log ↑n) := by simp
  rw [p3] at p2
  exact le_of_mul_le_mul_left p2 p9

omit [DecidableEq ι] in
lemma sup'_pow (s : Finset ι)
    (f : ι → ℝ) (hs) (hf : ∀ a ∈ s, 0 ≤ f a) :
    s.sup' hs f ^ 2 = s.sup' hs fun a ↦ f a ^ 2 := by
  have h_sup : ∀ a ∈ s, f a ≤ s.sup' hs f := fun a ha => Finset.le_sup' f ha
  have h_max : ∃ a ∈ s, s.sup' hs f = f a := Finset.exists_mem_eq_sup' hs f
  obtain ⟨a₀, ha₀, h_eq⟩ := h_max
  rw [h_eq]
  apply le_antisymm
  · -- (f a₀) ^ 2 ≤ s.sup' hs (fun a => f a ^ 2)
    rw [Finset.le_sup'_iff]
    use a₀, ha₀
  · -- s.sup' hs (fun a => f a ^ 2) ≤ (f a₀) ^ 2
    rw [Finset.sup'_le_iff]
    intro b hb
    have hb_nonneg : 0 ≤ f b := hf b hb
    have ha₀_nonneg : 0 ≤ f a₀ := hf a₀ ha₀
    have : f b ≤ f a₀ := by
      rw [← h_eq]
      exact h_sup b hb
    exact (sq_le_sq₀ (hf b hb) (hf a₀ ha₀)).mpr this

lemma maximal_inequality_supR'
  {ι ι' : Type*} [DecidableEq ι']
  (n : ℕ) (s : Finset ι) (s' : Finset ι') (hs' : s'.Nonempty)
  (n_car : s'.card = n)
  (X : ι' → Ω → ℝ)
  (Y : ι → ι' → Ω → ℝ)
  (r : ι → ι' → ℝ)
  (n_pos : 1 < n)
  (r_pos : ∃ j ∈ s', (∃ i ∈ s, r i j > 0))
  (y_pos : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, Y i j ω ≤ r i j)
  (y_neg : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, - r i j ≤ Y i j ω)
  (y_ave : ∀ i ∈ s, ∀ j ∈ s', ∫ ω, Y i j ω ∂μ = 0)
  (y_mea : ∀ i, ∀ j, Measurable (Y i j))
  (s_ind : ∀ j ∈ s', iIndepFun (fun i ↦ Y i j) μ)
  (xy : ∀ j ∈ s', (X j = ∑ i ∈ s, Y i j)) :
  let R : ι' → ℝ := fun j => Real.sqrt (∑ i ∈ s, (r i j) ^ 2)
  ∫ ω, Finset.sup' s' hs' (fun j => X j ω) ∂μ
    ≤ (Finset.sup' s' hs' R) * Real.sqrt (2 * Real.log n) := by
  intro r'
  have p1 : ∀ j ∈ s', ∀ (t : ℝ), ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ ≤ ENNReal.ofReal (rexp (t ^ 2 * s'.sup' hs' r' ^ 2 / 2)) := by
    intro j hj t
    have w : ∫⁻ (ω : Ω), ENNReal.ofReal (rexp (t * X j ω)) ∂μ = ENNReal.ofReal (∫ (ω : Ω), (rexp (t * X j ω)) ∂μ) := by
      refine Eq.symm (ofReal_integral_eq_lintegral_ofReal ?hfi ?f_nn)
      constructor
      refine measurable_expt' μ (X j) t ?hfi.left.hX
      · subst n_car
        simp_all only [gt_iff_lt]
        apply Finset.aemeasurable_sum
        intro i a
        apply Measurable.aemeasurable
        simp_all only
      dsimp [HasFiniteIntegral]
      have w : ∫⁻ (a : Ω), ↑‖rexp (t * X j a)‖₊ ∂μ < ⊤ := by
        calc
        _ ≤ ∫⁻ (a : Ω), ENNReal.ofReal (rexp (|t * X j a|)) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards
          intro a
          have w' : ↑‖rexp (t * X j a)‖₊ = ENNReal.ofReal (rexp (t * X j a)) := Real.enorm_eq_ofReal (exp_nonneg (t * X j a))
          rw [w']
          refine ENNReal.ofReal_le_ofReal ?h.h.h
          refine exp_le_exp.mpr ?h.h.h.a
          exact le_abs_self (t * X j a)
        _ ≤  ∫⁻ (a : Ω), ENNReal.ofReal (rexp |t * (∑ i ∈ s, r i j)|) ∂μ := by
          rw [xy]
          apply lintegral_mono
          · intro a
            simp
            apply ENNReal.ofReal_le_ofReal
            rw [exp_le_exp]
            rw [←abs_mul, abs_mul]
            apply mul_le_mul_of_nonneg_left
            · calc |∑ c ∈ s, Y c j a|
                ≤ ∑ c ∈ s, |Y c j a| := by exact Finset.abs_sum_le_sum_abs (fun i ↦ Y i j a) s
              _ ≤ ∑ c ∈ s, r c j := by
                  apply Finset.sum_le_sum
                  intro i hi
                  rw [abs_le]
                  constructor
                  · exact y_neg i hi j hj a
                  · exact y_pos i hi j hj a
              _ ≤ |∑ i ∈ s, r i j| := le_abs_self _
            · exact abs_nonneg t
          · exact hj

        _ < ⊤ := by
          refine lintegral_const_lt_top ?_
          exact ENNReal.ofReal_ne_top
      exact w
      filter_upwards
      intro a
      simp only [Pi.zero_apply]
      exact exp_nonneg (t * X j a)
    calc
    _ = ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * ((∑ i ∈ s, Y i j) ω))) ∂μ := by
      rw [xy j hj]
    _ = ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (∑ i ∈ s, t * Y i j ω)) ∂μ := by
      have q : ∀ ω : Ω, (t * (∑ i ∈ s, Y i j) ω) = (∑ i ∈ s, t * Y i j ω) := by
        intro ω
        calc
        _ = t * (∑ i ∈ s, Y i j ω) := by
          suffices (∑ i ∈ s, Y i j) ω = ∑ i ∈ s, Y i j ω from by
            rw [this]
          exact Finset.sum_apply ω s fun c ↦ Y c j
        _ = ∑ i ∈ s, t * Y i j ω := Finset.mul_sum s (fun i ↦ Y i j ω) t
      have q' : ∀ (ω : Ω), rexp (t * (∑ i ∈ s, Y i j) ω) = rexp (∑ i ∈ s, t * Y i j ω) := by
        intro ω
        have q0 := q ω
        rw [q0]
      apply lintegral_congr_ae
      filter_upwards with ω
      exact congrArg ENNReal.ofReal (q' ω)
    _ = ∫⁻ (ω : Ω), ENNReal.ofReal (∏ i ∈ s, Real.exp (t * Y i j ω)) ∂μ := by
      have q : ∀ ω : Ω, (rexp (∑ i ∈ s, t * Y i j ω) = ∏ i ∈ s, rexp (t * Y i j ω)) := by
        intro ω
        exact exp_sum s fun x ↦ t * Y x j ω
      apply lintegral_congr_ae
      filter_upwards with ω
      exact congrArg ENNReal.ofReal (q ω)
    _ = ∫⁻ (ω : Ω), ∏ i ∈ s, ENNReal.ofReal (Real.exp (t * Y i j ω)) ∂μ := by
      apply lintegral_congr
      intro a
      refine ENNReal.ofReal_prod_of_nonneg ?h.hf
      intro i hi
      exact exp_nonneg (t * Y i j a)
    _ = ∏ i ∈ s, ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * Y i j ω)) ∂μ := by
      apply ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun (s := s) (X := fun i ω ↦ ENNReal.ofReal (Real.exp (t * Y i j ω)))
      · change iIndepFun (fun i ↦ (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (t * x))) ∘ Y i j) μ
        refine ProbabilityTheory.iIndepFun.comp (s_ind j hj) ?_ ?_
        intro i
        refine Measurable.ennreal_ofReal ?_
        refine Continuous.borel_measurable ?_
        refine Continuous.rexp ?_
        exact continuous_mul_left t
      · intro i
        subst n_car
        simp_all only [gt_iff_lt, Finset.sum_apply]
        apply Measurable.coe_nnreal_ennreal
        apply Measurable.real_toNNReal
        apply Measurable.exp
        apply Measurable.const_mul
        simp_all only
    _ ≤ ∏ i ∈ s, ENNReal.ofReal (Real.exp (t ^ 2 * r i j ^ 2 / 2)) := by
      suffices ∀ i ∈ s, ∫⁻ (ω : Ω), ENNReal.ofReal (Real.exp (t * Y i j ω)) ∂μ ≤ ENNReal.ofReal (Real.exp (t ^ 2 * r i j ^ 2 / 2)) from by
        exact Finset.prod_le_prod' this
      intro i hi
      have : t ^ 2 * r i j ^ 2 / 2 = t ^ 2 * (r i j - (- r i j)) ^ 2 / 8 := by
        simp
        grind
      rw [this]
      rw [<- MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
      apply ENNReal.ofReal_le_ofReal
      apply hoeffding
      · exact Measurable.aemeasurable (y_mea i j)
      · filter_upwards
        intro ω
        constructor
        · apply y_neg
          exact hi
          exact hj
        · apply y_pos
          exact hi
          exact hj
      · apply y_ave
        exact hi
        exact hj
      · constructor
        · subst n_car
          simp_all only [gt_iff_lt, Finset.sum_apply, sub_neg_eq_add]
          apply Measurable.aestronglyMeasurable
          apply Measurable.exp
          apply Measurable.const_mul
          simp_all only
        · by_cases ht : 0 ≤ t
          · apply MeasureTheory.HasFiniteIntegral.of_bounded
            filter_upwards with ω
            change ‖rexp (t * Y i j ω)‖ ≤ ‖rexp (t * r i j)‖
            refine norm_le_norm_of_abs_le_abs ?_
            simp
            exact mul_le_mul_of_nonneg_left (y_pos i hi j hj ω) ht
          · apply MeasureTheory.HasFiniteIntegral.of_bounded
            filter_upwards with ω
            change ‖rexp (t * Y i j ω)‖ ≤ ‖rexp (t * (-r i j))‖
            refine norm_le_norm_of_abs_le_abs ?_
            simp only [abs_exp, exp_le_exp]
            have ht' : t < 0 := not_le.mp ht
            exact mul_le_mul_of_nonpos_left (y_neg i hi j hj ω) (le_of_lt ht')
      · filter_upwards with ω
        apply exp_nonneg
    _ ≤ _ := by
      rw [<- ENNReal.ofReal_prod_of_nonneg]
      apply ENNReal.ofReal_le_ofReal
      have : ∏ i ∈ s, rexp (t ^ 2 * r i j ^ 2 / 2) = rexp (t ^ 2 * ∑ i ∈ s, (r i j ^ 2) / 2) := by
        rw [← exp_sum]
        congr 1
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [this]
      rw [exp_le_exp]
      have : ∑ i ∈ s, r i j ^ 2 ≤ s'.sup' hs' r' ^ 2 := by
        dsimp [r']
        have : (s'.sup' hs' fun j ↦ √(∑ i ∈ s, r i j ^ 2)) ^ 2 = (s'.sup' hs' fun j ↦ (∑ i ∈ s, r i j ^ 2)) := by
          rw [sup'_pow]
          apply congrArg
          ext j
          apply sq_sqrt
          apply Finset.sum_nonneg
          exact fun i a ↦ sq_nonneg (r i j)
          intro a ha
          simp
        rw [this]
        refine (Finset.le_sup'_iff hs').mpr ?_
        use j
      · rw [<- Finset.sum_div]
        rw [mul_div]
        rw [div_le_div_iff_of_pos_right]
        apply mul_le_mul_of_nonneg_left
        exact this
        exact sq_nonneg t
        simp
      · intro i hi
        apply exp_nonneg
  apply maximal_inequality_finset
  · exact n_car
  · exact n_pos
  · rw [Finset.lt_sup'_iff]
    dsimp [r']
    obtain ⟨b, ⟨hb1, hb2⟩⟩ := r_pos
    use b
    constructor
    · exact hb1
    · obtain ⟨c, ⟨hc1, hc2⟩⟩ := hb2
      apply Real.sqrt_pos.mpr
      apply Finset.sum_pos'
      · intro k hk
        apply sq_nonneg
      · use c
        constructor
        · exact hc1
        · exact sq_pos_of_pos hc2
  · intro j hj t
    apply p1
    exact hj
  · intro j hj
    rw [xy j hj]
    refine Finset.aemeasurable_sum s ?q7.hf
    intro i hi
    exact Measurable.aemeasurable (y_mea i j)

lemma maximal_inequality_supR
  {ι ι' : Type*} [DecidableEq ι']
  (n : ℕ) (s : Finset ι) (s' : Finset ι') (hs' : s'.Nonempty)
  (n_car : s'.card = n)
  (X : ι' → Ω → ℝ)
  (Y : ι → ι' → Ω → ℝ)
  (r : ι → ι' → ℝ)
  (y_pos : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, Y i j ω ≤ r i j)
  (y_neg : ∀ i ∈ s, ∀ j ∈ s', ∀ ω, - r i j ≤ Y i j ω)
  (y_ave : ∀ i ∈ s, ∀ j ∈ s', ∫ ω, Y i j ω ∂μ = 0)
  (y_mea : ∀ i, ∀ j, Measurable (Y i j))
  (s_ind : ∀ j ∈ s', iIndepFun (fun i ↦ Y i j) μ)
  (xy : ∀ j ∈ s', (X j = ∑ i ∈ s, Y i j)) :
  let R : ι' → ℝ := fun j => Real.sqrt (∑ i ∈ s, (r i j) ^ 2)
  ∫ ω, Finset.sup' s' hs' (fun j => X j ω) ∂μ
    ≤ (Finset.sup' s' hs' R) * Real.sqrt (2 * Real.log n) := by
  by_cases hn : 1 < n
  case pos =>
    by_cases hr : ∃ j ∈ s', ∃ i ∈ s, r i j > 0
    case pos =>
      apply maximal_inequality_supR' μ n s s' hs' n_car X Y r hn hr y_pos y_neg y_ave y_mea s_ind xy
    case neg =>
      simp at hr
      intro R
      have hX0 : ∀ j ∈ s', ∀ (ω : Ω), X j = 0 := by
        have hX1 : ∀ i ∈ s, ∀ j ∈ s', r i j = 0 := by
          intros i hi j hj
          specialize hr j hj i hi
          have h_ge : 0 ≤ r i j := by
            have : Nonempty Ω := MeasureTheory.Measure.nonempty_of_neZero μ
            obtain ⟨ω⟩ := (inferInstance : Nonempty Ω)
            specialize y_pos i hi j hj ω
            specialize y_neg i hi j hj ω
            linarith
          linarith [hr, h_ge]
        have hX2 : ∀ i ∈ s, ∀ j ∈ s', Y i j = 0 := by
          intro i hi j hj
          ext ω
          have hr_eq := hX1 i hi j hj
          have h_pos := y_pos i hi j hj ω
          have h_neg := y_neg i hi j hj ω
          rw [hr_eq] at h_pos h_neg
          simp only [neg_zero] at h_neg
          simp only [Pi.zero_apply]
          linarith
        intro j hj ω
        have := xy j hj
        rw [this]
        apply Finset.sum_eq_zero
        intro i hi
        have := hX2 i hi j hj
        exact this
      calc
      (∫ (ω : Ω), Finset.sup' s' hs' (fun j => (X j) ω) ∂μ) = ∫ (ω : Ω), 0 ∂μ := by
        congr
        ext ω
        calc
        (s'.sup' hs' (fun j => X j ω)) = s'.sup' hs' (fun j => 0) := by
          apply Finset.sup'_congr
          · rfl
          · exact fun x a ↦ congrFun (hX0 x a ω) ω
        _ = 0 := by
          exact Finset.sup'_const hs' 0
      _ = 0 := by
        simp
      _ ≤ _ := by
        refine Right.mul_nonneg ?_ ?_
        · refine (Finset.le_sup'_iff hs').mpr ?_
          obtain ⟨b, hb⟩ := hs'
          use b, hb
          apply sqrt_nonneg
        · apply sqrt_nonneg
  case neg =>
    have hn' : n = 1 := by
      have : n ≠ 0 := by
        intro hn''
        have : s' = ∅ := by
          apply Finset.card_eq_zero.mp
          exact hn'' ▸ n_car
        exact Finset.not_nonempty_empty (this ▸ hs')
      grind
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hn' ▸ n_car)
    intro r'
    calc
    (∫ (ω : Ω), Finset.sup' s' hs' (fun j => (X j) ω) ∂μ) = ∫ (ω : Ω), X j ω ∂μ := by
      congr
      ext ω
      calc
      _ = ({j} : Finset ι').sup' (hj ▸ hs') (fun j => X j ω) := by
        congr
      _ = _ := by
        apply Finset.sup'_singleton
    _ = ∑ i ∈ s, ∫ (ω : Ω), Y i j ω ∂μ := by
      rw [xy j (by grind)]
      have q : ∀ i ∈ s, Integrable (Y i j) μ := by
        intro i hi
        constructor
        . apply AEMeasurable.aestronglyMeasurable
          exact Measurable.aemeasurable (y_mea i j)
        . apply MeasureTheory.HasFiniteIntegral.of_bounded
          filter_upwards with ω
          exact abs_le.mpr ⟨y_neg i hi j (by grind) ω, y_pos i hi j (by grind) ω⟩
      convert MeasureTheory.integral_finset_sum s q
      simp
    _ = ∑ i ∈ s, 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact y_ave i hi j (by grind)
    _ = 0 := by simp
    _ ≤ _ := by
      refine Right.mul_nonneg ?_ ?_
      · refine (Finset.le_sup'_iff hs').mpr ?_
        dsimp [r']
        use j
        constructor
        · rw [hj]; simp
        · apply sqrt_nonneg
      · apply sqrt_nonneg

end ProbabilityTheory
