import FoML.Defs
import FoML.MaximalInequality
import FoML.RademacherVariableProperty
import FoML.Symmetrization
import FoML.MeasurePiLemmas

universe v u
open scoped BigOperators
open Classical MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

variable {Z : Type v}
variable {m : ℕ} {ι : Type u}

instance : Nonempty ({-1, 1} : Finset ℤ) := by
  use -1
  simp

instance : @MeasurableSingletonClass (Signs m) MeasurableSpace.pi :=
  @MeasurableSingletonClass.mk (Signs m) MeasurableSpace.pi (by
    intro x
    let f : Fin m → Set (Signs m) := fun i : Fin m ↦ (Function.eval i)⁻¹' {x i}
    have : ∀ i : Fin m, @MeasurableSet (Signs m) MeasurableSpace.pi (f i) := by
      intro i
      dsimp [f]
      apply MeasurableSet.preimage
      · exact measurableSet_singleton (x i)
      · exact measurable_pi_apply i
    convert MeasurableSet.iInter this
    ext y
    constructor
    · intro eq
      simp at eq
      rw [eq]
      exact Set.mem_iInter.mpr (congrFun rfl)
    · intro h
      simp
      dsimp [Signs]
      ext i
      have := Set.mem_iInter.mp h i
      dsimp [f] at this
      simp at this
      exact congrArg Subtype.val this
  )

lemma measurablespace_eq : instMeasurableSpaceSigns m = MeasurableSpace.pi := by
  ext s
  constructor
  · intro h
    exact @Set.Finite.measurableSet (Signs m) MeasurableSpace.pi  _ s (Set.toFinite s)
  · intro h
    trivial

lemma measure_eq :
  (signVecPMF m).toMeasure ≍ Measure.pi fun (_ : Fin m) ↦ (PMF.uniformOfFintype ({-1, 1} : Finset ℤ)).toMeasure := by
  rw [measurablespace_eq]
  refine (Equiv.cast_eq_iff_heq ?_).mp ?_
  · rfl
  · apply Eq.symm
    apply Measure.pi_eq
    intro s hs
    dsimp [signVecPMF, Signs]
    rw [PMF.toMeasure_uniformOfFintype_apply (Set.univ.pi s) (MeasurableSet.univ_pi hs)]
    have : (Fintype.card (Set.univ.pi s) : ENNReal) / (Fintype.card (Fin m → ({-1, 1} : Finset ℤ)) : ENNReal)
      = ∏ i : Fin m, (Fintype.card (s i) : ENNReal) / (2 : ENNReal) := by
      have Ps_eq: {f : Fin m → ({-1, 1} : Finset ℤ) // ∀ i, f i ∈ (s i)} ≃ ∀ (i : Fin m), {fi // fi ∈ (s i)} := by
        apply Equiv.subtypePiEquivPi
      have : ((Set.univ.pi s) : Type) = {f : Fin m → ({-1, 1} : Finset ℤ) // ∀ i, f i ∈ (s i)} := by
        congr
        exact Set.Subset.antisymm (fun ⦃a⦄ a i ↦ a i trivial) fun ⦃a⦄ a i a_1 ↦ a i
      rw [←this] at Ps_eq
      rw [Fintype.card_congr Ps_eq, Fintype.card_pi, Fintype.card_pi]
      have : ∏ i : Fin m, (Fintype.card ↑(s i) : ENNReal) / 2 = ∏ i : Fin m, ↑(Fintype.card ↑(s i) : ENNReal) * 2⁻¹ := by
        congr
      rw [this]
      rw [Finset.prod_mul_distrib]
      simp
      rw [div_eq_mul_inv]
      congr
      exact ENNReal.inv_pow
    rw [this]
    congr
    ext i
    rw [PMF.toMeasure_uniformOfFintype_apply (s i) (hs i)]
    simp


variable (F : ι → Z → ℝ)
variable (S : Fin m → Z)

/-
Aligned notations for using maximal_inequality’s style in this file.
These are lightweight definitions/notations that make types line up; no proofs.
-/
namespace MassartNotation

open MeasureTheory

-- probability space for Rademacher signs
local notation3 "Ωᵣ" => Signs m

-- random increments Y i j : Ωᵣ → ℝ
noncomputable def Y (i : Fin m) (j : ι) : Ωᵣ → ℝ :=
  fun σ => (m : ℝ)⁻¹ * (((σ i).1 : ℤ) : ℝ) * F j (S i)

-- aggregated variable X j = ∑ i∈s_samples Y i j
noncomputable def X (j : ι) : Ωᵣ → ℝ :=
  fun σ => ∑ i : Fin m, Y (F:=F) (S:=S) i j σ

-- per-sample envelope r i (independent of j), and its ℓ2-aggregate r′
noncomputable def r (f : Finset ι) (hs : f.Nonempty) (i : Fin m) : ℝ :=
  (m : ℝ)⁻¹ * Finset.sup' f hs (fun j => |F j (S i)|)

noncomputable def r' (i : Fin m) (j : ι) : ℝ :=
  (m : ℝ)⁻¹ * |F j (S i)|

end MassartNotation

lemma MassartNotation.xy_identity
    (f : Finset ι)
    : ∀ j ∈ f,
        (MassartNotation.X (F:=F) (S:=S) (m:=m) (ι:=ι) j
          = ∑ i : Fin m,
              MassartNotation.Y (F:=F) (S:=S) (m:=m) (ι:=ι) i j) := by
  intro j hj
  -- Now show function equality pointwise in `σ`.
  funext σ
  -- Expand definitions; the RHS reduces to the sum over `Finset.univ` via `sum_image`.
  simp [MassartNotation.X, MassartNotation.Y]

/-
Restrict the function class to a finite set `f` so we can use
`empiricalRademacherComplexity_pmf m (F_on F f) S` directly.
-/

def F_on (F : ι → Z → ℝ) (f : Finset ι) : {j // j ∈ f} → Z → ℝ :=
  fun j z => F j.1 z

theorem massart_lemma_pmf.sign_mean_zero {Z : Type v} {m : ℕ}
    (f : Z → ℝ) (S : Fin m → Z)
    (a : Fin m):
    ∫ (ω : Signs m), ↑↑(ω a) * f (S a) ∂(signVecPMF m).toMeasure = 0 := by
  rw [PMF.integral_eq_tsum]
  · dsimp [signVecPMF, PMF.uniformOfFintype]
    simp only [Finset.mem_univ, ↓reduceIte, Signs.card, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, Int.reduceNeg]
    rw [tsum_mul_left]
    suffices ∑' (a_1 : Signs m), (↑↑(a_1 a) * f (S a)) = 0 from by
      exact mul_eq_zero_of_right (2 ^ m)⁻¹ this
    rw [tsum_mul_right]
    simp only [Int.reduceNeg, tsum_fintype, mul_eq_zero]
    left
    apply sign_sum_eq_zero
  · exact Integrable.of_finite

lemma massart_lemma_pmf
    (f : Finset ι) (hs : f.Nonempty) (m_pos : 0 < m)
    (C : ℝ) (hC : ∀ i ∈ f, ∀ j, |F i (S j)| ≤ C)
    (hsR : f.Nonempty) :
    empiricalRademacherComplexity_pmf_without_abs m (F_on (ι:=ι) (Z:=Z) F f) S
      ≤ (Finset.sup' f hs fun j => Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |F j (S i)|) ^ 2)) * Real.sqrt (2 * Real.log f.card) := by
    have hbridge :
        empiricalRademacherComplexity_pmf_without_abs m (F_on (ι:=ι) (Z:=Z) F f) S
          = ∫ σ, Finset.sup' f hsR
                (fun j => MassartNotation.X (F:=F) (S:=S) (m:=m) (ι:=ι) j σ) ∂(signVecPMF m).toMeasure := by
      dsimp [empiricalRademacherComplexity_pmf_without_abs]
      dsimp [MassartNotation.X]
      dsimp [MassartNotation.Y]
      dsimp [F_on]
      apply congrArg
      ext σ
      calc
      _ = ⨆ (i : { j // j ∈ f }), ∑ k, (↑m)⁻¹ * (↑↑(σ k) * F (↑i) (S k)) := by
        apply congrArg
        ext i
        exact Finset.mul_sum Finset.univ (fun i_1 ↦ ↑↑(σ i_1) * F (↑i) (S i_1)) (↑m)⁻¹
      _ = ⨆ (i : { j // j ∈ f }), ∑ k, (↑m)⁻¹ * ↑↑(σ k) * F (↑i) (S k) := by
        apply congrArg
        ext i
        apply congrArg
        ext k
        ring
      _ = _ := by
        rw [le_antisymm_iff]
        constructor
        · have : Nonempty { j // j ∈ f } := by
            simp
            exact hs
          apply ciSup_le
          intro x
          simp
          use x
          constructor
          · simp
          · simp
        · simp
          intro b bf
          apply le_ciSup_of_le
          rw [bddAbove_def]
          · simp
            use C
            intro a af
            calc
            _ ≤ ∑ x, |(↑m)⁻¹ * ↑↑(σ x) * F a (S x)| := by
              apply Finset.sum_le_sum
              intro i hi
              exact le_abs_self ((↑m)⁻¹ * ↑↑(σ i) * F a (S i))
            _ = ∑ x, (↑m)⁻¹ * |↑↑(σ x) * F a (S x)| := by
              apply congrArg
              ext x
              rw [mul_assoc]
              rw [abs_mul]
              simp
            _ = ∑ x, (↑m)⁻¹ * |F a (S x)| := by
              apply congrArg
              ext x
              apply congrArg
              rw [abs_mul]
              rw [abs_sigma]
              simp
            _ = (↑m)⁻¹ * ∑ x, |F a (S x)| := by
              exact Eq.symm (Finset.mul_sum Finset.univ (fun i ↦ |F a (S i)|) (↑m)⁻¹)
            _ ≤ (↑m)⁻¹ * ∑ x : Fin m, C := by
              refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
              simp [m_pos]
              apply Finset.sum_le_sum
              intro i hi
              apply hC
              exact af
            _ ≤ (↑m)⁻¹ * (m * C) := by
              simp
            _ = _ := by field_simp
          apply Finset.sum_le_sum
          intro i hi
          set j' : { j // j ∈ f } := ⟨b, bf⟩
          -- ↑j' is definally b
          have : (↑m : ℝ)⁻¹ * ↑↑(σ i) * F b (S i)
              = (↑m : ℝ)⁻¹ * ↑↑(σ i) * F (j' : ι) (S i) := by simp [j']
          exact le_of_eq this
    rw [hbridge]
    dsimp [MassartNotation.X, MassartNotation.Y]
    refine ProbabilityTheory.maximal_inequality_supR
      (μ := (signVecPMF m).toMeasure)
      (n := f.card)
      (s := (Finset.univ : Finset (Fin m)))
      (s' := f)
      hsR
      rfl
      (X := MassartNotation.X (F:=F) (S:=S) (m:=m) (ι:=ι))
      (Y := MassartNotation.Y (F:=F) (S:=S) (m:=m) (ι:=ι))
      (r := fun i j ↦ (m : ℝ)⁻¹ * |F j (S i)|)
      ?y_pos ?y_neg ?y_ave ?y_mea ?s_ind ?xy
    · simp
      dsimp [MassartNotation.Y, MassartNotation.r]
      intro a a_1 af ω
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ ?_
      · calc
        _ ≤ |↑↑(ω a) * F a_1 (S a)| := by
          exact le_abs_self (↑↑(ω a) * F a_1 (S a))
        _ = |↑↑(ω a)| * |F a_1 (S a)| := by
          rw [abs_mul]
        _ = _ := by simp
      · simp
    · simp
      dsimp [MassartNotation.Y, MassartNotation.r]
      intro a a_1 af ω
      calc
      _ = -|((↑m)⁻¹ * ↑↑(ω a) * F a_1 (S a))| := by
        rw [abs_mul]
        rw [abs_mul]
        simp
      _ ≤ _ := by
        exact neg_abs_le ((↑m)⁻¹ * ↑↑(ω a) * F a_1 (S a))
    · simp
      dsimp [MassartNotation.Y]
      intro a a_1 af
      have h :=
        ProbabilityTheory.massart_lemma_pmf.sign_mean_zero
          (f := fun z => (↑m : ℝ)⁻¹ * F a_1 z) (S := S) (a := a)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · intro i j
      exact fun ⦃t⦄ a ↦ trivial
    · intro a af
      have signs_coord_indep :
          iIndepFun (fun i ↦ MassartNotation.Y (F:=F) (S:=S) (m:=m) i a) (signVecPMF m).toMeasure := by
        dsimp [MassartNotation.Y]
        have h : ∀ (i : Fin m), Measurable fun (σi : ({-1, 1} : Finset ℤ)) ↦ (↑m)⁻¹ * (σi.1 : ℝ) * F a (S i) := by
          intro i
          measurability
        convert iIndepFun.comp pi_eval_iIndepFun
          (fun i ↦ fun (σi : ({-1, 1} : Finset ℤ)) => (m : ℝ)⁻¹ * (σi.1 : ℝ) * F a (S i)) h
        · exact measurablespace_eq
        · exact measure_eq
        · exact PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype { x // x ∈ {-1, 1} })
      exact signs_coord_indep
    · intro a af
      apply MassartNotation.xy_identity
      exact af
