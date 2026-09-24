import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
-- `import FoML` (root module) would be cyclic here; the root imports at the time of porting:
import FoML.Generalization.LinearPredictorL2
import FoML.Generalization.LinearPredictorL1
import FoML.Generalization.RKHS
import FoML.Generalization.Dudley
import FoML.Generalization.FiniteClass
import FoML.Generalization.LipschitzParameter
import FoML.Generalization.Learning
import FoML.Generalization.RKHSLearning
import FoML.Learning.Contraction
import FoML.Rademacher.Reindex
import FoML.ToFoML.SudakovMinoration

/-!
# One-sided uniform deviation bounds via one-sided symmetrization

FoML's uniform-deviation chain (`FoML.Generalization.Countable`, `FoML.Generalization.Separable`)
is stated for the *two-sided* deviation `uniformDeviation n f μ X S = sup_i |L̂ f_i − L f_i|` and
the *absolute* Rademacher complexity `empiricalRademacherComplexity` (`𝔼_σ sup_i |n⁻¹ ∑ σ_k f_i|`).
This file develops the parallel chain for the *one-sided* deviation

`oneSidedDeviation n f μ X S = sup_i (n⁻¹ ∑_k f_i(S_k) − 𝔼 f_i)`

and the one-sided (no absolute value) complexity `empiricalRademacherComplexity_without_abs`:

* one-sided symmetrization `𝔼 sup_i (L̂ f_i − L f_i) ≤ 2 𝔼_S R̂_S^{no-abs}(f)`
  (FoML's `symmetrization_equation` is already the no-abs identity; the absolute version is derived
  from it in FoML, so we only need to drop the absolute values in the surrounding chain);
* bounded differences and McDiarmid for the one-sided deviation and for the one-sided empirical
  complexity;
* the countable-class tail bounds `P(Δ ≥ 2 R_n + ε) ≤ exp(−nε²/(2b²))` and the observed-sample
  version `P(Δ ≥ 2 R̂_S + 3ε) ≤ 2 exp(−nε²/(2b²))`;
* the lifting to separable classes via `denseRestriction`;
* a two-sided bound `P(∃ i, |L f_i − L̂ f_i| > 2 C(S) + 3ε) ≤ 4 exp(−nε²/(2b²))` obtained by
  applying
  the one-sided bound to `f` and to `−f` (union bound), where `C(S)` dominates both one-sided
  empirical complexities `R̂_S^{no-abs}(f)` and `R̂_S^{no-abs}(−f)`.

The point of the one-sided chain is that the one-sided complexity contracts with constant `L`
(no factor `2`, no singleton term, cf.
`FoML.ToFoML.empiricalRademacherComplexity_without_abs_contraction`),
which recovers the paper's constant `2 β_ℓ R̂_S(𝓗)` in the uniform deviation bound.

This file depends only on Mathlib, FoML and `FoML.ToFoML.SudakovMinoration` (for the sign
flip `negSigns` on `Signs n`).
-/

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal BigOperators

namespace FoML.ToFoML

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {𝒳 : Type*}
variable {n : ℕ} {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/-! ### Definitions -/

/- @[blueprint "def:one-sided-deviation"
  (statement := /-- The one-sided uniform deviation of an indexed class $(f_i)_{i}$ on the sample
    $S = (x_1,\dots,x_n)$: $\Delta^+_S(f) := \sup_i \bigl(\tfrac1n \sum_k f_i(x_k)
    - \mathbb E f_i(X)\bigr)$ (empirical mean minus population mean, no absolute value). -/)] -/
noncomputable def oneSidedDeviation (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳)
    (S : Fin n → 𝒳) : ℝ :=
  ⨆ i, ((n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')])

/- @[blueprint "def:rademacher-without-abs"
  (statement := /-- The population one-sided Rademacher complexity
    $\mathfrak R_n(f) := \mathbb E_{S \sim \mu^{\otimes n}} \hat{\mathfrak R}_S(f)$, where
    $\hat{\mathfrak R}_S(f) = \mathbb E_\sigma \sup_i \tfrac1n \sum_k \sigma_k f_i(x_k)$ is the
    one-sided empirical complexity (FoML's
    \texttt{empiricalRademacherComplexity\_without\_abs}). -/)] -/
noncomputable def rademacherComplexity_without_abs (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω)
    (X : Ω → 𝒳) : ℝ :=
  (Measure.pi fun _ : Fin n ↦ μ)[fun ω : Fin n → Ω ↦
    empiricalRademacherComplexity_without_abs n f (X ∘ ω)]

/-! ### Elementary bounds -/

section Elementary

omit [MeasurableSpace Ω] in
lemma abs_signed_sum_le {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b) (S : Fin n → 𝒳) (σ : Signs n)
    (i : ι) : |∑ k : Fin n, (σ k : ℝ) * f i (S k)| ≤ n * b := by
  calc |∑ k : Fin n, (σ k : ℝ) * f i (S k)| ≤ ∑ k : Fin n, |(σ k : ℝ) * f i (S k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |f i (S k)| := by
        simp only [Int.reduceNeg, abs_mul, Signs.apply_abs', one_mul]
    _ ≤ ∑ _k : Fin n, b := Finset.sum_le_sum fun k _ ↦ hf' i (S k)
    _ = n * b := by simp

omit [MeasurableSpace Ω] in
lemma bddAbove_range_signed_sum {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b) (S : Fin n → 𝒳)
    (σ : Signs n) : BddAbove (Set.range fun i ↦ ∑ k : Fin n, (σ k : ℝ) * f i (S k)) :=
  ⟨n * b, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (abs_signed_sum_le hf' S σ i)⟩

/- Averaging over the sign patterns preserves a uniform bound. -/
lemma abs_card_inv_mul_sum_le {M : ℝ} (g : Signs n → ℝ) (hg : ∀ σ, |g σ| ≤ M) :
    |(Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ, g σ| ≤ M := by
  have hcard : (0 : ℝ) < Fintype.card (Signs n) := by rw [Signs.card]; positivity
  rw [abs_mul, abs_of_pos (inv_pos.mpr hcard)]
  calc (Fintype.card (Signs n) : ℝ)⁻¹ * |∑ σ, g σ|
      ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ, |g σ| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ _σ : Signs n, M := by
        gcongr with σ; exact hg σ
    _ = M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard.ne']

/- A measurable function bounded in absolute value is integrable for a finite measure. -/
lemma integrable_of_measurable_of_abs_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {g : α → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ a, |g a| ≤ C) :
    Integrable g ν :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun a ↦ by simpa [Real.norm_eq_abs] using hC a)

/- The supremum of the integrals of a countable, uniformly bounded family is at most the
integral of the supremum. -/
lemma ciSup_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    [Nonempty ι] [Countable ι] (g : ι → α → ℝ) (hg : ∀ i, Measurable (g i)) {C : ℝ}
    (hC : ∀ i a, |g i a| ≤ C) : ⨆ i, ∫ a, g i a ∂ν ≤ ∫ a, ⨆ i, g i a ∂ν := by
  refine ciSup_le fun i ↦ integral_mono (integrable_of_measurable_of_abs_le (hg i) (hC i))
    (integrable_of_measurable_of_abs_le (Measurable.iSup hg) fun a ↦ abs_iSup_le fun j ↦ hC j a)
    fun a ↦ le_ciSup (f := fun j ↦ g j a) ⟨C, ?_⟩ i
  rintro _ ⟨j, rfl⟩
  exact (le_abs_self _).trans (hC j a)

lemma negSigns_apply_coe (σ : Signs n) (k : Fin n) :
    ((negSigns σ k : ℤ) : ℝ) = -((σ k : ℤ) : ℝ) := by
  have : (negSigns σ k : ℤ) = -(σ k : ℤ) := rfl
  rw [this]; push_cast; ring

/- Sums over sign patterns are invariant under negation of the patterns. -/
lemma sum_signs_neg_eq (g : Signs n → ℝ) : ∑ σ : Signs n, g (negSigns σ) = ∑ σ, g σ :=
  Function.Bijective.sum_comp negSigns_involutive.bijective g

end Elementary

/-! ### One-sided symmetrization -/

section Symmetrization

variable [IsProbabilityMeasure μ] {X : Ω → 𝒳}

/- Measurability of the unnormalized one-sided Rademacher average on a random sample. -/
lemma measurable_signedSup [Countable ι] (hf : ∀ i, Measurable (f i ∘ X)) :
    Measurable fun ω : Fin n → Ω ↦
      (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k)) :=
  measurable_const.mul (Finset.measurable_sum _ fun _ _ ↦ Measurable.iSup fun i ↦
    Finset.measurable_sum _ fun k _ ↦ measurable_const.mul ((hf i).comp (measurable_pi_apply k)))

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma abs_signedSup_le [Nonempty ι] {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b) (S : Fin n → 𝒳) :
    |(Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (S k)|
      ≤ n * b :=
  abs_card_inv_mul_sum_le _ fun σ ↦ abs_iSup_le fun i ↦ abs_signed_sum_le hf' S σ i

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/- @[blueprint "lem:one-sided-signed-sup-split"
  (statement := /-- For two samples $S, T$ and a class bounded by $b$,
    $\mathbb E_\sigma \sup_i \sum_k \sigma_k (f_i(x_k) - f_i(x'_k))
    \le \mathbb E_\sigma \sup_i \sum_k \sigma_k f_i(x_k)
    + \mathbb E_\sigma \sup_i \sum_k \sigma_k f_i(x'_k)$
    (split the supremum and use the symmetry $\sigma \mapsto -\sigma$). -/)] -/
lemma signed_sup_sub_le [Nonempty ι] {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b) (S T : Fin n → 𝒳) :
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * (f i (S k) - f i (T k)) ≤
      ((Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (S k)) +
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (T k) := by
  have hneg : ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (T k) =
      ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (negSigns σ k : ℝ) * f i (T k) :=
    (sum_signs_neg_eq fun σ ↦ ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (T k)).symm
  have hsplit : ∀ (σ : Signs n) (i : ι), ∑ k : Fin n, (σ k : ℝ) * (f i (S k) - f i (T k)) =
      ∑ k : Fin n, (σ k : ℝ) * f i (S k) + ∑ k : Fin n, (negSigns σ k : ℝ) * f i (T k) := by
    intro σ i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [negSigns_apply_coe]; ring
  calc (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * (f i (S k) - f i (T k))
      ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ((⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (S k)) +
          ⨆ i, ∑ k : Fin n, (negSigns σ k : ℝ) * f i (T k)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ ↦ ?_) (by positivity)
        simp_rw [hsplit σ]
        exact ciSup_add_le_add_ciSup (bddAbove_range_signed_sum hf' S σ)
          (bddAbove_range_signed_sum hf' T (negSigns σ))
    _ = _ := by simp only [Finset.sum_add_distrib, mul_add, hneg]

/- Fubini for the product-of-pairs measure: an integral over `Fin n → Ω × Ω` w.r.t.
`Measure.pi (fun _ ↦ μ.prod μ)` is an iterated integral over two independent samples. -/
lemma integral_pi_prod_eq (Ψ : (Fin n → Ω × Ω) → ℝ) (hΨ : Measurable Ψ) {C : ℝ}
    (hC : ∀ ω, |Ψ ω| ≤ C) :
    (Measure.pi fun _ : Fin n ↦ μ.prod μ)[Ψ] =
      μⁿ[fun ω : Fin n → Ω ↦ μⁿ[fun ω' : Fin n → Ω ↦ Ψ (fun k ↦ (ω k, ω' k))]] := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  have mp := measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) (fun _ ↦ μ) (fun _ ↦ μ)
  let F : (Fin n → Ω) × (Fin n → Ω) → ℝ := fun p ↦ Ψ (fun k ↦ (p.1 k, p.2 k))
  have hF : Measurable F := hΨ.comp e.symm.measurable
  have hFint : Integrable F (μⁿ.prod μⁿ) := integrable_of_measurable_of_abs_le hF fun p ↦ hC _
  calc (Measure.pi fun _ : Fin n ↦ μ.prod μ)[Ψ]
      = ∫ ω, F (e ω) ∂(Measure.pi fun _ : Fin n ↦ μ.prod μ) := rfl
    _ = (μⁿ.prod μⁿ)[F] := mp.integral_comp e.measurableEmbedding F
    _ = _ := integral_prod F hFint

/- @[blueprint "lem:one-sided-symmetrization-unnormalized"
  (statement := /-- \textbf{One-sided symmetrization (unnormalized).} Let $(f_i)_{i \in I}$ be a
    countable family of measurable functions with $|f_i| \le b$ and $X_1,\dots,X_n \sim \mu$
    i.i.d. Then
    $$\mathbb E \sup_i \Bigl(\sum_k f_i(X_k) - n\,\mathbb E f_i(X)\Bigr)
    \le 2\, \mathbb E\, \mathbb E_\sigma \sup_i \sum_k \sigma_k f_i(X_k).$$
    Proof: introduce an independent copy $X'$, write $n \mathbb E f_i = \mathbb E' \sum_k
    f_i(X'_k)$, pull the supremum inside the inner expectation, apply FoML's (no-absolute-value)
    symmetrization identity \texttt{symmetrization\_equation}, split the supremum
    (\texttt{lem:one-sided-signed-sup-split}) and integrate. -/)] -/
theorem expectation_sup_sum_sub_le [Nonempty ι] [Countable ι] (hf : ∀ i, Measurable (f i ∘ X))
    {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b) :
    μⁿ[fun ω : Fin n → Ω ↦ ⨆ i, (∑ k : Fin n, f i (X (ω k)) - n • μ[fun ω' ↦ f i (X ω')])] ≤
      2 * μⁿ[fun ω : Fin n → Ω ↦
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))] := by
  classical
  have hcard : (Fintype.card (Signs n) : ℝ)⁻¹ = (2 : ℝ)⁻¹ ^ n := by
    rw [Signs.card]; push_cast; rw [inv_pow]
  -- the difference sums and their bounds
  have hDb : ∀ (i : ι) (ω ω' : Fin n → Ω),
      |∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))| ≤ n * (b + b) :=
    fun i ω ω' ↦ bounded_difference_of_bounded hf' ω i ω'
  have hDm : ∀ i : ι, Measurable fun p : (Fin n → Ω) × (Fin n → Ω) ↦
      ∑ k : Fin n, (f i (X (p.1 k)) - f i (X (p.2 k))) := fun i ↦
    Finset.measurable_sum _ fun k _ ↦
      ((hf i).comp ((measurable_pi_apply k).comp measurable_fst)).sub
        ((hf i).comp ((measurable_pi_apply k).comp measurable_snd))
  -- Step A: `n 𝔼 f_i = 𝔼' ∑_k f_i(X'_k)`
  have hA1 : ∀ (ω : Fin n → Ω) (i : ι),
      ∑ k : Fin n, f i (X (ω k)) - n • μ[fun ω' ↦ f i (X ω')] =
        μⁿ[fun ω' : Fin n → Ω ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))] := by
    intro ω i
    rw [integral_sum_sub_eq_sum_sub_integral hf hf' ω i]
    have hk : ∀ k : Fin n, μⁿ[fun ω' : Fin n → Ω ↦ f i (X (ω' k))] = μ[fun ω' ↦ f i (X ω')] := by
      intro k
      have hmap : (μⁿ).map (fun ω : Fin n → Ω ↦ ω k) = μ := pi_map_eval (μ := fun _ : Fin n ↦ μ) k
      have := integral_map (μ := μⁿ) (measurable_pi_apply k).aemeasurable
        (f := fun y ↦ f i (X y)) (by rw [hmap]; exact (hf i).aestronglyMeasurable)
      rw [hmap] at this
      exact this.symm
    simp only [hk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Step B: pull the supremum inside the inner expectation
  have hB : μⁿ[fun ω : Fin n → Ω ↦ ⨆ i,
        μⁿ[fun ω' : Fin n → Ω ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))]] ≤
      μⁿ[fun ω : Fin n → Ω ↦
        μⁿ[fun ω' : Fin n → Ω ↦ ⨆ i, ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))]] := by
    refine integral_mono ?_ ?_ fun ω ↦ ?_
    · refine integrable_of_measurable_of_abs_le ?_ (C := n * (b + b)) fun ω ↦
        abs_iSup_le fun i ↦ abs_expectation_le_of_abs_le_const
          (Filter.Eventually.of_forall fun ω' ↦ hDb i ω ω')
      exact Measurable.iSup fun i ↦ (hDm i).stronglyMeasurable.integral_prod_right'.measurable
    · refine integrable_of_measurable_of_abs_le ?_ (C := n * (b + b)) fun ω ↦
        abs_expectation_le_of_abs_le_const
          (Filter.Eventually.of_forall fun ω' ↦ abs_iSup_le fun i ↦ hDb i ω ω')
      have hm : Measurable fun p : (Fin n → Ω) × (Fin n → Ω) ↦
          ⨆ i, ∑ k : Fin n, (f i (X (p.1 k)) - f i (X (p.2 k))) := Measurable.iSup hDm
      exact hm.stronglyMeasurable.integral_prod_right'.measurable
    · exact ciSup_integral_le (ν := μⁿ) (fun i ω' ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k))))
        (fun i ↦ (hDm i).comp measurable_prodMk_left) (fun i ω' ↦ hDb i ω ω')
  -- Step C: the product-of-pairs measure
  have hC : μⁿ[fun ω : Fin n → Ω ↦
        μⁿ[fun ω' : Fin n → Ω ↦ ⨆ i, ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))]] =
      (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        ⨆ i, ∑ k : Fin n, (f i (X (ω k).1) - f i (X (ω k).2))] :=
    (integral_pi_prod_eq (fun ω : Fin n → Ω × Ω ↦
        ⨆ i, ∑ k : Fin n, (f i (X (ω k).1) - f i (X (ω k).2)))
      (Measurable.iSup fun i ↦ Finset.measurable_sum _ fun k _ ↦
        ((hf i).comp (measurable_fst.comp (measurable_pi_apply k))).sub
          ((hf i).comp (measurable_snd.comp (measurable_pi_apply k))))
      (C := n * (b + b)) (fun ω ↦ abs_iSup_le fun i ↦ bound_lem hf' ω i)).symm
  -- Step D: FoML's symmetrization identity (no absolute values)
  have hD : (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        ⨆ i, ∑ k : Fin n, (f i (X (ω k).1) - f i (X (ω k).2))] =
      (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * (f i (X (ω k).1) - f i (X (ω k).2))] := by
    rw [symmetrization_equation hf hf', hcard]
  -- Step E: split the supremum
  have hE : (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * (f i (X (ω k).1) - f i (X (ω k).2))] ≤
      (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).1)) +
          (Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).2)] := by
    refine integral_mono ?_ ?_ fun ω ↦ signed_sup_sub_le hf' _ _
    · refine integrable_of_measurable_of_abs_le ?_ (C := n * (b + b)) fun ω ↦
        abs_card_inv_mul_sum_le _ fun σ ↦ abs_iSup_le fun i ↦ bound_lem' hf' ω i σ
      exact measurable_const.mul (Finset.measurable_sum _ fun σ _ ↦ Measurable.iSup fun i ↦
        Finset.measurable_sum _ fun k _ ↦ measurable_const.mul
          (((hf i).comp (measurable_fst.comp (measurable_pi_apply k))).sub
            ((hf i).comp (measurable_snd.comp (measurable_pi_apply k)))))
    · refine Integrable.add ?_ ?_
      · refine integrable_of_measurable_of_abs_le ?_ (C := n * b)
          fun ω ↦ abs_signedSup_le hf' fun k ↦ X (ω k).1
        exact (measurable_signedSup hf).comp
          (measurable_pi_lambda _ fun k ↦ measurable_fst.comp (measurable_pi_apply k))
      · refine integrable_of_measurable_of_abs_le ?_ (C := n * b)
          fun ω ↦ abs_signedSup_le hf' fun k ↦ X (ω k).2
        exact (measurable_signedSup hf).comp
          (measurable_pi_lambda _ fun k ↦ measurable_snd.comp (measurable_pi_apply k))
  -- Step F: integrate out the two samples
  have hF : (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).1)) +
          (Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k).2)] =
      2 * μⁿ[fun ω : Fin n → Ω ↦
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))] := by
    set A : (Fin n → Ω) → ℝ := fun ω ↦
      (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))
      with hA
    have hAm : Measurable A := measurable_signedSup hf
    have hAb : ∀ ω, |A ω| ≤ n * b := fun ω ↦ abs_signedSup_le hf' (X ∘ ω)
    have hAint : Integrable A μⁿ := integrable_of_measurable_of_abs_le hAm hAb
    have h1 : (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        A (fun k ↦ (ω k).1) + A (fun k ↦ (ω k).2)] =
        μⁿ[fun ω : Fin n → Ω ↦ μⁿ[fun ω' : Fin n → Ω ↦ A ω + A ω']] :=
      integral_pi_prod_eq _
        ((hAm.comp (measurable_pi_lambda _ fun k ↦ measurable_fst.comp (measurable_pi_apply k))).add
          (hAm.comp (measurable_pi_lambda _ fun k ↦ measurable_snd.comp (measurable_pi_apply k))))
        (C := n * b + n * b) fun ω ↦ (abs_add_le _ _).trans (add_le_add (hAb _) (hAb _))
    have h2 : ∀ ω, μⁿ[fun ω' : Fin n → Ω ↦ A ω + A ω'] = A ω + μⁿ[A] := fun ω ↦ by
      rw [integral_add (integrable_const _) hAint]; simp
    change (Measure.pi fun _ : Fin n ↦ μ.prod μ)[fun ω : Fin n → Ω × Ω ↦
        A (fun k ↦ (ω k).1) + A (fun k ↦ (ω k).2)] = 2 * μⁿ[A]
    rw [h1]
    simp_rw [h2]
    rw [integral_add hAint (integrable_const _)]; simp; ring
  calc μⁿ[fun ω : Fin n → Ω ↦ ⨆ i, (∑ k : Fin n, f i (X (ω k)) - n • μ[fun ω' ↦ f i (X ω')])]
      = μⁿ[fun ω : Fin n → Ω ↦ ⨆ i,
          μⁿ[fun ω' : Fin n → Ω ↦ ∑ k : Fin n, (f i (X (ω k)) - f i (X (ω' k)))]] := by
        congr 1; funext ω; exact iSup_congr fun i ↦ hA1 ω i
    _ ≤ _ := hB
    _ = _ := hC
    _ = _ := hD
    _ ≤ _ := hE
    _ = _ := hF

/- @[blueprint "lem:one-sided-symmetrization"
  (statement := /-- \textbf{One-sided symmetrization.} Let $n \ge 1$, $(f_i)_{i \in I}$ be a
    countable family of measurable functions with $|f_i| \le b$ and $X_1,\dots,X_n \sim \mu$
    i.i.d. Then
    $$\mathbb E_S \sup_i \Bigl(\tfrac1n \sum_k f_i(X_k) - \mathbb E f_i(X)\Bigr)
    \le 2\, \mathfrak R_n(f),$$
    where $\mathfrak R_n(f) = \mathbb E_S \mathbb E_\sigma \sup_i \tfrac1n \sum_k \sigma_k f_i(X_k)$
    is the one-sided Rademacher complexity. -/)] -/
theorem oneSidedDeviation_expectation_le_two_mul_rademacher [Nonempty ι] [Countable ι]
    (hn : 0 < n) (X : Ω → 𝒳) (hf : ∀ i, Measurable (f i ∘ X)) {b : ℝ}
    (hf' : ∀ i z, |f i z| ≤ b) :
    μⁿ[fun ω : Fin n → Ω ↦ oneSidedDeviation n f μ X (X ∘ ω)] ≤
      2 * rademacherComplexity_without_abs n f μ X := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (fun ω : Fin n → Ω ↦ oneSidedDeviation n f μ X (X ∘ ω)) = fun ω ↦
      (n : ℝ)⁻¹ * ⨆ i, (∑ k : Fin n, f i (X (ω k)) - n • μ[fun ω' ↦ f i (X ω')]) := by
    funext ω
    unfold oneSidedDeviation
    rw [Real.mul_iSup_of_nonneg (by positivity)]
    refine iSup_congr fun i ↦ ?_
    simp only [Function.comp_apply, nsmul_eq_mul, mul_sub]
    rw [← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  have h2 : (fun ω : Fin n → Ω ↦ empiricalRademacherComplexity_without_abs n f (X ∘ ω)) =
      fun ω ↦ (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))) := by
    funext ω
    unfold empiricalRademacherComplexity_without_abs
    calc (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i ((X ∘ ω) k)
        = (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, (n : ℝ)⁻¹ * ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k)) := by
          congr 1
          refine Finset.sum_congr rfl fun σ _ ↦ ?_
          rw [Real.mul_iSup_of_nonneg (by positivity)]
          rfl
      _ = _ := by rw [← Finset.mul_sum, mul_left_comm]
  rw [h1, integral_const_mul]
  unfold rademacherComplexity_without_abs
  rw [h2, integral_const_mul]
  have := expectation_sup_sum_sub_le (μ := μ) (n := n) hf hf'
  calc (n : ℝ)⁻¹ * μⁿ[fun ω : Fin n → Ω ↦
          ⨆ i, (∑ k : Fin n, f i (X (ω k)) - n • μ[fun ω' ↦ f i (X ω')])]
      ≤ (n : ℝ)⁻¹ * (2 * μⁿ[fun ω : Fin n → Ω ↦ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ i, ∑ k : Fin n, (σ k : ℝ) * f i (X (ω k))]) := by gcongr
    _ = _ := by ring

end Symmetrization

/-! ### Bounded differences and McDiarmid -/

section Concentration

variable [IsProbabilityMeasure μ]

lemma abs_oneSidedDeviation_term_le (hn : 0 < n) (X : Ω → 𝒳) {b : ℝ}
    (hf' : ∀ i z, |f i z| ≤ b) (S : Fin n → 𝒳) (i : ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')]| ≤ b + b := by
  have h1 : |(n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k)| ≤ b :=
    abs_normalized_fin_sum_le hn (fun _ x ↦ f i x) S (fun _ x ↦ hf' i x)
  have h2 : |μ[fun ω' ↦ f i (X ω')]| ≤ b :=
    abs_expectation_le_of_abs_le_const (Filter.Eventually.of_forall fun ω' ↦ hf' i (X ω'))
  exact (abs_sub _ _).trans (add_le_add h1 h2)

lemma bddAbove_range_oneSidedDeviation_term (hn : 0 < n) (X : Ω → 𝒳) {b : ℝ}
    (hf' : ∀ i z, |f i z| ≤ b) (S : Fin n → 𝒳) :
    BddAbove (Set.range fun i ↦ (n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')]) :=
  ⟨b + b, by
    rintro _ ⟨i, rfl⟩
    exact (le_abs_self _).trans (abs_oneSidedDeviation_term_le hn X hf' S i)⟩

/- Each one-sided risk deviation is at most the one-sided uniform deviation. -/
lemma le_oneSidedDeviation (hn : 0 < n) (X : Ω → 𝒳) {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b)
    (S : Fin n → 𝒳) (i : ι) :
    (n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')] ≤ oneSidedDeviation n f μ X S :=
  le_ciSup (bddAbove_range_oneSidedDeviation_term hn X hf' S) i

/- @[blueprint "lem:one-sided-bounded-difference"
  (statement := /-- Replacing one observation changes the one-sided uniform deviation of a class
    bounded by $b$ by at most $2b/n$. -/)] -/
theorem oneSidedDeviation_bounded_difference [Nonempty ι] (hn : 0 < n) (X : Ω → 𝒳) {b : ℝ}
    (hf' : ∀ i z, |f i z| ≤ b) (j : Fin n) (S : Fin n → 𝒳) (x' : 𝒳) :
    |oneSidedDeviation n f μ X S - oneSidedDeviation n f μ X (Function.update S j x')| ≤
      (n : ℝ)⁻¹ * 2 * b := by
  unfold oneSidedDeviation
  refine abs_ciSup_sub_ciSup_le (bddAbove_range_oneSidedDeviation_term hn X hf' S)
    (bddAbove_range_oneSidedDeviation_term hn X hf' _) fun i ↦ ?_
  rw [sub_sub_sub_cancel_right]
  exact abs_normalized_fin_sum_update_sub_le hn (fun _ x ↦ f i x) (fun _ x ↦ hf' i x) j S x'

omit [IsProbabilityMeasure μ] in
theorem oneSidedDeviation_measurable [Countable ι] [MeasurableSpace 𝒳] (X : Ω → 𝒳)
    (hf : ∀ i, Measurable (f i)) : Measurable (oneSidedDeviation n f μ X) :=
  .iSup fun i ↦ (measurable_const.mul (Finset.univ.measurable_sum fun j _ ↦
    (hf i).comp (measurable_pi_apply j))).sub_const _

/- The scaling identity used to feed the bounded-difference constant `2b/n` to McDiarmid. -/
lemma mcdiarmid_scale (hn : 0 < n) {b t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2) :
    ((n : ℝ) * t / 2) * (n : ℝ) * ((n : ℝ)⁻¹ * 2 * b) ^ 2 ≤ 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : ((n : ℝ) * t / 2) * (n : ℝ) * ((n : ℝ)⁻¹ * 2 * b) ^ 2 = 2 * (t * b ^ 2) := by
    field_simp
  rw [this]; linarith

/- @[blueprint "lem:one-sided-mcdiarmid"
  (statement := /-- \textbf{McDiarmid for the one-sided deviation.} For a countable class of
    measurable functions bounded by $b$, $t b^2 \le 1/2$ and $\varepsilon \ge 0$,
    $$\mathbb P\bigl(\Delta^+_S(f) - \mathbb E \Delta^+_S(f) \ge \varepsilon\bigr)
    \le \exp(-\varepsilon^2 t n).$$ -/)] -/
theorem oneSidedDeviation_mcdiarmid_tail [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [Countable ι] {X : Ω → 𝒳} (hX : Measurable X) (hf : ∀ i, Measurable (f i)) {b : ℝ}
    (hf' : ∀ i x, |f i x| ≤ b) {t : ℝ} (ht : t * b ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω | oneSidedDeviation n f μ X (X ∘ ω) -
        μⁿ[fun ω : Fin n → Ω ↦ oneSidedDeviation n f μ X (X ∘ ω)] ≥ ε}).toReal ≤
      (-ε ^ 2 * t * n).exp := by
  by_cases hn : n = 0
  · simp [hn, ← measureReal_def]
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  calc _ ≤ (-2 * ε ^ 2 * (n * t / 2)).exp :=
        mcdiarmid_inequality_pos_iid_of_const hX
          (oneSidedDeviation_bounded_difference hn X hf')
          (oneSidedDeviation_measurable X hf) hε
          (by simpa using mcdiarmid_scale hn ht)
    _ = _ := congr_arg _ (by ring)

omit [IsProbabilityMeasure μ] in
/- @[blueprint "lem:rademacher-without-abs-bounded-difference"
  (statement := /-- Replacing one observation changes the one-sided empirical Rademacher
    complexity of a class bounded by $b$ by at most $2b/n$. -/)] -/
theorem empiricalRademacherComplexity_without_abs_bounded_difference [Nonempty ι] (hn : 0 < n)
    {b : ℝ} (hf' : ∀ i z, |f i z| ≤ b) (j : Fin n) (S : Fin n → 𝒳) (x' : 𝒳) :
    |empiricalRademacherComplexity_without_abs n f S -
        empiricalRademacherComplexity_without_abs n f (Function.update S j x')| ≤
      (n : ℝ)⁻¹ * 2 * b := by
  have hnorm : ∀ (T : Fin n → 𝒳) (σ : Signs n) (i : ι),
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (T k)| ≤ b := fun T σ i ↦
    abs_normalized_fin_sum_le hn (fun k x ↦ (σ k : ℝ) * f i x) T
      (fun k x ↦ by simpa [abs_mul, abs_sigma] using hf' i x)
  have hpoint : ∀ (σ : Signs n) (i : ι),
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k) -
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (Function.update S j x' k)| ≤
      (n : ℝ)⁻¹ * 2 * b := fun σ i ↦
    abs_normalized_fin_sum_update_sub_le hn (fun k x ↦ (σ k : ℝ) * f i x)
      (fun k x ↦ by simpa [abs_mul, abs_sigma] using hf' i x) j S x'
  have hsup : ∀ σ : Signs n,
      |(⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)) -
        ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (Function.update S j x' k)| ≤
      (n : ℝ)⁻¹ * 2 * b := fun σ ↦
    abs_ciSup_sub_ciSup_le
      ⟨b, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hnorm S σ i)⟩
      ⟨b, by rintro _ ⟨i, rfl⟩; exact (le_abs_self _).trans (hnorm _ σ i)⟩ (hpoint σ)
  unfold empiricalRademacherComplexity_without_abs
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact abs_card_inv_mul_sum_le _ hsup

omit [IsProbabilityMeasure μ] in
theorem measurable_empiricalRademacherComplexity_without_abs_comp [Countable ι] {X : Ω → 𝒳}
    (hf : ∀ i, Measurable (f i ∘ X)) :
    Measurable fun ω : Fin n → Ω ↦ empiricalRademacherComplexity_without_abs n f (X ∘ ω) := by
  unfold empiricalRademacherComplexity_without_abs
  exact measurable_const.mul (Finset.measurable_sum _ fun σ _ ↦ Measurable.iSup fun i ↦
    measurable_const.mul (Finset.measurable_sum _ fun k _ ↦
      measurable_const.mul ((hf i).comp (measurable_pi_apply k))))

/- @[blueprint "lem:rademacher-without-abs-lower-tail"
  (statement := /-- \textbf{Lower tail of the one-sided empirical Rademacher complexity.} For a
    countable class of measurable functions bounded by $b > 0$ and $\varepsilon \ge 0$,
    $\mathbb P\bigl(\hat{\mathfrak R}_S(f) \le \mathfrak R_n(f) - \varepsilon\bigr)
    \le \exp(-n\varepsilon^2/(2b^2))$. -/)] -/
theorem empiricalRademacherComplexity_without_abs_lower_tail_countable_of_pos
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι] (f : ι → 𝒳 → ℝ)
    (hf : ∀ i, Measurable (f i)) (X : Ω → 𝒳) (hX : Measurable X) {b : ℝ} (hb : 0 < b)
    (hf' : ∀ i x, |f i x| ≤ b) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω | empiricalRademacherComplexity_without_abs n f (X ∘ ω) -
        rademacherComplexity_without_abs n f μ X ≤ -ε}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  by_cases hn : n = 0
  · simp [hn, ← measureReal_def]
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have ht : (1 / (2 * b ^ 2)) * b ^ 2 ≤ 1 / 2 := le_of_eq (by field_simp)
  have key := mcdiarmid_inequality_neg_iid_of_const (μ := μ) (ι := Fin n) (X' := X)
    (f' := fun S : Fin n → 𝒳 ↦ empiricalRademacherComplexity_without_abs n f S)
    (c := (n : ℝ)⁻¹ * 2 * b) hX
    (empiricalRademacherComplexity_without_abs_bounded_difference (n := n) (f := f) hn hf')
    (measurable_empiricalRademacherComplexity_without_abs_comp (Ω := 𝒳) (n := n) (f := f)
      (X := id) (fun i ↦ by simpa using hf i))
    hε (t := n * (1 / (2 * b ^ 2)) / 2) (by simpa using mcdiarmid_scale hn ht)
  calc _ ≤ (-2 * ε ^ 2 * (n * (1 / (2 * b ^ 2)) / 2)).exp := key
    _ = _ := by congr 1; ring

/-! ### Tail bounds for countable classes -/

/- @[blueprint "lem:one-sided-tail-countable"
  (statement := /-- \textbf{One-sided tail bound, countable class.} For a countable class of
    measurable functions bounded by $b > 0$ and $\varepsilon \ge 0$,
    $$\mathbb P\Bigl(\sup_i \bigl(\tfrac1n \textstyle\sum_k f_i(X_k) - \mathbb E f_i\bigr)
    \ge 2 \mathfrak R_n(f) + \varepsilon\Bigr) \le \exp\bigl(-n\varepsilon^2/(2b^2)\bigr).$$
    (Symmetrization \texttt{lem:one-sided-symmetrization} and McDiarmid
    \texttt{lem:one-sided-mcdiarmid} with $t = 1/(2b^2)$.) -/)] -/
theorem oneSidedDeviation_tail_bound_countable_of_pos [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Nonempty ι] [Countable ι] (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i)) (X : Ω → 𝒳)
    (hX : Measurable X) {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b) {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω | 2 * rademacherComplexity_without_abs n f μ X + ε ≤
        oneSidedDeviation n f μ X (X ∘ ω)}).toReal ≤ (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  by_cases hn : n = 0
  · simp [hn, ← measureReal_def]
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have ht : (1 / (2 * b ^ 2)) * b ^ 2 ≤ 1 / 2 := le_of_eq (by field_simp)
  have htail := oneSidedDeviation_mcdiarmid_tail (μ := μ) (n := n) hX hf hf' ht hε
  have hexp : (-ε ^ 2 * (1 / (2 * b ^ 2)) * n) = -ε ^ 2 * n / (2 * b ^ 2) := by ring
  rw [hexp] at htail
  exact measureReal_superlevel_le_of_centered
    (oneSidedDeviation_expectation_le_two_mul_rademacher hn X (fun i ↦ (hf i).comp hX) hf') htail

/- @[blueprint "lem:one-sided-tail-empirical-countable"
  (statement := /-- \textbf{One-sided tail bound with the observed complexity, countable class.}
    Under the hypotheses of \texttt{lem:one-sided-tail-countable},
    $$\mathbb P\Bigl(\sup_i \bigl(\tfrac1n \textstyle\sum_k f_i(X_k) - \mathbb E f_i\bigr)
    \ge 2 \hat{\mathfrak R}_S(f) + 3\varepsilon\Bigr) \le 2\exp\bigl(-n\varepsilon^2/(2b^2)\bigr)$$
    (union bound with the lower tail \texttt{lem:rademacher-without-abs-lower-tail}). -/)] -/
theorem oneSidedDeviation_tail_bound_countable_of_empirical_complexity [MeasurableSpace 𝒳]
    [Nonempty 𝒳] [Nonempty ι] [Countable ι] (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X) {b : ℝ} (hb : 0 < b) (hf' : ∀ i x, |f i x| ≤ b) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω | 2 * empiricalRademacherComplexity_without_abs n f (X ∘ ω) + 3 * ε ≤
        oneSidedDeviation n f μ X (X ∘ ω)}).toReal ≤ 2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  set A : Set (Fin n → Ω) := {ω | 2 * rademacherComplexity_without_abs n f μ X + ε ≤
    oneSidedDeviation n f μ X (X ∘ ω)} with hA
  set B : Set (Fin n → Ω) := {ω | empiricalRademacherComplexity_without_abs n f (X ∘ ω) -
    rademacherComplexity_without_abs n f μ X ≤ -ε} with hB
  have hsubset : {ω : Fin n → Ω |
      2 * empiricalRademacherComplexity_without_abs n f (X ∘ ω) + 3 * ε ≤
        oneSidedDeviation n f μ X (X ∘ ω)} ⊆ A ∪ B := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, hA, hB]
    by_cases hA' : 2 * rademacherComplexity_without_abs n f μ X + ε ≤
        oneSidedDeviation n f μ X (X ∘ ω)
    · exact Or.inl hA'
    · right; linarith [not_le.mp hA']
  calc _ ≤ (μⁿ).real (A ∪ B) := measureReal_mono hsubset
    _ ≤ (μⁿ).real A + (μⁿ).real B := measureReal_union_le A B
    _ ≤ (-ε ^ 2 * n / (2 * b ^ 2)).exp + (-ε ^ 2 * n / (2 * b ^ 2)).exp :=
        add_le_add
          (oneSidedDeviation_tail_bound_countable_of_pos (μ := μ) f hf X hX hb hf' hε)
          (empiricalRademacherComplexity_without_abs_lower_tail_countable_of_pos (μ := μ)
            f hf X hX hb hf' hε)
    _ = _ := by ring

theorem oneSidedDeviation_tail_bound_countable_of_sample_empirical_le [MeasurableSpace 𝒳]
    [Nonempty 𝒳] [Nonempty ι] [Countable ι] (f : ι → 𝒳 → ℝ) (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X) (C : (Fin n → 𝒳) → ℝ) {b : ℝ} (hb : 0 < b)
    (hf' : ∀ i x, |f i x| ≤ b)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity_without_abs n f S ≤ C S) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (μⁿ {ω : Fin n → Ω | 2 * C (X ∘ ω) + 3 * ε ≤ oneSidedDeviation n f μ X (X ∘ ω)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc _ ≤ (μⁿ {ω : Fin n → Ω |
        2 * empiricalRademacherComplexity_without_abs n f (X ∘ ω) + 3 * ε ≤
          oneSidedDeviation n f μ X (X ∘ ω)}).toReal := by
        apply measureReal_superlevel_mono
        intro ω
        gcongr
        exact hC (X ∘ ω)
    _ ≤ _ := oneSidedDeviation_tail_bound_countable_of_empirical_complexity (μ := μ) f hf X hX
        hb hf' hε

end Concentration

/-! ### Separable classes -/

section Separable

variable {H : Type*} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma empiricalRademacherComplexity_without_abs_denseRestriction [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] (n : ℕ) {F : H → 𝒳 → ℝ}
    (hF : ∀ x : 𝒳, Continuous fun h ↦ F h x) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n F S =
      empiricalRademacherComplexity_without_abs n (denseRestriction F) S := by
  dsimp [empiricalRademacherComplexity_without_abs]
  congr
  ext σ
  apply separableSpaceSup_eq_real
  exact continuous_const.mul (continuous_finsetSum _ fun k _ ↦ continuous_const.mul (hF (S k)))

omit [IsProbabilityMeasure μ] in
lemma rademacherComplexity_without_abs_denseRestriction [Nonempty H] [TopologicalSpace H]
    [SeparableSpace H] (n : ℕ) (F : H → 𝒳 → ℝ) (hF : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (μ : Measure Ω) (X : Ω → 𝒳) :
    rademacherComplexity_without_abs n F μ X =
      rademacherComplexity_without_abs n (denseRestriction F) μ X := by
  dsimp [rademacherComplexity_without_abs]
  congr
  ext S
  exact empiricalRademacherComplexity_without_abs_denseRestriction n hF (X ∘ S)

omit [IsProbabilityMeasure μ] in
lemma oneSidedDeviation_denseRestriction [MeasurableSpace 𝒳] [Nonempty H] [TopologicalSpace H]
    [SeparableSpace H] [FirstCountableTopology H] (n : ℕ) (F : H → 𝒳 → ℝ)
    (hF_meas : ∀ h, Measurable (F h)) (X : Ω → 𝒳) (hX : Measurable X) {b : ℝ}
    (hF_bound : ∀ h x, |F h x| ≤ b) (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    oneSidedDeviation n F μ X = oneSidedDeviation n (denseRestriction F) μ X := by
  ext S
  dsimp [oneSidedDeviation]
  apply separableSpaceSup_eq_real
  apply Continuous.sub
  · exact continuous_const.mul (continuous_finsetSum _ fun k _ ↦ hF_cont (S k))
  · have hdominated : ∀ h : H, ∀ᵐ ω : Ω ∂μ, ‖F h (X ω)‖ ≤ b := by
      intro h
      filter_upwards with ω
      exact hF_bound h (X ω)
    apply MeasureTheory.continuous_of_dominated _ hdominated
    · exact MeasureTheory.integrable_const _
    · filter_upwards with ω
      exact hF_cont (X ω)
    · intro h
      exact ((hF_meas h).comp hX).aestronglyMeasurable

/- @[blueprint "lem:one-sided-tail-empirical"
  (statement := /-- \textbf{One-sided tail bound with the observed complexity, separable class.}
    Let $H$ be a nonempty separable first-countable topological space, $F : H \to (\mathcal X
    \to \mathbb R)$ with $|F_h| \le b$ ($b > 0$), $F_h$ measurable and $h \mapsto F_h(x)$
    continuous for every $x$, and let $C(S) \ge \hat{\mathfrak R}_S(F)$ for every sample $S$.
    Then for every $\varepsilon \ge 0$,
    $$\mathbb P_S\Bigl(\sup_h \bigl(\tfrac1n \textstyle\sum_k F_h(X_k) - \mathbb E F_h\bigr)
    \ge 2 C(S) + 3\varepsilon\Bigr) \le 2\exp\bigl(-n\varepsilon^2/(2b^2)\bigr).$$
    (Restrict to a countable dense sequence and apply
    \texttt{lem:one-sided-tail-empirical-countable}.) -/)] -/
theorem oneSidedDeviation_tail_bound_separable_of_sample_empirical_le [MeasurableSpace 𝒳]
    [Nonempty 𝒳] [Nonempty H] [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h)) (X : Ω → 𝒳) (hX : Measurable X)
    (C : (Fin n → 𝒳) → ℝ) {b : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity_without_abs n F S ≤ C S) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω | 2 * C (X ∘ S) + 3 * ε ≤ oneSidedDeviation n F μ X (X ∘ S)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  calc _ = (μⁿ {S : Fin n → Ω | 2 * C (X ∘ S) + 3 * ε ≤
        oneSidedDeviation n (denseRestriction F) μ X (X ∘ S)}).toReal := by
        congr
        ext S
        rw [oneSidedDeviation_denseRestriction n F hF_meas X hX hF_bound hF_cont μ]
    _ ≤ _ := by
        refine oneSidedDeviation_tail_bound_countable_of_sample_empirical_le (μ := μ)
          (denseRestriction F) (measurable_denseRestriction_apply hF_meas) X hX C hb
          (abs_denseRestriction_le hF_bound) (fun S ↦ ?_) hε
        rw [← empiricalRademacherComplexity_without_abs_denseRestriction n hF_cont S]
        exact hC S

/-! ### Two-sided deviation via the one-sided bound for `F` and `-F` -/

/- @[blueprint "lem:two-sided-tail-empirical"
  (statement := /-- \textbf{Two-sided deviation from the one-sided bound.} Under the hypotheses
    of \texttt{lem:one-sided-tail-empirical} with $n \ge 1$, assume moreover that
    $C(S) \ge \hat{\mathfrak R}_S(-F)$ for every sample $S$. Then for every
    $\varepsilon \ge 0$,
    $$\mathbb P_S\Bigl(\exists h,\ \bigl|\mathbb E F_h - \tfrac1n \textstyle\sum_k F_h(X_k)\bigr|
    > 2 C(S) + 3\varepsilon\Bigr) \le 4\exp\bigl(-n\varepsilon^2/(2b^2)\bigr).$$
    Proof: the event is contained in the union of the one-sided events for $F$ and for $-F$;
    each has probability at most $2\exp(-n\varepsilon^2/(2b^2))$. -/)] -/
theorem twoSided_deviation_tail_bound_separable_of_sample_empirical_le [MeasurableSpace 𝒳]
    [Nonempty 𝒳] [Nonempty H] [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    (hn : 0 < n) (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h)) (X : Ω → 𝒳)
    (hX : Measurable X) (C : (Fin n → 𝒳) → ℝ) {b : ℝ} (hb : 0 < b)
    (hF_bound : ∀ h x, |F h x| ≤ b) (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity_without_abs n F S ≤ C S)
    (hC' : ∀ S : Fin n → 𝒳,
      empiricalRademacherComplexity_without_abs n (fun h x ↦ -F h x) S ≤ C S)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω | ∃ h, 2 * C (X ∘ S) + 3 * ε <
        |μ[fun ω ↦ F h (X ω)] - (n : ℝ)⁻¹ * ∑ k : Fin n, F h (X (S k))|}).toReal ≤
      4 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  set G : H → 𝒳 → ℝ := fun h x ↦ -F h x with hG
  have hG_meas : ∀ h, Measurable (G h) := fun h ↦ (hF_meas h).neg
  have hG_bound : ∀ h x, |G h x| ≤ b := fun h x ↦ by
    simp only [hG, abs_neg]; exact hF_bound h x
  have hG_cont : ∀ x : 𝒳, Continuous fun h ↦ G h x := fun x ↦ (hF_cont x).neg
  set A : Set (Fin n → Ω) :=
    {S | 2 * C (X ∘ S) + 3 * ε ≤ oneSidedDeviation n F μ X (X ∘ S)} with hA
  set B : Set (Fin n → Ω) :=
    {S | 2 * C (X ∘ S) + 3 * ε ≤ oneSidedDeviation n G μ X (X ∘ S)} with hB
  have hsub : {S : Fin n → Ω | ∃ h, 2 * C (X ∘ S) + 3 * ε <
      |μ[fun ω ↦ F h (X ω)] - (n : ℝ)⁻¹ * ∑ k : Fin n, F h (X (S k))|} ⊆ A ∪ B := by
    rintro S ⟨h, hh⟩
    rcases lt_abs.mp hh with h1 | h1
    · right
      refine le_trans ?_ (le_oneSidedDeviation (μ := μ) hn X hG_bound (X ∘ S) h)
      have : (n : ℝ)⁻¹ * ∑ k : Fin n, G h ((X ∘ S) k) - μ[fun ω' ↦ G h (X ω')] =
          μ[fun ω ↦ F h (X ω)] - (n : ℝ)⁻¹ * ∑ k : Fin n, F h (X (S k)) := by
        simp only [hG, Function.comp_apply, Finset.sum_neg_distrib, mul_neg, integral_neg]
        ring
      rw [this]; exact h1.le
    · left
      refine le_trans ?_ (le_oneSidedDeviation (μ := μ) hn X hF_bound (X ∘ S) h)
      simp only [Function.comp_apply]
      linarith
  calc _ ≤ (μⁿ).real (A ∪ B) := measureReal_mono hsub
    _ ≤ (μⁿ).real A + (μⁿ).real B := measureReal_union_le A B
    _ ≤ 2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp + 2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp :=
        add_le_add
          (oneSidedDeviation_tail_bound_separable_of_sample_empirical_le (μ := μ) F hF_meas X hX
            C hb hF_bound hF_cont hC hε)
          (oneSidedDeviation_tail_bound_separable_of_sample_empirical_le (μ := μ) G hG_meas X hX
            C hb hG_bound hG_cont hC' hε)
    _ = _ := by ring

end Separable

end FoML.ToFoML
