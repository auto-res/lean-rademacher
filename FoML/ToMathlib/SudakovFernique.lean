import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
import FoML.ToMathlib.GaussianPi
import FoML.ToMathlib.GaussianIntegrationByParts
import FoML.ToMathlib.LogSumExp

/-!
# The Sudakov–Fernique comparison inequality

Rows G6–G7 of the Bernoulli–Sudakov blueprint (the Bernoulli–Sudakov blueprint of lean-deepgen: Talagrand ULB §6.4 + Sudakov–Fernique; §2 step S3).

Gaussian vectors are linear images of the standard Gaussian: for `A : Matrix (Fin M) (Fin N) ℝ`
and `g ~ stdGaussianPi N`, `X := A.mulVec g` is a centred Gaussian vector with covariance
`A Aᵀ` and increments `E (X_j − X_k)² = ∑ i, (A j i − A k i)²`.

**Main result** (`integral_iSup_mulVec_le`, `thm:sudakov-fernique`): if
`B : Matrix (Fin M) (Fin N') ℝ` satisfies `∑ i, (B j i − B k i)² ≤ ∑ i, (A j i − A k i)²` for all
`j, k` (the increments of `X = A g` dominate those of `Y = B g'`), then
`E max_j Y_j ≤ E max_j X_j` (Vershynin, *High-Dimensional Probability*, Thm 7.2.11).

**Route.** Put `X` and `Y` on one Gaussian space by the block matrices `[A | 0]`, `[0 | B]`
acting on `stdGaussianPi (N + N')` (`blockLeft`, `blockRight`); their rows are orthogonal.
For orthogonal `A, B` on a common `Fin K` interpolate `Z_θ := cos θ · A g + sin θ · B g`
(`interpMat`) and set `φ_β(θ) := ∫ logSumExp β (Z_θ) dγ` (`sfInterp`). Differentiating under the
integral sign (`hasDerivAt_sfInterp`, `lem:sf-hasDerivAt`; the θ-derivative of the integrand is
dominated by `‖A g‖ + ‖B g‖`) and integrating by parts in the Gaussian variable
(`integral_mulVec_mul_comp_mulVec_eq_sum_integral`, a two-matrix form of `cor:gaussian-ibp-linear`)
gives
\[ φ_β'(θ) = -\sin θ \cos θ \int \sum_{j,k} H_{jk}(Z_θ)\,(Σ^A − Σ^B)_{jk}\, dγ \le 0
   \quad (0 \le θ \le π/2), \]
where `H = lseHessian β` and `Σ^A = A Aᵀ`; the sign comes from `lem:lse-hessian-quadratic-nonneg`
since `(Σ^A − Σ^B)_{jj} + (Σ^A − Σ^B)_{kk} − 2 (Σ^A − Σ^B)_{jk} = ∑ i, (A j i − A k i)² −
∑ i, (B j i − B k i)² ≥ 0`. Hence `φ_β(π/2) ≤ φ_β(0)` (`sfInterp_pi_div_two_le_zero`,
`lem:sf-monotone`), i.e. `E logSumExp β (B g) ≤ E logSumExp β (A g)`; finally
`max ≤ logSumExp β ≤ max + log M / β` and `β → ∞`.

This file depends only on Mathlib (`Architect` annotations are commented out) through the
modules `FoML.ToMathlib.GaussianPi`, `FoML.ToMathlib.GaussianIntegrationByParts`
and `FoML.ToMathlib.LogSumExp`.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal Topology

namespace FoML.ToMathlib

section Prelim

variable {M N : ℕ}

/- @[blueprint "lem:norm-le-sum-abs"
  (statement := /-- $\|g\|_\infty \le \sum_i |g_i|$. -/)] -/
theorem norm_le_sum_abs (g : Fin N → ℝ) : ‖g‖ ≤ ∑ i, |g i| := by
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |g i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)

/- @[blueprint "lem:integrable-norm-std-gaussian-pi"
  (statement := /-- $\|g\|_\infty$ is $\gamma_N$-integrable. -/)] -/
theorem integrable_norm_stdGaussianPi :
    Integrable (fun g : Fin N → ℝ => ‖g‖) (stdGaussianPi N) := by
  refine Integrable.mono' (g := fun g : Fin N → ℝ => ∑ i, |g i|)
    (integrable_finsetSum _ fun i _ => (integrable_eval_stdGaussianPi i).abs)
    continuous_norm.measurable.aestronglyMeasurable (ae_of_all _ fun g => ?_)
  rw [norm_norm]
  exact norm_le_sum_abs g

/- @[blueprint "lem:continuous-mulVec"
  (statement := /-- $g \mapsto Ag$ is continuous. -/)] -/
theorem continuous_mulVec (A : Matrix (Fin M) (Fin N) ℝ) :
    Continuous fun g : Fin N → ℝ => A.mulVec g :=
  (LinearMap.toContinuousLinearMap A.mulVecLin).continuous

/- @[blueprint "lem:integrable-norm-mulVec-std-gaussian-pi"
  (statement := /-- $\|Ag\|_\infty$ is $\gamma_N$-integrable. -/)] -/
theorem integrable_norm_mulVec_stdGaussianPi (A : Matrix (Fin M) (Fin N) ℝ) :
    Integrable (fun g : Fin N → ℝ => ‖A.mulVec g‖) (stdGaussianPi N) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_mulVec_le A
  refine (integrable_norm_stdGaussianPi.const_mul K).mono'
    (continuous_norm.comp (continuous_mulVec A)).measurable.aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  rw [norm_norm]
  exact hK g

/- @[blueprint "lem:abs-iSup-le-norm"
  (statement := /-- For $M \ge 1$ and $y \in \mathbb R^M$, $|\max_j y_j| \le \|y\|_\infty$. -/)] -/
theorem abs_iSup_le_norm [Nonempty (Fin M)] (y : Fin M → ℝ) : |⨆ j, y j| ≤ ‖y‖ := by
  obtain ⟨j₀⟩ := ‹Nonempty (Fin M)›
  rw [abs_le]
  constructor
  · have h1 : y j₀ ≤ ⨆ j, y j := le_ciSup (Finite.bddAbove_range y) j₀
    have h2 : |y j₀| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y j₀
    linarith [neg_abs_le (y j₀)]
  · exact ciSup_le fun j =>
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y j)

/- @[blueprint "lem:measurable-iSup-mulVec"
  (statement := /-- $g \mapsto \max_j (Ag)_j$ is measurable. -/)] -/
theorem measurable_iSup_mulVec (A : Matrix (Fin M) (Fin N) ℝ) :
    Measurable fun g : Fin N → ℝ => ⨆ j, (A.mulVec g) j :=
  Measurable.iSup fun j => ((continuous_apply j).comp (continuous_mulVec A)).measurable

/- @[blueprint "lem:integrable-iSup-mulVec"
  (statement := /-- For $M \ge 1$, $g \mapsto \max_j (Ag)_j$ is $\gamma_N$-integrable. -/)] -/
theorem integrable_iSup_mulVec [Nonempty (Fin M)] (A : Matrix (Fin M) (Fin N) ℝ) :
    Integrable (fun g : Fin N → ℝ => ⨆ j, (A.mulVec g) j) (stdGaussianPi N) :=
  (integrable_norm_mulVec_stdGaussianPi A).mono' (measurable_iSup_mulVec A).aestronglyMeasurable
    (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact abs_iSup_le_norm _)

/- @[blueprint "lem:abs-lse-le"
  (statement := /-- For $\beta > 0$ and $M \ge 1$,
    $|\operatorname{LSE}_\beta(y)| \le \|y\|_\infty + \log M/\beta$. -/)] -/
theorem abs_logSumExp_le [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β) (y : Fin M → ℝ) :
    |logSumExp β y| ≤ ‖y‖ + Real.log M / β := by
  have h1 := iSup_le_logSumExp hβ y
  have h2 := logSumExp_le_iSup_add hβ y
  have h3 := abs_iSup_le_norm y
  have hM : (1 : ℝ) ≤ M := by
    have : 0 < M := Fin.pos'
    exact_mod_cast this
  have h4 : 0 ≤ Real.log M / β := div_nonneg (Real.log_nonneg hM) hβ.le
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

/- @[blueprint "lem:integrable-lse-mulVec"
  (statement := /-- For $\beta > 0$ and $M \ge 1$, $g \mapsto \operatorname{LSE}_\beta(Ag)$ is
    $\gamma_N$-integrable. -/)] -/
theorem integrable_logSumExp_mulVec [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A : Matrix (Fin M) (Fin N) ℝ) :
    Integrable (fun g : Fin N → ℝ => logSumExp β (A.mulVec g)) (stdGaussianPi N) :=
  ((integrable_norm_mulVec_stdGaussianPi A).add (integrable_const _)).mono'
    ((contDiff_logSumExp β (n := 1)).continuous.comp
      (continuous_mulVec A)).measurable.aestronglyMeasurable
    (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact abs_logSumExp_le hβ _)

end Prelim

section Block

/-! ### Block matrices `[A | 0]`, `[0 | B]` and the marginals of `stdGaussianPi (N + N')` -/

variable {M N N' : ℕ}

/- @[blueprint "def:block-left"
  (statement := /-- For $A \in \mathbb R^{M \times N}$, the block matrix
    $[A \mid 0] \in \mathbb R^{M \times (N + N')}$. -/)] -/
def blockLeft (A : Matrix (Fin M) (Fin N) ℝ) (N' : ℕ) : Matrix (Fin M) (Fin (N + N')) ℝ :=
  Matrix.of fun j => Fin.append (A j) 0

/- @[blueprint "def:block-right"
  (statement := /-- For $B \in \mathbb R^{M \times N'}$, the block matrix
    $[0 \mid B] \in \mathbb R^{M \times (N + N')}$. -/)] -/
def blockRight (N : ℕ) (B : Matrix (Fin M) (Fin N') ℝ) : Matrix (Fin M) (Fin (N + N')) ℝ :=
  Matrix.of fun j => Fin.append 0 (B j)

/- @[blueprint "lem:block-left-mulVec"
  (statement := /-- $[A \mid 0]\,g = A\,g_{<N}$ where $g_{<N} = (g_0, \dots, g_{N-1})$. -/)] -/
theorem blockLeft_mulVec (A : Matrix (Fin M) (Fin N) ℝ) (g : Fin (N + N') → ℝ) :
    (blockLeft A N').mulVec g = A.mulVec fun i => g (Fin.castAdd N' i) := by
  ext j
  simp [blockLeft, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/- @[blueprint "lem:block-right-mulVec"
  (statement := /-- $[0 \mid B]\,g = B\,g_{\ge N}$ where
    $g_{\ge N} = (g_N, \dots, g_{N+N'-1})$. -/)] -/
theorem blockRight_mulVec (B : Matrix (Fin M) (Fin N') ℝ) (g : Fin (N + N') → ℝ) :
    (blockRight N B).mulVec g = B.mulVec fun i => g (Fin.natAdd N i) := by
  ext j
  simp [blockRight, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/- @[blueprint "lem:block-orthogonal"
  (statement := /-- The rows of $[A \mid 0]$ and $[0 \mid B]$ are orthogonal:
    $\sum_i [A \mid 0]_{ji} [0 \mid B]_{ki} = 0$. -/)] -/
theorem sum_blockLeft_mul_blockRight (A : Matrix (Fin M) (Fin N) ℝ) (B : Matrix (Fin M) (Fin N') ℝ)
    (j k : Fin M) : ∑ i, blockLeft A N' j i * blockRight N B k i = 0 := by
  simp [blockLeft, blockRight, Fin.sum_univ_add]

/- @[blueprint "lem:block-left-increments"
  (statement := /-- $\sum_i ([A \mid 0]_{ji} - [A \mid 0]_{ki})^2
    = \sum_i (A_{ji} - A_{ki})^2$. -/)] -/
theorem sum_sq_sub_blockLeft (A : Matrix (Fin M) (Fin N) ℝ) (j k : Fin M) :
    ∑ i, (blockLeft A N' j i - blockLeft A N' k i) ^ 2 = ∑ i, (A j i - A k i) ^ 2 := by
  simp [blockLeft, Fin.sum_univ_add]

/- @[blueprint "lem:block-right-increments"
  (statement := /-- $\sum_i ([0 \mid B]_{ji} - [0 \mid B]_{ki})^2
    = \sum_i (B_{ji} - B_{ki})^2$. -/)] -/
theorem sum_sq_sub_blockRight (B : Matrix (Fin M) (Fin N') ℝ) (j k : Fin M) :
    ∑ i, (blockRight N B j i - blockRight N B k i) ^ 2 = ∑ i, (B j i - B k i) ^ 2 := by
  simp [blockRight, Fin.sum_univ_add]

/- @[blueprint "lem:std-gaussian-pi-castAdd-measurePreserving"
  (statement := /-- The projection $g \mapsto g_{<N}$ is measure preserving from
    $\gamma_{N+N'}$ to $\gamma_N$. -/)] -/
theorem measurePreserving_castAdd_stdGaussianPi (N N' : ℕ) :
    MeasurePreserving (fun g : Fin (N + N') → ℝ => fun i => g (Fin.castAdd N' i))
      (stdGaussianPi (N + N')) (stdGaussianPi N) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (N + N') => gaussianReal 0 1)
    finSumFinEquiv).symm _
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N' => gaussianReal 0 1)
  have h3 := measurePreserving_fst (μ := Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N' => gaussianReal 0 1)
  exact (h3.comp h2).comp h1

/- @[blueprint "lem:std-gaussian-pi-natAdd-measurePreserving"
  (statement := /-- The projection $g \mapsto g_{\ge N}$ is measure preserving from
    $\gamma_{N+N'}$ to $\gamma_{N'}$. -/)] -/
theorem measurePreserving_natAdd_stdGaussianPi (N N' : ℕ) :
    MeasurePreserving (fun g : Fin (N + N') → ℝ => fun i => g (Fin.natAdd N i))
      (stdGaussianPi (N + N')) (stdGaussianPi N') := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (N + N') => gaussianReal 0 1)
    finSumFinEquiv).symm _
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N' => gaussianReal 0 1)
  have h3 := measurePreserving_snd (μ := Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin N' => gaussianReal 0 1)
  exact (h3.comp h2).comp h1

/- @[blueprint "lem:integral-iSup-blockLeft"
  (statement := /-- $\int \max_j ([A \mid 0]g)_j\, d\gamma_{N+N'}
    = \int \max_j (Ag)_j\, d\gamma_N$. -/)] -/
theorem integral_iSup_blockLeft (A : Matrix (Fin M) (Fin N) ℝ) (N' : ℕ) :
    ∫ g, ⨆ j, ((blockLeft A N').mulVec g) j ∂stdGaussianPi (N + N')
      = ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N := by
  simp_rw [blockLeft_mulVec]
  rw [← (measurePreserving_castAdd_stdGaussianPi N N').map_eq]
  exact (integral_map (measurePreserving_castAdd_stdGaussianPi N N').measurable.aemeasurable
    (measurable_iSup_mulVec A).aestronglyMeasurable).symm

/- @[blueprint "lem:integral-iSup-blockRight"
  (statement := /-- $\int \max_j ([0 \mid B]g)_j\, d\gamma_{N+N'}
    = \int \max_j (Bg)_j\, d\gamma_{N'}$. -/)] -/
theorem integral_iSup_blockRight (N : ℕ) (B : Matrix (Fin M) (Fin N') ℝ) :
    ∫ g, ⨆ j, ((blockRight N B).mulVec g) j ∂stdGaussianPi (N + N')
      = ∫ g, ⨆ j, (B.mulVec g) j ∂stdGaussianPi N' := by
  simp_rw [blockRight_mulVec]
  rw [← (measurePreserving_natAdd_stdGaussianPi N N').map_eq]
  exact (integral_map (measurePreserving_natAdd_stdGaussianPi N N').measurable.aemeasurable
    (measurable_iSup_mulVec B).aestronglyMeasurable).symm

end Block

section IBP

/-! ### Gaussian integration by parts with two linear images -/

variable {M N : ℕ}

/- @[blueprint "lem:norm-lin-comb-le"
  (statement := /-- $\|\operatorname{linComb}(c)\| \le \sum_k |c_k|$ (operator norm for
    $\|\cdot\|_\infty$). -/)] -/
theorem norm_linComb_le (c : Fin M → ℝ) : ‖linComb c‖ ≤ ∑ k, |c k| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _)
    fun v => ?_
  rw [linComb_apply, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm v k

/- @[blueprint "cor:gaussian-ibp-linear-two"
  (statement := /-- \textbf{Gaussian integration by parts, two linear images.} Let
    $C, D \in \mathbb R^{M \times N}$, $g \sim N(0,1)^{\otimes N}$. If
    $f : \mathbb R^M \to \mathbb R$ is $C^1$ with $|f(y)| \le K(1 + \|y\|_\infty)$ and
    $\|Df(y)\| \le K$, then for every $j$
    \[ \mathbb E[(Dg)_j\, f(Cg)] = \sum_k \Big(\sum_i D_{ji} C_{ki}\Big)\,
      \mathbb E[\partial_k f(Cg)] . \] -/)] -/
theorem integral_mulVec_mul_comp_mulVec_eq_sum_integral (D C : Matrix (Fin M) (Fin N) ℝ)
    {f : (Fin M → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hfK : ∀ y, |f y| ≤ K * (1 + ‖y‖)) (hDf : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (j : Fin M) :
    ∫ x, (D.mulVec x) j * f (C.mulVec x) ∂(stdGaussianPi N)
      = ∑ k, (∑ i, D j i * C k i) *
          ∫ x, fderiv ℝ f (C.mulVec x) (Pi.single k 1) ∂(stdGaussianPi N) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hDf 0)
  set L : (Fin N → ℝ) →L[ℝ] (Fin M → ℝ) := LinearMap.toContinuousLinearMap C.mulVecLin with hL
  obtain ⟨K', hK'0, hK'⟩ := exists_norm_mulVec_le C
  have hfcont : Continuous f := hf.continuous
  have hDfcont : Continuous fun p : (Fin M → ℝ) × (Fin M → ℝ) => fderiv ℝ f p.1 p.2 :=
    hf.continuous_fderiv_apply one_ne_zero
  have hmeasD : ∀ v, Measurable fun x : Fin N → ℝ => fderiv ℝ f (C.mulVec x) v := fun v =>
    (hDfcont.comp (L.continuous.prodMk continuous_const)).measurable
  have hnorm_single : ∀ k : Fin M, ‖(Pi.single k (1 : ℝ) : Fin M → ℝ)‖ ≤ 1 := fun k => by
    rw [Pi.norm_single, norm_one]
  have hboundD : ∀ (v : Fin M → ℝ) (x : Fin N → ℝ), |fderiv ℝ f (C.mulVec x) v| ≤ K * ‖v‖ :=
    fun v x => by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ f (C.mulVec x)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hDf _) (norm_nonneg _))
  have hintD : ∀ k : Fin M,
      Integrable (fun x => fderiv ℝ f (C.mulVec x) (Pi.single k 1)) (stdGaussianPi N) := fun k =>
    (integrable_const K).mono' (hmeasD _).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact (hboundD _ x).trans (mul_le_of_le_one_right hK (hnorm_single k)))
  -- the partial IBP identity for each coordinate `i` of `x`
  have hcoord : ∀ i : Fin N,
      ∫ x, x i * f (C.mulVec x) ∂(stdGaussianPi N)
        = ∑ k, C k i * ∫ x, fderiv ℝ f (C.mulVec x) (Pi.single k 1) ∂(stdGaussianPi N) := by
    intro i
    have key := integral_mul_stdGaussianPi_eq_integral_partial i
      (F := fun x => f (C.mulVec x)) (F' := fun x => fderiv ℝ f (C.mulVec x) (fun k => C k i))
      (hfcont.comp L.continuous).measurable (hmeasD _) ?_ (C := K * (1 + K' + ‖(fun k => C k i)‖))
      ?_ ?_
    · rw [key]
      simp_rw [fderiv_apply_col]
      rw [integral_finsetSum _ fun k _ => (hintD k).const_mul _]
      simp_rw [integral_const_mul]
    · intro x
      have hu : HasDerivAt (fun t => C.mulVec (Function.update x i t)) (C.mulVec (Pi.single i 1))
          (x i) :=
        L.hasFDerivAt.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
      have hfd : HasFDerivAt f (fderiv ℝ f (C.mulVec x))
          (C.mulVec (Function.update x i (x i))) := by
        rw [Function.update_eq_self]
        exact ((hf.differentiable one_ne_zero) (C.mulVec x)).hasFDerivAt
      have := hfd.comp_hasDerivAt (x i) hu
      rw [Matrix.mulVec_single_one] at this
      exact this
    · intro x
      refine (hfK _).trans ?_
      have := hK' x
      have hv : 0 ≤ ‖(fun k => C k i)‖ := norm_nonneg _
      nlinarith [norm_nonneg x, mul_nonneg hK (norm_nonneg x), mul_nonneg hK hK'0,
        mul_nonneg (mul_nonneg hK hK'0) (norm_nonneg x), mul_nonneg hK hv,
        mul_nonneg (mul_nonneg hK hv) (norm_nonneg x)]
    · intro x
      refine (hboundD _ x).trans ?_
      nlinarith [mul_nonneg hK hK'0, norm_nonneg (fun k => C k i)]
  -- assemble
  have hmul : ∀ x, (D.mulVec x) j * f (C.mulVec x) = ∑ i, D j i * (x i * f (C.mulVec x)) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  have hint_i : ∀ i : Fin N, Integrable (fun x => x i * f (C.mulVec x)) (stdGaussianPi N) := by
    intro i
    have hb : Integrable (fun x : Fin N → ℝ => K * (1 + K') * (2 + 2 * ‖x‖ ^ 2))
        (stdGaussianPi N) :=
      ((integrable_const (2 : ℝ)).add (integrable_norm_sq_stdGaussianPi.const_mul 2)).const_mul _
    refine hb.mono' ((measurable_pi_apply i).mul
      (hfcont.comp L.continuous).measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hxi : |x i| ≤ ‖x‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i
    have hCx := hK' x
    calc |x i| * |f (C.mulVec x)| ≤ ‖x‖ * (K * (1 + ‖C.mulVec x‖)) :=
          mul_le_mul hxi (hfK _) (abs_nonneg _) (norm_nonneg _)
      _ ≤ ‖x‖ * (K * (1 + K' * ‖x‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hK) (norm_nonneg _)
      _ ≤ K * (1 + K') * (2 + 2 * ‖x‖ ^ 2) := by
          nlinarith [norm_nonneg x, mul_nonneg hK (norm_nonneg x), mul_nonneg hK hK'0,
            mul_nonneg (mul_nonneg hK hK'0) (norm_nonneg x),
            mul_nonneg (mul_nonneg hK hK'0) (sq_nonneg ‖x‖), mul_nonneg hK (sq_nonneg ‖x‖)]
  simp_rw [hmul]
  rw [integral_finsetSum _ fun i _ => (hint_i i).const_mul _]
  simp_rw [integral_const_mul, hcoord, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- @[blueprint "lem:softmax-growth"
  (statement := /-- $|p_j(y)| \le (1 + M|\beta|)(1 + \|y\|_\infty)$ and
    $\|Dp_j(y)\| \le 1 + M|\beta|$. -/)] -/
theorem softmax_growth [Nonempty (Fin M)] (β : ℝ) (j : Fin M) :
    (∀ y : Fin M → ℝ, |softmax β y j| ≤ (1 + M * |β|) * (1 + ‖y‖)) ∧
      ∀ y : Fin M → ℝ, ‖fderiv ℝ (fun y => softmax β y j) y‖ ≤ 1 + M * |β| := by
  have hM : (0 : ℝ) ≤ M * |β| := by positivity
  constructor
  · intro y
    rw [abs_of_nonneg (softmax_nonneg β y j)]
    calc softmax β y j ≤ 1 := softmax_le_one β y j
      _ ≤ (1 + M * |β|) * (1 + ‖y‖) := by nlinarith [norm_nonneg y]
  · intro y
    rw [(hasFDerivAt_softmax β y j).fderiv]
    refine (norm_linComb_le _).trans ?_
    calc ∑ k, |lseHessian β y j k| ≤ ∑ _k : Fin M, |β| :=
          Finset.sum_le_sum fun k _ => abs_lseHessian_le β y j k
      _ = M * |β| := by simp
      _ ≤ 1 + M * |β| := by linarith

/- @[blueprint "cor:gaussian-ibp-softmax"
  (statement := /-- For $C, D \in \mathbb R^{M \times N}$ and $g \sim N(0,1)^{\otimes N}$,
    \[ \mathbb E[(Dg)_j\, p_j(Cg)] = \sum_k \Big(\sum_i D_{ji} C_{ki}\Big)\,
      \mathbb E[H_{jk}(Cg)] , \] where $p = \nabla \operatorname{LSE}_\beta$ and
    $H = \nabla^2 \operatorname{LSE}_\beta$. -/)] -/
theorem integral_mulVec_mul_softmax_eq_sum_integral [Nonempty (Fin M)] (β : ℝ)
    (D C : Matrix (Fin M) (Fin N) ℝ) (j : Fin M) :
    ∫ x, (D.mulVec x) j * softmax β (C.mulVec x) j ∂(stdGaussianPi N)
      = ∑ k, (∑ i, D j i * C k i) * ∫ x, lseHessian β (C.mulVec x) j k ∂(stdGaussianPi N) := by
  obtain ⟨h1, h2⟩ := softmax_growth (M := M) β j
  have := integral_mulVec_mul_comp_mulVec_eq_sum_integral D C (f := fun y => softmax β y j)
    (contDiff_softmax β j) h1 h2 j
  simp_rw [fderiv_softmax_single] at this
  exact this

end IBP

section Interp

/-! ### The interpolation `Z_θ = cos θ · A g + sin θ · B g` -/

variable {M N : ℕ}

/- @[blueprint "def:sf-interp-mat"
  (statement := /-- $C_\theta := \cos\theta\, A + \sin\theta\, B$, so that
    $Z_\theta = C_\theta\, g = \cos\theta\, Ag + \sin\theta\, Bg$. -/)] -/
noncomputable def interpMat (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  Real.cos θ • A + Real.sin θ • B

/- @[blueprint "def:sf-interp-mat-deriv"
  (statement := /-- $D_\theta := \frac{d}{d\theta} C_\theta
    = -\sin\theta\, A + \cos\theta\, B$. -/)] -/
noncomputable def interpMatDeriv (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  (-Real.sin θ) • A + Real.cos θ • B

/- @[blueprint "lem:sf-interp-mat-mulVec"
  (statement := /-- $C_\theta g = \cos\theta \cdot Ag + \sin\theta \cdot Bg$. -/)] -/
theorem interpMat_mulVec (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) (g : Fin N → ℝ) :
    (interpMat A B θ).mulVec g = Real.cos θ • A.mulVec g + Real.sin θ • B.mulVec g := by
  simp [interpMat, Matrix.add_mulVec, Matrix.smul_mulVec]

/- @[blueprint "lem:sf-interp-mat-deriv-mulVec"
  (statement := /-- $D_\theta g = -\sin\theta \cdot Ag + \cos\theta \cdot Bg$. -/)] -/
theorem interpMatDeriv_mulVec (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) (g : Fin N → ℝ) :
    (interpMatDeriv A B θ).mulVec g = (-Real.sin θ) • A.mulVec g + Real.cos θ • B.mulVec g := by
  simp only [interpMatDeriv, Matrix.add_mulVec, Matrix.smul_mulVec]

/- @[blueprint "lem:sf-interp-mat-zero"
  (statement := /-- $C_0 = A$. -/)] -/
theorem interpMat_zero (A B : Matrix (Fin M) (Fin N) ℝ) : interpMat A B 0 = A := by
  simp [interpMat]

/- @[blueprint "lem:sf-interp-mat-pi-div-two"
  (statement := /-- $C_{\pi/2} = B$. -/)] -/
theorem interpMat_pi_div_two (A B : Matrix (Fin M) (Fin N) ℝ) :
    interpMat A B (Real.pi / 2) = B := by
  simp [interpMat]

/- @[blueprint "lem:norm-smul-add-smul-le"
  (statement := /-- For $|c|, |s| \le 1$:
    $\|c\,u + s\,v\|_\infty \le \|u\|_\infty + \|v\|_\infty$. -/)] -/
theorem norm_smul_add_smul_le {c s : ℝ} (hc : |c| ≤ 1) (hs : |s| ≤ 1) (u v : Fin M → ℝ) :
    ‖c • u + s • v‖ ≤ ‖u‖ + ‖v‖ := by
  calc ‖c • u + s • v‖ ≤ ‖c • u‖ + ‖s • v‖ := norm_add_le _ _
    _ = |c| * ‖u‖ + |s| * ‖v‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖u‖ + 1 * ‖v‖ := by gcongr
    _ = ‖u‖ + ‖v‖ := by ring

/- @[blueprint "lem:sf-interp-norm-le"
  (statement := /-- $\|C_\theta g\|_\infty \le \|Ag\|_\infty + \|Bg\|_\infty$. -/)] -/
theorem norm_interpMat_mulVec_le (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) (g : Fin N → ℝ) :
    ‖(interpMat A B θ).mulVec g‖ ≤ ‖A.mulVec g‖ + ‖B.mulVec g‖ := by
  rw [interpMat_mulVec]
  exact norm_smul_add_smul_le (Real.abs_cos_le_one θ) (Real.abs_sin_le_one θ) _ _

/- @[blueprint "lem:sf-interp-deriv-norm-le"
  (statement := /-- $\|D_\theta g\|_\infty \le \|Ag\|_\infty + \|Bg\|_\infty$. -/)] -/
theorem norm_interpMatDeriv_mulVec_le (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) (g : Fin N → ℝ) :
    ‖(interpMatDeriv A B θ).mulVec g‖ ≤ ‖A.mulVec g‖ + ‖B.mulVec g‖ := by
  rw [interpMatDeriv_mulVec]
  exact norm_smul_add_smul_le (by rw [abs_neg]; exact Real.abs_sin_le_one θ)
    (Real.abs_cos_le_one θ) _ _

/- @[blueprint "lem:sf-interp-hasDerivAt"
  (statement := /-- $\theta \mapsto C_\theta g$ is differentiable with derivative $D_\theta g$. -/)] -/
theorem hasDerivAt_interpMat_mulVec (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) (g : Fin N → ℝ) :
    HasDerivAt (fun θ => (interpMat A B θ).mulVec g) ((interpMatDeriv A B θ).mulVec g) θ := by
  rw [hasDerivAt_pi]
  intro j
  simp only [interpMat_mulVec, interpMatDeriv_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ((Real.hasDerivAt_cos θ).mul_const _).add ((Real.hasDerivAt_sin θ).mul_const _)

/- @[blueprint "lem:sf-interp-cov"
  (statement := /-- If the rows of $A$ and $B$ are orthogonal ($\sum_i A_{ji} B_{ki} = 0$ for all
    $j, k$), then
    $\sum_i (D_\theta)_{ji} (C_\theta)_{ki} = \sin\theta \cos\theta\,
      \big(\sum_i B_{ji} B_{ki} - \sum_i A_{ji} A_{ki}\big)$. -/)] -/
theorem sum_interpMatDeriv_mul_interpMat (A B : Matrix (Fin M) (Fin N) ℝ)
    (hAB : ∀ j k, ∑ i, A j i * B k i = 0) (θ : ℝ) (j k : Fin M) :
    ∑ i, interpMatDeriv A B θ j i * interpMat A B θ k i
      = Real.sin θ * Real.cos θ * (∑ i, B j i * B k i - ∑ i, A j i * A k i) := by
  have h : ∀ i, interpMatDeriv A B θ j i * interpMat A B θ k i
      = (-(Real.sin θ * Real.cos θ)) * (A j i * A k i)
        + (-(Real.sin θ * Real.sin θ)) * (A j i * B k i)
        + (Real.cos θ * Real.cos θ) * (A k i * B j i)
        + (Real.cos θ * Real.sin θ) * (B j i * B k i) := by
    intro i
    simp only [interpMat, interpMatDeriv, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hAB j k, hAB k j]
  ring

/- @[blueprint "lem:sf-increment-identity"
  (statement := /-- With $\Sigma^A_{jk} = \sum_i A_{ji} A_{ki}$ and $Q := \Sigma^A - \Sigma^B$,
    $Q_{jj} + Q_{kk} - 2 Q_{jk} = \sum_i (A_{ji} - A_{ki})^2 - \sum_i (B_{ji} - B_{ki})^2$. -/)] -/
theorem cov_sub_identity (A B : Matrix (Fin M) (Fin N) ℝ) (j k : Fin M) :
    (∑ i, A j i * A j i - ∑ i, B j i * B j i) + (∑ i, A k i * A k i - ∑ i, B k i * B k i)
        - 2 * (∑ i, A j i * A k i - ∑ i, B j i * B k i)
      = ∑ i, (A j i - A k i) ^ 2 - ∑ i, (B j i - B k i) ^ 2 := by
  have h1 : ∀ i, (A j i - A k i) ^ 2 = A j i * A j i + A k i * A k i - 2 * (A j i * A k i) :=
    fun i => by ring
  have h2 : ∀ i, (B j i - B k i) ^ 2 = B j i * B j i + B k i * B k i - 2 * (B j i * B k i) :=
    fun i => by ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Interp

section Deriv

/-! ### `φ_β(θ) = ∫ logSumExp β (Z_θ)` and its derivative -/

variable {M N : ℕ}

/- @[blueprint "def:sf-interp"
  (statement := /-- $\phi_\beta(\theta) := \int \operatorname{LSE}_\beta(C_\theta g)\,
    d\gamma_N(g)$. -/)] -/
noncomputable def sfInterp (β : ℝ) (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) : ℝ :=
  ∫ g, logSumExp β ((interpMat A B θ).mulVec g) ∂stdGaussianPi N

/- @[blueprint "def:sf-interp-deriv"
  (statement := /-- The pointwise $\theta$-derivative of the integrand:
    $\Phi'_\beta(\theta, g) := \sum_j p_j(C_\theta g)\,(D_\theta g)_j$. -/)] -/
noncomputable def sfInterpDeriv (β : ℝ) (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ)
    (g : Fin N → ℝ) : ℝ :=
  ∑ j, softmax β ((interpMat A B θ).mulVec g) j * ((interpMatDeriv A B θ).mulVec g) j

/- @[blueprint "lem:sf-integrand-hasDerivAt"
  (statement := /-- For $\beta \ne 0$, $\theta \mapsto \operatorname{LSE}_\beta(C_\theta g)$ is
    differentiable with derivative $\Phi'_\beta(\theta, g)$ (chain rule). -/)] -/
theorem hasDerivAt_logSumExp_interpMat [Nonempty (Fin M)] {β : ℝ} (hβ : β ≠ 0)
    (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) (g : Fin N → ℝ) :
    HasDerivAt (fun θ => logSumExp β ((interpMat A B θ).mulVec g)) (sfInterpDeriv β A B θ g) θ := by
  have := (hasFDerivAt_logSumExp hβ ((interpMat A B θ).mulVec g)).comp_hasDerivAt θ
    (hasDerivAt_interpMat_mulVec A B θ g)
  rw [linComb_apply] at this
  exact this

/- @[blueprint "lem:sf-integrand-deriv-bound"
  (statement := /-- $|\Phi'_\beta(\theta, g)| \le \|Ag\|_\infty + \|Bg\|_\infty$, uniformly in
    $\theta$ (since $p$ is a probability vector). -/)] -/
theorem abs_sfInterpDeriv_le [Nonempty (Fin M)] (β : ℝ) (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ)
    (g : Fin N → ℝ) : |sfInterpDeriv β A B θ g| ≤ ‖A.mulVec g‖ + ‖B.mulVec g‖ := by
  set Z := (interpMat A B θ).mulVec g
  set D := (interpMatDeriv A B θ).mulVec g
  calc |sfInterpDeriv β A B θ g| ≤ ∑ j, |softmax β Z j * D j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, softmax β Z j * ‖D‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (softmax_nonneg β Z j)]
        refine mul_le_mul_of_nonneg_left ?_ (softmax_nonneg β Z j)
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm D j
    _ = ‖D‖ := by rw [← Finset.sum_mul, sum_softmax, one_mul]
    _ ≤ ‖A.mulVec g‖ + ‖B.mulVec g‖ := norm_interpMatDeriv_mulVec_le A B θ g

/- @[blueprint "lem:sf-integrand-deriv-continuous"
  (statement := /-- $g \mapsto \Phi'_\beta(\theta, g)$ is continuous. -/)] -/
theorem continuous_sfInterpDeriv [Nonempty (Fin M)] (β : ℝ) (A B : Matrix (Fin M) (Fin N) ℝ)
    (θ : ℝ) : Continuous (sfInterpDeriv β A B θ) := by
  refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
  · exact (contDiff_softmax β (n := 1) j).continuous.comp (continuous_mulVec _)
  · exact (continuous_apply j).comp (continuous_mulVec _)

/- @[blueprint "lem:sf-hasDerivAt"
  (statement := /-- \textbf{Differentiation under the integral sign.} For $\beta > 0$ and
    $M \ge 1$, $\phi_\beta$ is differentiable at every $\theta$ with
    $\phi_\beta'(\theta) = \int \Phi'_\beta(\theta, g)\, d\gamma_N(g)
    = \int \sum_j p_j(Z_\theta)\,(-\sin\theta\,(Ag)_j + \cos\theta\,(Bg)_j)\, d\gamma_N$.
    (Domination: $|\Phi'_\beta(\theta, g)| \le \|Ag\|_\infty + \|Bg\|_\infty$, which is
    integrable.) -/)] -/
theorem hasDerivAt_sfInterp [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ) :
    HasDerivAt (sfInterp β A B) (∫ g, sfInterpDeriv β A B θ g ∂stdGaussianPi N) θ := by
  have hbound : Integrable (fun g : Fin N → ℝ => ‖A.mulVec g‖ + ‖B.mulVec g‖) (stdGaussianPi N) :=
    (integrable_norm_mulVec_stdGaussianPi A).add (integrable_norm_mulVec_stdGaussianPi B)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussianPi N)
    (F := fun θ g => logSumExp β ((interpMat A B θ).mulVec g)) (F' := sfInterpDeriv β A B)
    (x₀ := θ) (s := Set.univ) (bound := fun g => ‖A.mulVec g‖ + ‖B.mulVec g‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ' => (integrable_logSumExp_mulVec hβ _).aestronglyMeasurable)
    (integrable_logSumExp_mulVec hβ _)
    (continuous_sfInterpDeriv β A B θ).measurable.aestronglyMeasurable
    (ae_of_all _ fun g θ' _ => by rw [Real.norm_eq_abs]; exact abs_sfInterpDeriv_le β A B θ' g)
    hbound
    (ae_of_all _ fun g θ' _ => hasDerivAt_logSumExp_interpMat hβ.ne' A B θ' g)
  exact h.2

/- @[blueprint "lem:sf-integrable-hessian"
  (statement := /-- $g \mapsto H_{jk}(C g)$ is $\gamma_N$-integrable (it is bounded by
    $|\beta|$). -/)] -/
theorem integrable_lseHessian_mulVec (β : ℝ) (C : Matrix (Fin M) (Fin N) ℝ) (j k : Fin M) :
    Integrable (fun g : Fin N → ℝ => lseHessian β (C.mulVec g) j k) (stdGaussianPi N) := by
  have hcont : Continuous fun g : Fin N → ℝ => lseHessian β (C.mulVec g) j k := by
    have : ∀ y : Fin M → ℝ, lseHessian β y j k
        = β * ((if j = k then softmax β y j else 0) - softmax β y j * softmax β y k) := fun _ => rfl
    simp only [this]
    haveI : Nonempty (Fin M) := ⟨j⟩
    have h1 : Continuous fun g : Fin N → ℝ => softmax β (C.mulVec g) j :=
      (contDiff_softmax β (n := 1) j).continuous.comp (continuous_mulVec _)
    have h2 : Continuous fun g : Fin N → ℝ => softmax β (C.mulVec g) k :=
      (contDiff_softmax β (n := 1) k).continuous.comp (continuous_mulVec _)
    split_ifs <;> fun_prop
  exact (integrable_const |β|).mono' hcont.measurable.aestronglyMeasurable
    (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact abs_lseHessian_le β _ j k)

/- @[blueprint "lem:sf-integrable-deriv-term"
  (statement := /-- $g \mapsto p_j(C_\theta g)\,(D_\theta g)_j$ is $\gamma_N$-integrable. -/)] -/
theorem integrable_softmax_mul_interpMatDeriv (β : ℝ) (A B : Matrix (Fin M) (Fin N) ℝ) (θ : ℝ)
    (j : Fin M) :
    Integrable (fun g : Fin N → ℝ =>
      softmax β ((interpMat A B θ).mulVec g) j * ((interpMatDeriv A B θ).mulVec g) j)
      (stdGaussianPi N) := by
  haveI : Nonempty (Fin M) := ⟨j⟩
  have hcont : Continuous fun g : Fin N → ℝ =>
      softmax β ((interpMat A B θ).mulVec g) j * ((interpMatDeriv A B θ).mulVec g) j :=
    ((contDiff_softmax β (n := 1) j).continuous.comp (continuous_mulVec _)).mul
      ((continuous_apply j).comp (continuous_mulVec _))
  refine ((integrable_norm_mulVec_stdGaussianPi A).add
    (integrable_norm_mulVec_stdGaussianPi B)).mono' hcont.measurable.aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (softmax_nonneg _ _ _)]
  calc softmax β ((interpMat A B θ).mulVec g) j * |((interpMatDeriv A B θ).mulVec g) j|
      ≤ 1 * ‖(interpMatDeriv A B θ).mulVec g‖ := by
        refine mul_le_mul (softmax_le_one _ _ _) ?_ (abs_nonneg _) zero_le_one
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ j
    _ ≤ ‖A.mulVec g‖ + ‖B.mulVec g‖ := by rw [one_mul]; exact norm_interpMatDeriv_mulVec_le A B θ g

/- @[blueprint "lem:sf-deriv-formula"
  (statement := /-- \textbf{Derivative formula.} If the rows of $A$ and $B$ are orthogonal, then
    for $\beta > 0$, $M \ge 1$,
    \[ \phi_\beta'(\theta) = -\sin\theta\cos\theta \int \sum_{j,k} H_{jk}(Z_\theta)\,
      \big(\Sigma^A_{jk} - \Sigma^B_{jk}\big)\, d\gamma_N , \qquad
      \Sigma^A_{jk} = \sum_i A_{ji} A_{ki} . \]
    (Gaussian integration by parts in each term of $\Phi'_\beta$.) -/)] -/
theorem integral_sfInterpDeriv_eq [Nonempty (Fin M)] (β : ℝ) (A B : Matrix (Fin M) (Fin N) ℝ)
    (hAB : ∀ j k, ∑ i, A j i * B k i = 0) (θ : ℝ) :
    ∫ g, sfInterpDeriv β A B θ g ∂stdGaussianPi N
      = -(Real.sin θ * Real.cos θ) * ∫ g, ∑ j, ∑ k, lseHessian β ((interpMat A B θ).mulVec g) j k *
          (∑ i, A j i * A k i - ∑ i, B j i * B k i) ∂stdGaussianPi N := by
  unfold sfInterpDeriv
  rw [integral_finsetSum _ fun j _ => integrable_softmax_mul_interpMatDeriv β A B θ j]
  have hibp : ∀ j, ∫ g, softmax β ((interpMat A B θ).mulVec g) j *
        ((interpMatDeriv A B θ).mulVec g) j ∂stdGaussianPi N
      = ∑ k, Real.sin θ * Real.cos θ * (∑ i, B j i * B k i - ∑ i, A j i * A k i) *
          ∫ g, lseHessian β ((interpMat A B θ).mulVec g) j k ∂stdGaussianPi N := by
    intro j
    simp_rw [mul_comm (softmax β _ j)]
    rw [integral_mulVec_mul_softmax_eq_sum_integral β (interpMatDeriv A B θ) (interpMat A B θ) j]
    simp_rw [sum_interpMatDeriv_mul_interpMat A B hAB θ]
  simp_rw [hibp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (integrable_lseHessian_mulVec β _ j k).mul_const _]
  simp_rw [integral_finsetSum _ fun k _ => (integrable_lseHessian_mulVec β _ _ k).mul_const _,
    integral_mul_const, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- @[blueprint "lem:sf-deriv-nonpos"
  (statement := /-- \textbf{Sign of the derivative.} If the rows of $A$ and $B$ are orthogonal and
    $\sum_i (B_{ji} - B_{ki})^2 \le \sum_i (A_{ji} - A_{ki})^2$ for all $j, k$, then for
    $\beta > 0$ and $0 \le \theta \le \pi/2$, $\phi_\beta'(\theta) \le 0$. -/)] -/
theorem integral_sfInterpDeriv_nonpos [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A B : Matrix (Fin M) (Fin N) ℝ) (hAB : ∀ j k, ∑ i, A j i * B k i = 0)
    (hinc : ∀ j k, ∑ i, (B j i - B k i) ^ 2 ≤ ∑ i, (A j i - A k i) ^ 2)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) :
    ∫ g, sfInterpDeriv β A B θ g ∂stdGaussianPi N ≤ 0 := by
  rw [integral_sfInterpDeriv_eq β A B hAB θ]
  have hsc : 0 ≤ Real.sin θ * Real.cos θ :=
    mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]))
      (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθ1)
  have hint : 0 ≤ ∫ g, ∑ j, ∑ k, lseHessian β ((interpMat A B θ).mulVec g) j k *
      (∑ i, A j i * A k i - ∑ i, B j i * B k i) ∂stdGaussianPi N := by
    refine integral_nonneg fun g => ?_
    refine sum_lseHessian_mul_nonneg hβ.le _
      (Q := fun j k => ∑ i, A j i * A k i - ∑ i, B j i * B k i) fun j k => ?_
    linarith [hinc j k, cov_sub_identity A B j k]
  nlinarith

/- @[blueprint "lem:sf-monotone"
  (statement := /-- \textbf{Monotonicity.} Under the hypotheses of the previous lemma,
    $\phi_\beta(\pi/2) \le \phi_\beta(0)$, i.e.
    $\int \operatorname{LSE}_\beta(Bg)\, d\gamma_N \le \int \operatorname{LSE}_\beta(Ag)\,
    d\gamma_N$. -/)] -/
theorem sfInterp_pi_div_two_le_zero [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A B : Matrix (Fin M) (Fin N) ℝ) (hAB : ∀ j k, ∑ i, A j i * B k i = 0)
    (hinc : ∀ j k, ∑ i, (B j i - B k i) ^ 2 ≤ ∑ i, (A j i - A k i) ^ 2) :
    sfInterp β A B (Real.pi / 2) ≤ sfInterp β A B 0 := by
  have hd : ∀ θ, HasDerivAt (sfInterp β A B) (∫ g, sfInterpDeriv β A B θ g ∂stdGaussianPi N) θ :=
    hasDerivAt_sfInterp hβ A B
  have hanti : AntitoneOn (sfInterp β A B) (Set.Icc 0 (Real.pi / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun θ => (hd θ).continuousAt).continuousOn
    · exact fun θ _ => (hd θ).differentiableAt.differentiableWithinAt
    · intro θ hθ
      rw [interior_Icc] at hθ
      rw [(hd θ).deriv]
      exact integral_sfInterpDeriv_nonpos hβ A B hAB hinc hθ.1.le hθ.2.le
  exact hanti ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩ (by positivity)

/- @[blueprint "lem:sf-lse-comparison"
  (statement := /-- If the rows of $A$ and $B$ are orthogonal and
    $\sum_i (B_{ji} - B_{ki})^2 \le \sum_i (A_{ji} - A_{ki})^2$, then for every $\beta > 0$
    $\int \operatorname{LSE}_\beta(Bg)\, d\gamma_N \le \int \operatorname{LSE}_\beta(Ag)\,
    d\gamma_N$. -/)] -/
theorem integral_logSumExp_mulVec_le_of_orthogonal [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A B : Matrix (Fin M) (Fin N) ℝ) (hAB : ∀ j k, ∑ i, A j i * B k i = 0)
    (hinc : ∀ j k, ∑ i, (B j i - B k i) ^ 2 ≤ ∑ i, (A j i - A k i) ^ 2) :
    ∫ g, logSumExp β (B.mulVec g) ∂stdGaussianPi N
      ≤ ∫ g, logSumExp β (A.mulVec g) ∂stdGaussianPi N := by
  have := sfInterp_pi_div_two_le_zero hβ A B hAB hinc
  unfold sfInterp at this
  rwa [interpMat_pi_div_two, interpMat_zero] at this

end Deriv

section Main

variable {M N N' : ℕ}

/- @[blueprint "lem:integral-iSup-le-integral-lse"
  (statement := /-- $\int \max_j (Ag)_j\, d\gamma_N \le \int \operatorname{LSE}_\beta(Ag)\,
    d\gamma_N$ for $\beta > 0$. -/)] -/
theorem integral_iSup_mulVec_le_integral_logSumExp [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A : Matrix (Fin M) (Fin N) ℝ) :
    ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N ≤ ∫ g, logSumExp β (A.mulVec g) ∂stdGaussianPi N :=
  integral_mono (integrable_iSup_mulVec A) (integrable_logSumExp_mulVec hβ A)
    fun g => iSup_le_logSumExp hβ (A.mulVec g)

/- @[blueprint "lem:integral-lse-le-integral-iSup-add"
  (statement := /-- $\int \operatorname{LSE}_\beta(Ag)\, d\gamma_N \le \int \max_j (Ag)_j\,
    d\gamma_N + \log M/\beta$ for $\beta > 0$. -/)] -/
theorem integral_logSumExp_mulVec_le_integral_iSup_add [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β)
    (A : Matrix (Fin M) (Fin N) ℝ) :
    ∫ g, logSumExp β (A.mulVec g) ∂stdGaussianPi N
      ≤ ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N + Real.log M / β := by
  have hi : Integrable (fun g : Fin N → ℝ => (⨆ j, (A.mulVec g) j) + Real.log M / β)
      (stdGaussianPi N) :=
    (integrable_iSup_mulVec A).add (integrable_const (Real.log M / β))
  have h := integral_mono (integrable_logSumExp_mulVec hβ A) hi
    fun g => logSumExp_le_iSup_add hβ (A.mulVec g)
  rwa [integral_add (integrable_iSup_mulVec A) (integrable_const _), integral_const,
    probReal_univ, one_smul] at h

/- @[blueprint "lem:sf-sup-comparison-orthogonal"
  (statement := /-- \textbf{Sudakov--Fernique, orthogonal form.} If the rows of $A$ and $B$ are
    orthogonal and $\sum_i (B_{ji} - B_{ki})^2 \le \sum_i (A_{ji} - A_{ki})^2$ for all $j, k$,
    then $\int \max_j (Bg)_j\, d\gamma_N \le \int \max_j (Ag)_j\, d\gamma_N$
    (let $\beta \to \infty$ in the log-sum-exp comparison). -/)] -/
theorem integral_iSup_mulVec_le_of_orthogonal [Nonempty (Fin M)]
    (A B : Matrix (Fin M) (Fin N) ℝ) (hAB : ∀ j k, ∑ i, A j i * B k i = 0)
    (hinc : ∀ j k, ∑ i, (B j i - B k i) ^ 2 ≤ ∑ i, (A j i - A k i) ^ 2) :
    ∫ g, ⨆ j, (B.mulVec g) j ∂stdGaussianPi N ≤ ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hM : (1 : ℝ) ≤ M := by
    have : 0 < M := Fin.pos'
    exact_mod_cast this
  have hL : 0 ≤ Real.log M := Real.log_nonneg hM
  set β : ℝ := (Real.log M + 1) / ε with hβdef
  have hβ : 0 < β := by positivity
  have hlog : Real.log M / β ≤ ε := by
    rw [hβdef, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc ∫ g, ⨆ j, (B.mulVec g) j ∂stdGaussianPi N
      ≤ ∫ g, logSumExp β (B.mulVec g) ∂stdGaussianPi N :=
        integral_iSup_mulVec_le_integral_logSumExp hβ B
    _ ≤ ∫ g, logSumExp β (A.mulVec g) ∂stdGaussianPi N :=
        integral_logSumExp_mulVec_le_of_orthogonal hβ A B hAB hinc
    _ ≤ ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N + Real.log M / β :=
        integral_logSumExp_mulVec_le_integral_iSup_add hβ A
    _ ≤ ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N + ε := by linarith

/- @[blueprint "thm:sudakov-fernique"
  (statement := /-- \textbf{Sudakov--Fernique comparison inequality (matrix form).} Let
    $A \in \mathbb R^{M \times N}$, $B \in \mathbb R^{M \times N'}$ with $M \ge 1$, and let
    $X = Ag$, $Y = Bg'$ with $g \sim N(0,1)^{\otimes N}$, $g' \sim N(0,1)^{\otimes N'}$, so that
    $\mathbb E(X_j - X_k)^2 = \sum_i (A_{ji} - A_{ki})^2$ and
    $\mathbb E(Y_j - Y_k)^2 = \sum_i (B_{ji} - B_{ki})^2$. If
    \[ \sum_i (B_{ji} - B_{ki})^2 \le \sum_i (A_{ji} - A_{ki})^2 \qquad \text{for all } j, k, \]
    i.e.\ $\mathbb E(Y_j - Y_k)^2 \le \mathbb E(X_j - X_k)^2$, then
    \[ \mathbb E \max_j Y_j \le \mathbb E \max_j X_j , \qquad\text{i.e.}\qquad
      \int \max_j (Bg')_j\, d\gamma_{N'}(g') \le \int \max_j (Ag)_j\, d\gamma_N(g). \]
    (Vershynin, HDP, Thm 7.2.11; proof by interpolation $Z_\theta = \cos\theta\, Ag +
    \sin\theta\, Bg'$ and the smooth maximum $\operatorname{LSE}_\beta$.) -/)] -/
theorem integral_iSup_mulVec_le [Nonempty (Fin M)]
    (A : Matrix (Fin M) (Fin N) ℝ) (B : Matrix (Fin M) (Fin N') ℝ)
    (hinc : ∀ j k, ∑ i, (B j i - B k i) ^ 2 ≤ ∑ i, (A j i - A k i) ^ 2) :
    ∫ g, ⨆ j, (B.mulVec g) j ∂stdGaussianPi N' ≤ ∫ g, ⨆ j, (A.mulVec g) j ∂stdGaussianPi N := by
  rw [← integral_iSup_blockLeft A N', ← integral_iSup_blockRight N B]
  refine integral_iSup_mulVec_le_of_orthogonal (blockLeft A N') (blockRight N B)
    (sum_blockLeft_mul_blockRight A B) fun j k => ?_
  rw [sum_sq_sub_blockLeft, sum_sq_sub_blockRight]
  exact hinc j k

/- @[blueprint "cor:sudakov-fernique-increments"
  (statement := /-- \textbf{Sudakov--Fernique, increment form.} Let $u_j \in \mathbb R^N$,
    $v_j \in \mathbb R^{N'}$ ($j < M$, $M \ge 1$) and $X_j = \langle u_j, g\rangle$,
    $Y_j = \langle v_j, g'\rangle$. If $\|v_j - v_k\|_2^2 \le \|u_j - u_k\|_2^2$ for all $j, k$
    (i.e.\ $\mathbb E(Y_j - Y_k)^2 \le \mathbb E(X_j - X_k)^2$), then
    \[ \int \max_j \sum_i v_{j,i}\, g'_i\, d\gamma_{N'} \le
      \int \max_j \sum_i u_{j,i}\, g_i\, d\gamma_N . \] -/)] -/
theorem integral_iSup_linear_le [Nonempty (Fin M)] (u : Fin M → Fin N → ℝ) (v : Fin M → Fin N' → ℝ)
    (hinc : ∀ j k, ∑ i, (v j i - v k i) ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2) :
    ∫ g, ⨆ j, ∑ i, v j i * g i ∂stdGaussianPi N' ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N := by
  have h := integral_iSup_mulVec_le (Matrix.of u) (Matrix.of v) hinc
  simpa [Matrix.mulVec, dotProduct] using h

/- @[blueprint "lem:sum-sq-sub-smul-one"
  (statement := /-- For the scaled identity $cI_M$: $\sum_i ((cI)_{ji} - (cI)_{ki})^2 = 2c^2$ if
    $j \ne k$ and $0$ if $j = k$; in particular it is $\le 2c^2$. -/)] -/
theorem sum_sq_sub_smul_one_le (c : ℝ) (j k : Fin M) :
    ∑ i, ((c • (1 : Matrix (Fin M) (Fin M) ℝ)) j i - (c • (1 : Matrix (Fin M) (Fin M) ℝ)) k i) ^ 2
      ≤ 2 * c ^ 2 := by
  have h : ∀ i, ((c • (1 : Matrix (Fin M) (Fin M) ℝ)) j i
        - (c • (1 : Matrix (Fin M) (Fin M) ℝ)) k i) ^ 2
      = c ^ 2 * (if j = i then 1 else 0) + c ^ 2 * (if k = i then 1 else 0)
        - 2 * c ^ 2 * ((if j = i then 1 else 0) * (if k = i then 1 else 0)) := by
    intro i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have : 0 ≤ ∑ i, (if j = i then (1 : ℝ) else 0) * (if k = i then 1 else 0) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  nlinarith [sq_nonneg c]

/- @[blueprint "cor:sudakov-fernique-iid"
  (statement := /-- \textbf{Comparison with i.i.d.\ Gaussians.} Let $u_j \in \mathbb R^N$
    ($j < M$, $M \ge 1$) and $c \ge 0$ with $\|u_j - u_k\|_2^2 \ge 2c^2$ for all $j \ne k$. Then
    \[ c \int \max_{j} g_j\, d\gamma_M \le \int \max_j \sum_i u_{j,i}\, g_i\, d\gamma_N , \]
    (the process $Y_j = c\, g_j$ has increments $\mathbb E(Y_j - Y_k)^2 = 2c^2 \le
    \mathbb E(X_j - X_k)^2$). With $c = a/\sqrt2$ this is the input of the Gaussian Sudakov
    minoration. -/)] -/
theorem mul_integral_iSup_le_integral_iSup_linear [Nonempty (Fin M)] (u : Fin M → Fin N → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hsep : ∀ j k, j ≠ k → 2 * c ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2) :
    c * ∫ g, ⨆ j, g j ∂stdGaussianPi M ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N := by
  have h := integral_iSup_mulVec_le (Matrix.of u) (c • (1 : Matrix (Fin M) (Fin M) ℝ)) fun j k => by
    by_cases hjk : j = k
    · subst hjk; simp
    · exact (sum_sq_sub_smul_one_le c j k).trans (hsep j k hjk)
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at h
  rw [← integral_const_mul]
  simp_rw [Real.mul_iSup_of_nonneg hc]
  simpa [Matrix.mulVec, dotProduct] using h

end Main

end FoML.ToMathlib
