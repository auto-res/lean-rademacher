import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# The standard Gaussian product measure on `Fin n → ℝ`

`stdGaussianPi n := Measure.pi (fun _ ↦ gaussianReal 0 1)` is the law of `n` i.i.d. standard
Gaussian random variables. We record the elementary facts about it that are needed for
Gaussian comparison arguments (Sudakov minoration):

* it is a probability measure, each coordinate has law `gaussianReal 0 1`, and the coordinates
  are independent (`iIndepFun`);
* every linear functional `g ↦ ∑ i, a i * g i` is Gaussian with mean `0` and variance
  `∑ i, a i ^ 2`; consequently it has all moments, exponential moments, the explicit
  moment-generating function `exp (t ^ 2 * ∑ a i ^ 2 / 2)` and second moment `∑ a i ^ 2`;
* the difference of two distinct coordinates has law `gaussianReal 0 2`.

This file depends only on Mathlib (`Architect` annotations are commented out).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace FoML.ToMathlib

/- @[blueprint "def:std-gaussian-pi"
  (statement := /-- The standard Gaussian measure on $\mathbb R^n$: the product
    $\gamma_n := \bigotimes_{i < n} N(0,1)$ on $\mathrm{Fin}\, n \to \mathbb R$, i.e. the joint
    law of $n$ i.i.d. standard Gaussian variables $g_1, \dots, g_n$. -/)] -/
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

/- @[blueprint "lem:std-gaussian-pi-prob"
  (statement := /-- $\gamma_n$ is a probability measure. -/)] -/
instance instIsProbabilityMeasureStdGaussianPi (n : ℕ) :
    IsProbabilityMeasure (stdGaussianPi n) := by
  unfold stdGaussianPi; infer_instance

variable {n : ℕ}

/- @[blueprint "lem:std-gaussian-pi-eval-measurePreserving"
  (statement := /-- Each coordinate projection $g \mapsto g_i$ is measure preserving from
    $\gamma_n$ to $N(0,1)$. -/)] -/
theorem measurePreserving_eval_stdGaussianPi (i : Fin n) :
    MeasurePreserving (fun g : Fin n → ℝ => g i) (stdGaussianPi n) (gaussianReal 0 1) :=
  measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i

/- @[blueprint "lem:std-gaussian-pi-eval"
  (statement := /-- The law of each coordinate under $\gamma_n$ is $N(0,1)$:
    $(g \mapsto g_i)_* \gamma_n = N(0,1)$. -/)] -/
theorem stdGaussianPi_map_eval (i : Fin n) :
    (stdGaussianPi n).map (fun g => g i) = gaussianReal 0 1 :=
  (measurePreserving_eval_stdGaussianPi i).map_eq

/- @[blueprint "lem:std-gaussian-pi-eval-hasLaw"
  (statement := /-- `HasLaw` form of the previous lemma. -/)] -/
theorem hasLaw_eval_stdGaussianPi (i : Fin n) :
    HasLaw (fun g : Fin n → ℝ => g i) (gaussianReal 0 1) (stdGaussianPi n) :=
  (measurePreserving_eval_stdGaussianPi i).hasLaw

/- @[blueprint "lem:std-gaussian-pi-indep"
  (statement := /-- The coordinates $g_1, \dots, g_n$ are (mutually) independent under
    $\gamma_n$. -/)] -/
theorem iIndepFun_eval_stdGaussianPi :
    iIndepFun (fun (i : Fin n) (g : Fin n → ℝ) => g i) (stdGaussianPi n) :=
  iIndepFun_pi (μ := fun _ : Fin n => gaussianReal 0 1) (X := fun _ => id)
    (fun _ => aemeasurable_id)

/- @[blueprint "lem:std-gaussian-pi-eval-memLp"
  (statement := /-- Each coordinate has all moments: $g_i \in L^p(\gamma_n)$ for every
    $p < \infty$. -/)] -/
theorem memLp_eval_stdGaussianPi (i : Fin n) (p : ℝ≥0) :
    MemLp (fun g : Fin n → ℝ => g i) p (stdGaussianPi n) :=
  (memLp_id_gaussianReal p).comp_measurePreserving (measurePreserving_eval_stdGaussianPi i)

/- @[blueprint "lem:std-gaussian-pi-eval-integrable"
  (statement := /-- Each coordinate is integrable, with $\mathbb E\, g_i = 0$. -/)] -/
theorem integrable_eval_stdGaussianPi (i : Fin n) :
    Integrable (fun g : Fin n → ℝ => g i) (stdGaussianPi n) :=
  (memLp_eval_stdGaussianPi i 1).integrable le_rfl

/- @[blueprint "lem:std-gaussian-pi-eval-integral"
  (statement := /-- $\mathbb E_{\gamma_n}\, g_i = 0$. -/)] -/
theorem integral_eval_stdGaussianPi (i : Fin n) :
    ∫ g, g i ∂stdGaussianPi n = 0 := by
  rw [(hasLaw_eval_stdGaussianPi i).integral_eq, integral_id_gaussianReal]

/-! ### Linear functionals -/

/- @[blueprint "lem:std-gaussian-pi-linear-hasGaussianLaw"
  (statement := /-- For $a \in \mathbb R^n$, the linear functional
    $\langle a, g\rangle = \sum_i a_i g_i$ is a Gaussian random variable under $\gamma_n$
    (sum of independent Gaussians). -/)] -/
theorem hasGaussianLaw_linear_stdGaussianPi (a : Fin n → ℝ) :
    HasGaussianLaw (fun g : Fin n → ℝ => ∑ i, a i * g i) (stdGaussianPi n) := by
  /- Each summand $a_i g_i$ is Gaussian, the summands are independent, and a sum of independent
    Gaussians is Gaussian. -/
  have h1 : ∀ i, HasGaussianLaw (fun g : Fin n → ℝ => a i * g i) (stdGaussianPi n) := fun i =>
    (hasLaw_eval_stdGaussianPi i).hasGaussianLaw.fun_smul (a i)
  have h2 : iIndepFun (fun (i : Fin n) (g : Fin n → ℝ) => a i * g i) (stdGaussianPi n) :=
    iIndepFun_eval_stdGaussianPi.comp (fun i x => a i * x) (fun i => by fun_prop)
  exact iIndepFun.hasGaussianLaw_fun_sum h1 h2

/- @[blueprint "lem:std-gaussian-pi-linear-memLp"
  (statement := /-- $\langle a, g\rangle \in L^p(\gamma_n)$ for every $p < \infty$. -/)] -/
theorem memLp_linear_stdGaussianPi (a : Fin n → ℝ) (p : ℝ≥0) :
    MemLp (fun g : Fin n → ℝ => ∑ i, a i * g i) p (stdGaussianPi n) := by
  /- Finite sum of the coordinate moments. -/
  have : (fun g : Fin n → ℝ => ∑ i, a i * g i) = ∑ i, fun g : Fin n → ℝ => a i * g i := by
    ext g; simp [Finset.sum_apply]
  rw [this]
  exact memLp_finsetSum' _ fun i _ => (memLp_eval_stdGaussianPi i p).const_mul (a i)

/- @[blueprint "lem:std-gaussian-pi-linear-mean"
  (statement := /-- $\mathbb E_{\gamma_n}\langle a, g\rangle = 0$. -/)] -/
theorem integral_linear_stdGaussianPi (a : Fin n → ℝ) :
    ∫ g, ∑ i, a i * g i ∂stdGaussianPi n = 0 := by
  rw [integral_finsetSum _ fun i _ => (integrable_eval_stdGaussianPi i).const_mul (a i)]
  exact Finset.sum_eq_zero fun i _ => by
    rw [integral_const_mul, integral_eval_stdGaussianPi, mul_zero]

/- @[blueprint "lem:std-gaussian-pi-variance-linear'"
  (statement := /-- $\mathrm{Var}_{\gamma_n}\langle a, g\rangle = \sum_i a_i^2$. -/)] -/
theorem variance_linear_stdGaussianPi (a : Fin n → ℝ) :
    Var[fun g : Fin n → ℝ => ∑ i, a i * g i; stdGaussianPi n] = ∑ i, a i ^ 2 := by
  /- Variance of a sum of independent variables on a product space
    (`variance_sum_pi`), with $\mathrm{Var}(a_i g_i) = a_i^2$. -/
  have h := variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
  have h2 : ∀ i, Var[fun x : ℝ => a i * x; gaussianReal 0 1] = a i ^ 2 := fun i => by
    simpa [variance_fun_id_gaussianReal] using
      variance_const_mul (a i) (fun x : ℝ => x) (gaussianReal 0 1)
  simp only [h2] at h
  have hfun : (fun g : Fin n → ℝ => ∑ i, a i * g i) =
      ∑ i, fun g : Fin n → ℝ => a i * g i := by
    ext g; simp [Finset.sum_apply]
  rw [hfun]
  exact h

/- @[blueprint "lem:std-gaussian-pi-linear-law"
  (statement := /-- The law of $\langle a, g\rangle$ under $\gamma_n$ is
    $N\bigl(0, \sum_i a_i^2\bigr)$. -/)] -/
theorem stdGaussianPi_map_linear (a : Fin n → ℝ) :
    (stdGaussianPi n).map (fun g => ∑ i, a i * g i) =
      gaussianReal 0 (∑ i, a i ^ 2).toNNReal := by
  /- A real Gaussian variable has law $N(\mathbb E X, \mathrm{Var}\, X)$. -/
  rw [(hasGaussianLaw_linear_stdGaussianPi a).map_eq_gaussianReal,
    integral_linear_stdGaussianPi, variance_linear_stdGaussianPi]

/- @[blueprint "lem:std-gaussian-pi-linear-hasLaw"
  (statement := /-- `HasLaw` form of the previous lemma. -/)] -/
theorem hasLaw_linear_stdGaussianPi (a : Fin n → ℝ) :
    HasLaw (fun g : Fin n → ℝ => ∑ i, a i * g i) (gaussianReal 0 (∑ i, a i ^ 2).toNNReal)
      (stdGaussianPi n) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := stdGaussianPi_map_linear a

/- @[blueprint "lem:std-gaussian-pi-mgf-linear"
  (statement := /-- Moment generating function:
    $\mathbb E_{\gamma_n} \exp(t \langle a, g\rangle) = \exp\bigl(t^2 \sum_i a_i^2 / 2\bigr)$. -/)] -/
theorem integral_exp_linear_stdGaussianPi (a : Fin n → ℝ) (t : ℝ) :
    ∫ g, Real.exp (t * ∑ i, a i * g i) ∂stdGaussianPi n =
      Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 2) := by
  /- The MGF of $N(0,v)$ is $\exp(v t^2/2)$. -/
  have h := mgf_gaussianReal (stdGaussianPi_map_linear a) t
  rw [mgf] at h
  rw [h, Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  ring_nf

/- @[blueprint "lem:std-gaussian-pi-integrable-linear"
  (statement := /-- For $a \in \mathbb R^n$, $p \in \mathbb N$ and $\lambda \in \mathbb R$, the
    functions $g \mapsto |\langle a, g\rangle|^p$ and $g \mapsto \exp(\lambda \langle a, g\rangle)$
    are $\gamma_n$-integrable. -/)] -/
theorem integrable_abs_pow_linear_stdGaussianPi (a : Fin n → ℝ) (p : ℕ) :
    Integrable (fun g : Fin n → ℝ => |∑ i, a i * g i| ^ p) (stdGaussianPi n) := by
  /- $|\cdot|^p$-integrability is $L^p$ membership; all moments are finite. -/
  simpa [Real.norm_eq_abs] using (memLp_linear_stdGaussianPi a p).integrable_norm_pow'

/- @[blueprint "lem:std-gaussian-pi-integrable-exp-linear"
  (statement := /-- $g \mapsto \exp(\lambda \langle a, g\rangle)$ is $\gamma_n$-integrable. -/)] -/
theorem integrable_exp_linear_stdGaussianPi (a : Fin n → ℝ) (t : ℝ) :
    Integrable (fun g : Fin n → ℝ => Real.exp (t * ∑ i, a i * g i)) (stdGaussianPi n) := by
  /- Transport `integrable_exp_mul_gaussianReal` along the law of $\langle a, g\rangle$. -/
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := (∑ i, a i ^ 2).toNNReal) t
  rw [← stdGaussianPi_map_linear a] at h
  exact (integrable_map_measure (f := fun g : Fin n → ℝ => ∑ i, a i * g i)
    (g := fun x : ℝ => Real.exp (t * x)) (Measurable.aestronglyMeasurable (by fun_prop))
    (Measurable.aemeasurable (by fun_prop))).1 h

/- @[blueprint "lem:std-gaussian-pi-variance-linear"
  (statement := /-- Second moment: $\mathbb E_{\gamma_n} \langle a, g\rangle^2 = \sum_i a_i^2$. -/)] -/
theorem integral_sq_linear_stdGaussianPi (a : Fin n → ℝ) :
    ∫ g, (∑ i, a i * g i) ^ 2 ∂stdGaussianPi n = ∑ i, a i ^ 2 := by
  /- $\mathbb E X^2 = \mathrm{Var}\, X + (\mathbb E X)^2$ with $\mathbb E X = 0$. -/
  have h := variance_eq_sub (memLp_linear_stdGaussianPi a 2)
  rw [variance_linear_stdGaussianPi, integral_linear_stdGaussianPi] at h
  have : (fun g : Fin n → ℝ => ∑ i, a i * g i) ^ 2 =
      fun g : Fin n → ℝ => (∑ i, a i * g i) ^ 2 := by ext g; simp
  rw [this] at h
  linarith

/-! ### Difference of two coordinates -/

/- @[blueprint "lem:std-gaussian-pi-sub-law"
  (statement := /-- For $i \ne j$, the law of $g_i - g_j$ under $\gamma_n$ is $N(0, 2)$. -/)] -/
theorem stdGaussianPi_map_sub {i j : Fin n} (hij : i ≠ j) :
    (stdGaussianPi n).map (fun g => g i - g j) = gaussianReal 0 2 := by
  /- $g_i - g_j$ is Gaussian (difference of independent Gaussians) with mean $0$ and variance
    $\mathrm{Var}\, g_i + \mathrm{Var}\, g_j = 2$ (the covariance vanishes by independence). -/
  have hi := (hasLaw_eval_stdGaussianPi (n := n) i).hasGaussianLaw
  have hj := (hasLaw_eval_stdGaussianPi (n := n) j).hasGaussianLaw
  have hind : IndepFun (fun g : Fin n → ℝ => g i) (fun g : Fin n → ℝ => g j) (stdGaussianPi n) :=
    iIndepFun_eval_stdGaussianPi.indepFun hij
  have hG : HasGaussianLaw (fun g : Fin n → ℝ => g i - g j) (stdGaussianPi n) :=
    iIndepFun.hasGaussianLaw_fun_sub hi hj hind
  rw [hG.map_eq_gaussianReal]
  have hmean : ∫ g, g i - g j ∂stdGaussianPi n = 0 := by
    rw [integral_sub (integrable_eval_stdGaussianPi i) (integrable_eval_stdGaussianPi j),
      integral_eval_stdGaussianPi, integral_eval_stdGaussianPi, sub_zero]
  have hvar : Var[fun g : Fin n → ℝ => g i - g j; stdGaussianPi n] = 2 := by
    rw [variance_fun_sub (memLp_eval_stdGaussianPi i 2) (memLp_eval_stdGaussianPi j 2),
      hind.covariance_eq_zero (memLp_eval_stdGaussianPi i 2) (memLp_eval_stdGaussianPi j 2),
      (hasLaw_eval_stdGaussianPi i).variance_eq, (hasLaw_eval_stdGaussianPi j).variance_eq,
      variance_id_gaussianReal]
    norm_num
  rw [hmean, hvar]
  congr 1
  ext
  simp

end FoML.ToMathlib
