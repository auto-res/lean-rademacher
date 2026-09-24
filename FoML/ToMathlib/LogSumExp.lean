import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Log-sum-exp: bounds, gradient (softmax) and Hessian

Prerequisite G6 of the Bernoulli–Sudakov plan (`PLAN.md` §7).

For `β > 0` and `x : Fin M → ℝ` the *log-sum-exp* is
`logSumExp β x = β⁻¹ log ∑ⱼ exp(β xⱼ)`, a smooth approximation of `max_j x_j`:

* `max ≤ logSumExp β x ≤ max + log M / β` (`le_logSumExp`, `iSup_le_logSumExp`,
  `logSumExp_le_iSup_add`);
* the gradient is the softmax `p_j = e^{β x_j} / ∑ₖ e^{β x_k}` (`hasFDerivAt_logSumExp`),
  with `p_j ≥ 0`, `∑ p_j = 1` (`softmax_nonneg`, `sum_softmax`);
* the Hessian is `∂_j ∂_k logSumExp = β (δ_{jk} p_j − p_j p_k)` (`hasFDerivAt_softmax`);
* `logSumExp β` and `softmax β · j` are `C^∞` (`contDiff_logSumExp`, `contDiff_softmax`);
* the algebraic identity `∑_{j,k} β (δ_{jk} p_j − p_j p_k) Q_{jk}
  = (β/2) ∑_{j,k} p_j p_k (Q_{jj} + Q_{kk} − 2 Q_{jk})` (`hessian_quadratic`; note the sign: for
  `Q = v vᵀ` this is `β · Var_p(v) ≥ 0`, the convexity of `logSumExp`), which gives the sign
  `≥ 0` used in the Sudakov–Fernique interpolation (`hessian_quadratic_nonneg`,
  `sum_lseHessian_mul_nonneg`): with `Q = Σ^X − Σ^Y`, `Q_{jj} + Q_{kk} − 2Q_{jk}
  = E(X_j − X_k)² − E(Y_j − Y_k)² ≥ 0` gives `d/dθ E logSumExp(Z_θ) ≥ 0`.

## Representation of derivatives

Fréchet derivatives are stated with the continuous linear map `linComb c : (Fin M → ℝ) →L[ℝ] ℝ`,
`v ↦ ∑ₖ cₖ vₖ` (`linComb_apply`), so that `linComb c (Pi.single k 1) = c k` (`linComb_single`).
Partial derivatives in the form used by the Gaussian integration by parts
(`FoML.ToMathlib.GaussianIntegrationByParts`) are the derivatives of the one-variable slices
`t ↦ f (Function.update x j t)` (`hasDerivAt_logSumExp_update`, `hasDerivAt_softmax_update`), and
`fderiv ℝ f x (Pi.single k 1)` is also provided (`fderiv_logSumExp_single`,
`fderiv_softmax_single`).

This file depends only on Mathlib (`Architect` annotations are commented out).
-/

open Finset

namespace FoML.ToMathlib

variable {M : ℕ}

section LinComb

/- @[blueprint "def:lin-comb"
  (statement := /-- For $c \in \mathbb R^M$, $\operatorname{linComb}(c) : v \mapsto \sum_k c_k v_k$
    is the corresponding continuous linear functional on $\mathbb R^M$. -/)] -/
noncomputable def linComb (c : Fin M → ℝ) : (Fin M → ℝ) →L[ℝ] ℝ :=
  ∑ k, c k • ContinuousLinearMap.proj k

/- @[blueprint "lem:lin-comb-apply"
  (statement := /-- $\operatorname{linComb}(c)(v) = \sum_k c_k v_k$. -/)] -/
theorem linComb_apply (c v : Fin M → ℝ) : linComb c v = ∑ k, c k * v k := by
  simp [linComb, _root_.sum_apply]

attribute [simp] linComb_apply

/- @[blueprint "lem:lin-comb-single"
  (statement := /-- $\operatorname{linComb}(c)(e_k) = c_k$. -/)] -/
theorem linComb_single (c : Fin M → ℝ) (k : Fin M) : linComb c (Pi.single k 1) = c k := by
  simp [Pi.single_apply]

attribute [simp] linComb_single

end LinComb

section Def

/- @[blueprint "def:log-sum-exp"
  (statement := /-- For $\beta > 0$ and $x \in \mathbb R^M$, the \emph{log-sum-exp} is
    $\operatorname{LSE}_\beta(x) := \beta^{-1} \log \sum_{j=1}^M e^{\beta x_j}$. -/)] -/
noncomputable def logSumExp (β : ℝ) (x : Fin M → ℝ) : ℝ :=
  β⁻¹ * Real.log (∑ j, Real.exp (β * x j))

/- @[blueprint "def:softmax"
  (statement := /-- The \emph{softmax} $p_j(x) := e^{\beta x_j} / \sum_k e^{\beta x_k}$. -/)] -/
noncomputable def softmax (β : ℝ) (x : Fin M → ℝ) (j : Fin M) : ℝ :=
  Real.exp (β * x j) / ∑ k, Real.exp (β * x k)

/- @[blueprint "lem:sum-exp-pos"
  (statement := /-- For $M \ge 1$, $\sum_k e^{\beta x_k} > 0$. -/)] -/
theorem sum_exp_pos [Nonempty (Fin M)] (β : ℝ) (x : Fin M → ℝ) :
    0 < ∑ k, Real.exp (β * x k) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/- @[blueprint "lem:softmax-nonneg"
  (statement := /-- $p_j(x) \ge 0$. -/)] -/
theorem softmax_nonneg (β : ℝ) (x : Fin M → ℝ) (j : Fin M) : 0 ≤ softmax β x j :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

/- @[blueprint "lem:softmax-le-one"
  (statement := /-- $p_j(x) \le 1$. -/)] -/
theorem softmax_le_one (β : ℝ) (x : Fin M → ℝ) (j : Fin M) : softmax β x j ≤ 1 := by
  haveI : Nonempty (Fin M) := ⟨j⟩
  rw [softmax, div_le_one (sum_exp_pos β x)]
  exact single_le_sum (f := fun k => Real.exp (β * x k)) (fun _ _ => (Real.exp_pos _).le)
    (mem_univ j)

/- @[blueprint "lem:sum-softmax"
  (statement := /-- For $M \ge 1$, $\sum_j p_j(x) = 1$. -/)] -/
theorem sum_softmax [Nonempty (Fin M)] (β : ℝ) (x : Fin M → ℝ) : ∑ j, softmax β x j = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (sum_exp_pos β x).ne'

end Def

section Bounds

/- @[blueprint "lem:le-lse"
  (statement := /-- For $\beta > 0$ and every $j$, $x_j \le \operatorname{LSE}_\beta(x)$. -/)] -/
theorem le_logSumExp {β : ℝ} (hβ : 0 < β) (x : Fin M → ℝ) (j : Fin M) :
    x j ≤ logSumExp β x := by
  haveI : Nonempty (Fin M) := ⟨j⟩
  rw [logSumExp, ← div_eq_inv_mul, le_div_iff₀ hβ, mul_comm,
    Real.le_log_iff_exp_le (sum_exp_pos β x)]
  exact single_le_sum (f := fun k => Real.exp (β * x k)) (fun _ _ => (Real.exp_pos _).le)
    (mem_univ j)

/- @[blueprint "lem:max-le-lse"
  (statement := /-- For $\beta > 0$ and $M \ge 1$,
    $\max_j x_j \le \operatorname{LSE}_\beta(x)$. -/)] -/
theorem iSup_le_logSumExp [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β) (x : Fin M → ℝ) :
    (⨆ j, x j) ≤ logSumExp β x :=
  ciSup_le (le_logSumExp hβ x)

/- @[blueprint "lem:lse-le-max-add"
  (statement := /-- For $\beta > 0$ and $M \ge 1$,
    $\operatorname{LSE}_\beta(x) \le \max_j x_j + \log M / \beta$. -/)] -/
theorem logSumExp_le_iSup_add [Nonempty (Fin M)] {β : ℝ} (hβ : 0 < β) (x : Fin M → ℝ) :
    logSumExp β x ≤ (⨆ j, x j) + Real.log M / β := by
  set m := ⨆ j, x j with hm
  have hM : (0 : ℝ) < M := by
    have : 0 < M := Fin.pos'
    exact_mod_cast this
  have hle : ∑ k, Real.exp (β * x k) ≤ M * Real.exp (β * m) := by
    have := Finset.sum_le_card_nsmul univ (fun k => Real.exp (β * x k)) (Real.exp (β * m))
      (fun k _ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_ciSup (Finite.bddAbove_range x) k) hβ.le))
    simpa [nsmul_eq_mul] using this
  have hlog : Real.log (∑ k, Real.exp (β * x k)) ≤ Real.log M + β * m := by
    calc Real.log (∑ k, Real.exp (β * x k)) ≤ Real.log (M * Real.exp (β * m)) :=
          Real.log_le_log (sum_exp_pos β x) hle
      _ = Real.log M + β * m := by rw [Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp]
  calc logSumExp β x = β⁻¹ * Real.log (∑ k, Real.exp (β * x k)) := rfl
    _ ≤ β⁻¹ * (Real.log M + β * m) := mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hβ.le)
    _ = m + Real.log M / β := by field_simp; ring

end Bounds

section Derivatives

variable (β : ℝ)

/- The denominator `S(x) = ∑ₖ exp(β xₖ)` of the softmax. -/
private noncomputable def sumExp (x : Fin M → ℝ) : ℝ := ∑ k, Real.exp (β * x k)

private theorem hasFDerivAt_sumExp (x : Fin M → ℝ) :
    HasFDerivAt (sumExp β) (linComb fun k => β * Real.exp (β * x k)) x := by
  have h : ∀ k ∈ (univ : Finset (Fin M)),
      HasFDerivAt (fun x : Fin M → ℝ => Real.exp (β * x k))
        (Real.exp (β * x k) • (β • ContinuousLinearMap.proj k)) x :=
    fun k _ => ((hasFDerivAt_apply k x).const_mul β).exp
  have := HasFDerivAt.sum h
  rw [show (∑ k, fun x : Fin M → ℝ => Real.exp (β * x k)) = sumExp β from
    funext fun x => by simp [sumExp, Finset.sum_apply]] at this
  refine this.congr_fderiv ?_
  ext v
  simp only [_root_.sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    linComb_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem contDiff_sumExp {n : WithTop ℕ∞} : ContDiff ℝ n (sumExp β : (Fin M → ℝ) → ℝ) :=
  ContDiff.sum fun k _ => (contDiff_const.mul (contDiff_apply ℝ ℝ k)).exp

/- @[blueprint "lem:lse-hasFDerivAt"
  (statement := /-- For $\beta \ne 0$ and $M \ge 1$, $\operatorname{LSE}_\beta$ is Fréchet
    differentiable at every $x$ with gradient the softmax:
    $D\operatorname{LSE}_\beta(x)[v] = \sum_j p_j(x)\, v_j$. -/)] -/
theorem hasFDerivAt_logSumExp [Nonempty (Fin M)] {β : ℝ} (hβ : β ≠ 0) (x : Fin M → ℝ) :
    HasFDerivAt (logSumExp β) (linComb (softmax β x)) x := by
  have h := ((hasFDerivAt_sumExp β x).log (sum_exp_pos β x).ne').const_mul β⁻¹
  refine h.congr_fderiv ?_
  ext v
  simp only [linComb_apply, smul_apply, smul_eq_mul, sumExp, softmax, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

/- @[blueprint "lem:lse-contDiff"
  (statement := /-- For $M \ge 1$, $\operatorname{LSE}_\beta$ is $C^\infty$. -/)] -/
theorem contDiff_logSumExp [Nonempty (Fin M)] {n : WithTop ℕ∞} :
    ContDiff ℝ n (logSumExp β : (Fin M → ℝ) → ℝ) :=
  contDiff_const.mul ((contDiff_sumExp β).log fun x => (sum_exp_pos β x).ne')

/- @[blueprint "lem:lse-partial"
  (statement := /-- For $\beta \ne 0$, the partial derivative of $\operatorname{LSE}_\beta$ in
    the $j$-th coordinate is the softmax: $t \mapsto \operatorname{LSE}_\beta(x[j \leftarrow t])$
    has derivative $p_j(x[j \leftarrow t])$ at $t$. -/)] -/
theorem hasDerivAt_logSumExp_update {β : ℝ} (hβ : β ≠ 0) (x : Fin M → ℝ) (j : Fin M) (t : ℝ) :
    HasDerivAt (fun s => logSumExp β (Function.update x j s))
      (softmax β (Function.update x j t) j) t := by
  haveI : Nonempty (Fin M) := ⟨j⟩
  have := (hasFDerivAt_logSumExp hβ (Function.update x j t)).comp_hasDerivAt t
    (hasDerivAt_update x j t)
  rw [linComb_single] at this
  exact this

/- @[blueprint "lem:lse-fderiv-single"
  (statement := /-- $\partial_k \operatorname{LSE}_\beta(x) = p_k(x)$ for $\beta \ne 0$. -/)] -/
theorem fderiv_logSumExp_single [Nonempty (Fin M)] {β : ℝ} (hβ : β ≠ 0) (x : Fin M → ℝ)
    (k : Fin M) : fderiv ℝ (logSumExp β) x (Pi.single k 1) = softmax β x k := by
  rw [(hasFDerivAt_logSumExp hβ x).fderiv, linComb_single]

/- @[blueprint "lem:softmax-eq-exp-sub"
  (statement := /-- $p_j(x) = \exp(\beta x_j - \log \sum_k e^{\beta x_k})$. -/)] -/
theorem softmax_eq_exp_sub [Nonempty (Fin M)] (x : Fin M → ℝ) (j : Fin M) :
    softmax β x j = Real.exp (β * x j - Real.log (∑ k, Real.exp (β * x k))) := by
  rw [Real.exp_sub, Real.exp_log (sum_exp_pos β x), softmax]

/- The Hessian entries `β (δ_{jk} p_j − p_j p_k)` of `logSumExp β` at `x`. -/
/- @[blueprint "def:lse-hessian"
  (statement := /-- $H_{jk}(x) := \beta\,(\delta_{jk} p_j(x) - p_j(x) p_k(x))$. -/)] -/
noncomputable def lseHessian (x : Fin M → ℝ) (j k : Fin M) : ℝ :=
  β * ((if j = k then softmax β x j else 0) - softmax β x j * softmax β x k)

/- @[blueprint "lem:lse-hessian"
  (statement := /-- For $M \ge 1$, $p_j$ is Fréchet differentiable with
    $D p_j(x)[v] = \sum_k \beta (\delta_{jk} p_j - p_j p_k)\, v_k$; i.e. the Hessian of
    $\operatorname{LSE}_\beta$ is $\partial_j \partial_k \operatorname{LSE}_\beta(x)
    = \beta (\delta_{jk} p_j(x) - p_j(x) p_k(x))$. -/)] -/
theorem hasFDerivAt_softmax [Nonempty (Fin M)] (x : Fin M → ℝ) (j : Fin M) :
    HasFDerivAt (fun y => softmax β y j) (linComb (lseHessian β x j)) x := by
  have hfun : (fun y => softmax β y j) =
      fun y => Real.exp (β * y j - Real.log (sumExp β y)) :=
    funext fun y => softmax_eq_exp_sub β y j
  rw [hfun]
  have h := (((hasFDerivAt_apply j x).const_mul β).sub
    ((hasFDerivAt_sumExp β x).log (sum_exp_pos β x).ne')).exp
  refine h.congr_fderiv ?_
  ext v
  have hS : (∑ k, Real.exp (β * x k)) ≠ 0 := (sum_exp_pos β x).ne'
  have hp : Real.exp (β * x j - Real.log (∑ k, Real.exp (β * x k))) = softmax β x j :=
    (softmax_eq_exp_sub β x j).symm
  have hR : ∑ k, β * ((if j = k then softmax β x j else 0) - softmax β x j * softmax β x k) * v k
      = β * softmax β x j * v j - β * softmax β x j * ∑ k, softmax β x k * v k := by
    have : ∀ k, β * ((if j = k then softmax β x j else 0) - softmax β x j * softmax β x k) * v k
        = (if j = k then β * softmax β x j * v k else 0)
          - β * softmax β x j * (softmax β x k * v k) := by
      intro k; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, mem_univ, if_true,
      ← Finset.mul_sum]
  have hsum : (∑ k, Real.exp (β * x k))⁻¹ * ∑ k, β * Real.exp (β * x k) * v k
      = β * ∑ k, softmax β x k * v k := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [softmax]
    field_simp
  simp only [linComb_apply, lseHessian, smul_apply, sub_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.sub_apply, sumExp, hp]
  rw [hR, hsum]
  ring

/- @[blueprint "lem:softmax-contDiff"
  (statement := /-- For $M \ge 1$, $p_j$ is $C^\infty$. -/)] -/
theorem contDiff_softmax [Nonempty (Fin M)] {n : WithTop ℕ∞} (j : Fin M) :
    ContDiff ℝ n (fun y : Fin M → ℝ => softmax β y j) := by
  have hfun : (fun y : Fin M → ℝ => softmax β y j) =
      fun y => Real.exp (β * y j - Real.log (sumExp β y)) :=
    funext fun y => softmax_eq_exp_sub β y j
  rw [hfun]
  exact ((contDiff_const.mul (contDiff_apply ℝ ℝ j)).sub
    ((contDiff_sumExp β).log fun x => (sum_exp_pos β x).ne')).exp

/- @[blueprint "lem:softmax-partial"
  (statement := /-- $t \mapsto p_j(x[k \leftarrow t])$ has derivative
    $H_{jk}(x[k \leftarrow t]) = \beta (\delta_{jk} p_j - p_j p_k)(x[k \leftarrow t])$ at $t$. -/)] -/
theorem hasDerivAt_softmax_update (x : Fin M → ℝ) (j k : Fin M) (t : ℝ) :
    HasDerivAt (fun s => softmax β (Function.update x k s) j)
      (lseHessian β (Function.update x k t) j k) t := by
  haveI : Nonempty (Fin M) := ⟨j⟩
  have := (hasFDerivAt_softmax β (Function.update x k t) j).comp_hasDerivAt t
    (hasDerivAt_update x k t)
  rw [linComb_single] at this
  exact this

/- @[blueprint "lem:softmax-fderiv-single"
  (statement := /-- $\partial_k p_j(x) = H_{jk}(x)$. -/)] -/
theorem fderiv_softmax_single [Nonempty (Fin M)] (x : Fin M → ℝ) (j k : Fin M) :
    fderiv ℝ (fun y => softmax β y j) x (Pi.single k 1) = lseHessian β x j k := by
  rw [(hasFDerivAt_softmax β x j).fderiv, linComb_single]

/- @[blueprint "lem:lse-hessian-bound"
  (statement := /-- $|H_{jk}(x)| \le |\beta|$. -/)] -/
theorem abs_lseHessian_le (x : Fin M → ℝ) (j k : Fin M) : |lseHessian β x j k| ≤ |β| := by
  rw [lseHessian, abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨?_, ?_⟩)
  · have := mul_le_one₀ (softmax_le_one β x j) (softmax_nonneg β x k) (softmax_le_one β x k)
    split_ifs <;>
      nlinarith [softmax_nonneg β x j, mul_nonneg (softmax_nonneg β x j) (softmax_nonneg β x k)]
  · have := mul_nonneg (softmax_nonneg β x j) (softmax_nonneg β x k)
    split_ifs <;> nlinarith [softmax_le_one β x j]

end Derivatives

section Quadratic

/- @[blueprint "lem:lse-hessian-quadratic"
  (statement := /-- \textbf{Hessian quadratic form.} If $\sum_j p_j = 1$, then for every
    $Q \in \mathbb R^{M \times M}$ (symmetry is not needed)
    \[ \sum_{j,k} \beta (\delta_{jk} p_j - p_j p_k)\, Q_{jk}
      = \frac{\beta}{2} \sum_{j,k} p_j p_k \,(Q_{jj} + Q_{kk} - 2 Q_{jk}). \]
    (For $Q = v v^\top$ the right-hand side is $\beta \operatorname{Var}_p(v) \ge 0$: the
    convexity of $\operatorname{LSE}_\beta$.) -/)] -/
theorem hessian_quadratic (β : ℝ) (p : Fin M → ℝ) (hp : ∑ j, p j = 1) (Q : Fin M → Fin M → ℝ) :
    ∑ j, ∑ k, β * ((if j = k then p j else 0) - p j * p k) * Q j k
      = (β / 2) * ∑ j, ∑ k, p j * p k * (Q j j + Q k k - 2 * Q j k) := by
  have h1 : ∀ j, ∑ k, (if j = k then p j else 0) * Q j k = p j * Q j j := by
    intro j
    simp [ite_mul]
  have h2 : ∑ j, ∑ k, p j * p k * Q j j = ∑ j, p j * Q j j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ∑ k, p j * p k * Q j j = p j * Q j j * ∑ k, p k := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = p j * Q j j := by rw [hp, mul_one]
  have h3 : ∑ j, ∑ k, p j * p k * Q k k = ∑ k, p k * Q k k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc ∑ j, p j * p k * Q k k = p k * Q k k * ∑ j, p j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = p k * Q k k := by rw [hp, mul_one]
  have hL : ∑ j, ∑ k, β * ((if j = k then p j else 0) - p j * p k) * Q j k
      = β * (∑ j, p j * Q j j - ∑ j, ∑ k, p j * p k * Q j k) := by
    have : ∀ j k, β * ((if j = k then p j else 0) - p j * p k) * Q j k
        = β * ((if j = k then p j else 0) * Q j k) - β * (p j * p k * Q j k) := fun j k => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
    ring
  have hR : ∑ j, ∑ k, p j * p k * (Q j j + Q k k - 2 * Q j k)
      = ∑ j, p j * Q j j + ∑ k, p k * Q k k - 2 * ∑ j, ∑ k, p j * p k * Q j k := by
    have : ∀ j k, p j * p k * (Q j j + Q k k - 2 * Q j k)
        = p j * p k * Q j j + p j * p k * Q k k - 2 * (p j * p k * Q j k) := fun j k => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h2, h3]
  rw [hL, hR]
  ring

/- @[blueprint "lem:lse-hessian-quadratic-nonneg"
  (statement := /-- If $\beta \ge 0$, $p_j \ge 0$, $\sum_j p_j = 1$ and
    $Q_{jj} + Q_{kk} - 2 Q_{jk} \ge 0$ for all $j, k$ (e.g. $Q = \Sigma^X - \Sigma^Y$ with
    $\mathbb E(X_j - X_k)^2 \ge \mathbb E(Y_j - Y_k)^2$, the Sudakov--Fernique hypothesis), then
    $\sum_{j,k} \beta (\delta_{jk} p_j - p_j p_k)\, Q_{jk} \ge 0$. -/)] -/
theorem hessian_quadratic_nonneg {β : ℝ} (hβ : 0 ≤ β) {p : Fin M → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : ∑ j, p j = 1) {Q : Fin M → Fin M → ℝ} (hQ : ∀ j k, 0 ≤ Q j j + Q k k - 2 * Q j k) :
    0 ≤ ∑ j, ∑ k, β * ((if j = k then p j else 0) - p j * p k) * Q j k := by
  rw [hessian_quadratic β p hp Q]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_)
  exact mul_nonneg (mul_nonneg (hp0 j) (hp0 k)) (hQ j k)

/- @[blueprint "lem:lse-hessian-quadratic-softmax"
  (statement := /-- For $\beta \ge 0$, $M \ge 1$ and $Q$ with $Q_{jj} + Q_{kk} - 2Q_{jk} \ge 0$,
    $\sum_{j,k} H_{jk}(x)\, Q_{jk} \ge 0$ where $H$ is the Hessian of
    $\operatorname{LSE}_\beta$. -/)] -/
theorem sum_lseHessian_mul_nonneg [Nonempty (Fin M)] {β : ℝ} (hβ : 0 ≤ β) (x : Fin M → ℝ)
    {Q : Fin M → Fin M → ℝ} (hQ : ∀ j k, 0 ≤ Q j j + Q k k - 2 * Q j k) :
    0 ≤ ∑ j, ∑ k, lseHessian β x j k * Q j k :=
  hessian_quadratic_nonneg hβ (softmax_nonneg β x) (sum_softmax β x) hQ

end Quadratic

end FoML.ToMathlib
