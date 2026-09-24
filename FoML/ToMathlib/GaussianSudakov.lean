import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
import FoML.ToMathlib.GaussianMaxLower
import FoML.ToMathlib.SudakovFernique

/-!
# The Gaussian Sudakov minoration

Row G8 of the Bernoulli–Sudakov blueprint (lean-deepgen's `00note/sudakov-math.md`, §2 step S4).

For `u : Fin M → Fin N → ℝ` write `g(u) := ∫ max_j ⟨u_j, g⟩ dγ_N` for the expected maximum of
the Gaussian process `X_j = ⟨u_j, g⟩`, `g ~ N(0,1)^{⊗N}`. If the vectors `u_j` are
`a`-separated in `ℓ₂`, i.e. `‖u_j − u_k‖₂ ≥ a` for `j ≠ k`, then

\[ g(u) \ge \frac{a}{6\sqrt2}\,\sqrt{\log M} \qquad (M \ge 2). \]

**Proof.** The i.i.d. process `Y_j = (a/√2) g_j` on `stdGaussianPi M` has increments
`E (Y_j − Y_k)² = a² ≤ ‖u_j − u_k‖₂² = E (X_j − X_k)²`, so the Sudakov–Fernique comparison
(`mul_integral_iSup_le_integral_iSup_linear`, `cor:sudakov-fernique-iid`) gives
`(a/√2) ∫ max_j g_j dγ_M ≤ g(u)`, and `∫ max_j g_j dγ_M ≥ (1/6) √(log M)`
(`gaussian_max_lower_explicit`, `thm:gaussian-max-lower-explicit`).

The note's constant `L₁ = √2 / c₀ = 10√2` becomes `6√2` with `c₀ = 1/6`.

We also record the separation hypothesis in the two forms used downstream
(`√(∑ (u_j − u_k)²) ≥ a` and the normalised metric `√((1/N) ∑ (u_j − u_k)²) ≥ ρ`) and the
trivial lower bound `g(u) ≥ 0` for `M ≥ 1`.
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace FoML.ToMathlib

variable {M N : ℕ}

/- @[blueprint "lem:integrable-iSup-linear"
  (statement := /-- For $M \ge 1$, $g \mapsto \max_j \sum_i u_{j,i} g_i$ is
    $\gamma_N$-integrable. -/)] -/
theorem integrable_iSup_linear [Nonempty (Fin M)] (u : Fin M → Fin N → ℝ) :
    Integrable (fun g : Fin N → ℝ => ⨆ j, ∑ i, u j i * g i) (stdGaussianPi N) := by
  have h := integrable_iSup_mulVec (Matrix.of u)
  simpa [Matrix.mulVec, dotProduct] using h

/- @[blueprint "lem:integrable-linear-std-gaussian-pi"
  (statement := /-- $\langle a, g\rangle = \sum_i a_i g_i$ is $\gamma_N$-integrable. -/)] -/
theorem integrable_linear_stdGaussianPi (a : Fin N → ℝ) :
    Integrable (fun g : Fin N → ℝ => ∑ i, a i * g i) (stdGaussianPi N) :=
  integrable_finsetSum _ fun i _ => (integrable_eval_stdGaussianPi i).const_mul (a i)

/- @[blueprint "lem:gaussian-sudakov-nonneg"
  (statement := /-- For $M \ge 1$ and any $u_j \in \mathbb R^N$,
    $\int \max_j \sum_i u_{j,i} g_i\, d\gamma_N \ge 0$: the maximum dominates the single centred
    term $\langle u_{j_0}, g\rangle$, whose mean is $0$. -/)] -/
theorem gaussian_sudakov_nonneg [Nonempty (Fin M)] (u : Fin M → Fin N → ℝ) :
    0 ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N := by
  /- Pick $j_0$; pointwise $\langle u_{j_0}, g\rangle \le \max_j \langle u_j, g\rangle$, integrate,
    and use $\mathbb E\langle u_{j_0}, g\rangle = 0$. -/
  obtain ⟨j₀⟩ := ‹Nonempty (Fin M)›
  have h : ∫ g, ∑ i, u j₀ i * g i ∂stdGaussianPi N
      ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N :=
    integral_mono (integrable_linear_stdGaussianPi (u j₀)) (integrable_iSup_linear u)
      fun g => le_ciSup (Set.finite_range fun j => ∑ i, u j i * g i).bddAbove j₀
  rwa [integral_linear_stdGaussianPi] at h

/- @[blueprint "lem:gaussian-sudakov-nonneg-of-one-le"
  (statement := /-- The same as `lem:gaussian-sudakov-nonneg` with the hypothesis $M \ge 1$. -/)] -/
theorem gaussian_sudakov_nonneg_of_one_le (hM : 1 ≤ M) (u : Fin M → Fin N → ℝ) :
    0 ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N :=
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  gaussian_sudakov_nonneg u

/- @[blueprint "lem:two-mul-div-sqrt-two-sq"
  (statement := /-- $2\,(a/\sqrt2)^2 = a^2$. -/)] -/
theorem two_mul_div_sqrt_two_sq (a : ℝ) : 2 * (a / √2) ^ 2 = a ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/- @[blueprint "thm:gaussian-sudakov"
  (statement := /-- \textbf{Gaussian Sudakov minoration.} Let $M \ge 2$, $u_j \in \mathbb R^N$
    ($j < M$) and $a \ge 0$ with $\|u_j - u_k\|_2^2 = \sum_i (u_{j,i} - u_{k,i})^2 \ge a^2$ for all
    $j \ne k$. Then
    \[ \frac{a}{6\sqrt2}\,\sqrt{\log M} \le \int \max_j \sum_i u_{j,i}\, g_i\, d\gamma_N(g) . \]
    (Step S4 of the note with $c_0 = 1/6$, so $L_1 = \sqrt2/c_0 = 6\sqrt2$.) -/)] -/
theorem gaussian_sudakov (hM : 2 ≤ M) (u : Fin M → Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hsep : ∀ j k, j ≠ k → a ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2) :
    a / (6 * √2) * √(Real.log M) ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N := by
  /- Compare with the i.i.d. process $Y_j = (a/\sqrt2)\, g_j$, whose increments are
    $\mathbb E(Y_j - Y_k)^2 = 2 (a/\sqrt2)^2 = a^2 \le \|u_j - u_k\|_2^2$
    (`cor:sudakov-fernique-iid`), then apply `thm:gaussian-max-lower-explicit`. -/
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have hc : 0 ≤ a / √2 := by positivity
  have hsep' : ∀ j k, j ≠ k → 2 * (a / √2) ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2 := by
    intro j k hjk
    rw [two_mul_div_sqrt_two_sq]
    exact hsep j k hjk
  have h1 := mul_integral_iSup_le_integral_iSup_linear u hc hsep'
  have h2 := gaussian_max_lower_explicit hM
  calc a / (6 * √2) * √(Real.log M) = a / √2 * (1 / 6 * √(Real.log M)) := by ring
    _ ≤ a / √2 * ∫ g, ⨆ j, g j ∂stdGaussianPi M := by gcongr
    _ ≤ _ := h1

/- @[blueprint "cor:gaussian-sudakov-euclid"
  (statement := /-- \textbf{Gaussian Sudakov minoration, Euclidean form.} Let $M \ge 2$,
    $u_j \in \mathbb R^N$ and $a \ge 0$ with
    $\sqrt{\sum_i (u_{j,i} - u_{k,i})^2} \ge a$ for all $j \ne k$. Then
    \[ \frac{a}{6\sqrt2}\,\sqrt{\log M} \le
      \int \max_j \sum_i u_{j,i}\, g_i\, d\gamma_N(g) . \] -/)] -/
theorem gaussian_sudakov_euclid (hM : 2 ≤ M) (u : Fin M → Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hsep : ∀ j k, j ≠ k → a ≤ Real.sqrt (∑ i, (u j i - u k i) ^ 2)) :
    a / (6 * √2) * √(Real.log M) ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N :=
  gaussian_sudakov hM u ha fun j k hjk => by
    /- Square the separation hypothesis. -/
    have h := hsep j k hjk
    calc a ^ 2 ≤ (Real.sqrt (∑ i, (u j i - u k i) ^ 2)) ^ 2 := by gcongr
      _ = ∑ i, (u j i - u k i) ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/- @[blueprint "lem:sqrt-normalized-mul-sqrt-le"
  (statement := /-- For $S \ge 0$ and $N \in \mathbb N$:
    $\sqrt{S/N}\,\sqrt N \le \sqrt S$ (with equality for $N \ge 1$; for $N = 0$ the left side is
    $0$ by the convention $1/0 = 0$). -/)] -/
theorem sqrt_div_mul_sqrt_le {S : ℝ} (hS : 0 ≤ S) (N : ℕ) :
    Real.sqrt (1 / (N : ℝ) * S) * Real.sqrt N ≤ Real.sqrt S := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN, hS]
  · have hN' : (N : ℝ) ≠ 0 := by positivity
    rw [one_div, inv_mul_eq_div, div_mul_cancel₀ S hN']

/- @[blueprint "cor:gaussian-sudakov-normalized"
  (statement := /-- \textbf{Gaussian Sudakov minoration, normalised metric.} Let $M \ge 2$,
    $u_j \in \mathbb R^N$ and $\rho \ge 0$ with
    $\sqrt{\tfrac1N \sum_i (u_{j,i} - u_{k,i})^2} \ge \rho$ for all $j \ne k$. Then
    \[ \frac{\rho\sqrt N}{6\sqrt2}\,\sqrt{\log M} \le
      \int \max_j \sum_i u_{j,i}\, g_i\, d\gamma_N(g) . \] -/)] -/
theorem gaussian_sudakov_normalized (hM : 2 ≤ M) (u : Fin M → Fin N → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsep : ∀ j k, j ≠ k → ρ ≤ Real.sqrt (1 / (N : ℝ) * ∑ i, (u j i - u k i) ^ 2)) :
    ρ * Real.sqrt N / (6 * √2) * √(Real.log M)
      ≤ ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi N :=
  gaussian_sudakov_euclid hM u (by positivity) fun j k hjk => by
    /- Multiply the normalised separation by $\sqrt N$. -/
    calc ρ * Real.sqrt N ≤ Real.sqrt (1 / (N : ℝ) * ∑ i, (u j i - u k i) ^ 2) * Real.sqrt N := by
          gcongr; exact hsep j k hjk
      _ ≤ Real.sqrt (∑ i, (u j i - u k i) ^ 2) :=
        sqrt_div_mul_sqrt_le (Finset.sum_nonneg fun i _ => sq_nonneg _) N

end FoML.ToMathlib
