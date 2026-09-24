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
import FoML.ToFoML.BernoulliSudakovTools
import FoML.ToFoML.BernoulliSudakovIteration

/-!
# The Bernoulli–Sudakov minoration (B12)

Row B12 of the Bernoulli–Sudakov blueprint (lean-deepgen's `00note/sudakov-math.md`, §2 "final normalisation"):
the theorem `bernoulli_sudakov` (`thm:bernoulli-sudakov`) in the normalised form used by the
conditional Sudakov-type lower bound `thm:sudakov-type` (`LeanDeepgen.Bounds.Sudakov` in lean-deepgen):

`𝔼_σ max_j (1/n) ∑ᵢ σᵢ u j i ≥ c · min{ρ √(log M / n), ρ² / R}`,   `c := 1/L₀ = 1/(8 L₂)`,

for `u : Fin M → Fin n → ℝ` pairwise `ρ`-separated in the normalised Euclidean metric
`‖u j − u l‖_S = √((1/n) ∑ᵢ |u j i − u l i|²)` and bounded by `|u j i| ≤ R`.

**Proof.** The left-hand side is `(1/n) b(u)` (`lem:bernoulli-sup-eq-target`). For `M ≤ 1` the
right-hand side is `0` (`log M ≤ 0`, so `√(log M / n) = 0`) and `b(u) ≥ 0`
(`lem:bernoulli-sup-nonneg`, or `b(u) = 0` for `M = 0`). For `M ≥ 2` put `a := ρ √n`, `b := R`:
the separation hypothesis gives `a² = ρ² n ≤ ∑ᵢ (u j i − u l i)²`, the multiscale minoration
`lem:bernoulli-multiscale` (B11) gives `min(a √(log M), a²/R) / L₀ ≤ b(u)`, and dividing by `n`
turns the minimum into `min(ρ √(log M / n), ρ²/R)`.

This module is the last one of the Bernoulli–Sudakov development; it imports everything on which
the theorem depends. (The statement was previously in `FoML.ToFoML.SudakovMinoration`,
which is imported by the tool modules, hence the separate file.)

References: M. Talagrand, *Regularity of infinitely divisible processes*, Ann. Probab. 21
(1993), 362–432; M. Talagrand, *Upper and Lower Bounds for Stochastic Processes* (Springer,
2014), Thm. 6.4.1 (2nd ed.); M. Ledoux and M. Talagrand, *Probability in Banach Spaces*
(Springer, 1991), Ch. 4.
-/

open Real
open scoped BigOperators

namespace FoML.ToFoML

variable {n : ℕ}

/- @[blueprint "lem:bernoulli-sup-nonneg-any"
  (statement := /-- $b(u) \ge 0$ for every family (including the empty one, where
    $b(u) = 0$). -/)] -/
theorem bernoulliSup_nonneg' {M : ℕ} (u : Fin M → Fin n → ℝ) : 0 ≤ bernoulliSup u := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; rw [bernoulliSup_of_isEmpty]
  · haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    exact bernoulliSup_nonneg u

/- @[blueprint "lem:min-normalise"
  (statement := /-- \textbf{Normalisation of the minimum.} For $n \ge 1$, $\rho > 0$, $R \ne 0$
    and $\ell \ge 0$, with $a := \rho\sqrt n$,
    $$ \frac1n \min\Bigl(a\sqrt{\ell},\ \frac{a^2}{R}\Bigr)
       = \min\Bigl(\rho\sqrt{\ell/n},\ \frac{\rho^2}{R}\Bigr). $$ -/)] -/
theorem inv_mul_min_sqrt_eq {ρ R ℓ : ℝ} (hn : 0 < n) (hℓ : 0 ≤ ℓ) :
    (n : ℝ)⁻¹ * min (ρ * √n * √ℓ) ((ρ * √n) ^ 2 / R) = min (ρ * √(ℓ / n)) (ρ ^ 2 / R) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  rw [← div_eq_inv_mul, ← min_div_div_right hn'.le]
  congr 1
  · rw [Real.sqrt_div hℓ]
    field_simp
    rw [Real.sq_sqrt hn'.le]
    ring
  · rw [mul_pow, Real.sq_sqrt hn'.le]
    field_simp

/- @[blueprint "thm:bernoulli-sudakov"
  (statement := /-- \textbf{Sudakov minoration for Bernoulli processes} (Talagrand). There is a
    universal constant $c > 0$ such that the following holds. Let $n \ge 1$, $M \ge 0$, and let
    $u_1, \dots, u_M \in \mathbb R^n$ satisfy, for constants $\rho, R > 0$,
    $$\|u_j - u_l\|_S := \Bigl(\frac1n \sum_{i=1}^n |u_{j,i} - u_{l,i}|^2\Bigr)^{1/2} \ge \rho
    \quad (j \ne l), \qquad |u_{j,i}| \le R \quad (\text{all } j, i).$$
    Then
    $$\mathbb E_\sigma \max_{j \le M} \frac1n \sum_{i=1}^n \sigma_i u_{j,i}
    = 2^{-n} \sum_{\sigma \in \{\pm1\}^n} \max_{j \le M} \frac1n \sum_{i=1}^n \sigma_i u_{j,i}
    \ge c \min\Bigl\{\rho \sqrt{\frac{\log M}{n}},\ \frac{\rho^2}{R}\Bigr\}.$$
    (In Lean the maximum is `⨆ j : Fin M`, which is $0$ for $M = 0$; the bound is trivially true
    for $M \le 1$ since $\log M \le 0$.) This is the Bernoulli-process analogue of the Gaussian
    Sudakov minoration; see M. Talagrand, \emph{Regularity of infinitely divisible processes},
    Ann. Probab. 21 (1993), and \emph{Upper and Lower Bounds for Stochastic Processes}
    (Springer 2014), Thm.~6.4.1; Ledoux--Talagrand, \emph{Probability in Banach Spaces}, Ch.~4.
    The proof is fully formalised, with the explicit constant $c = 1/L_0 = 1/(8L_2)
    \approx 9.6\cdot10^{-6}$: after unnormalising ($a = \rho\sqrt n$, $b = R$, so that
    $\|u_j - u_l\|_2 \ge a$) it is the multiscale minoration \texttt{lem:bernoulli-multiscale},
    whose ingredients are the Gaussian Sudakov minoration \texttt{thm:gaussian-sudakov} (via the
    Sudakov--Fernique comparison), Talagrand's truncation/contraction comparison of Bernoulli with
    Gaussian averages under an $\ell^\infty$ bound (\texttt{lem:bernoulli-critical}), subset
    selection (\texttt{lem:bernoulli-subset-selection}) and the multiscale counting lemma
    (\texttt{lem:separated-net-counting}). The case $M = 2$ with the better constant
    $1/(2\sqrt3)$ is \texttt{lem:bernoulli-sudakov-two}. -/)] -/
theorem bernoulli_sudakov :
    ∃ c : ℝ, 0 < c ∧ ∀ (n M : ℕ) (u : Fin M → Fin n → ℝ) (ρ R : ℝ), 0 < n → 0 < ρ → 0 < R →
      (∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2)) →
      (∀ j i, |u j i| ≤ R) →
      c * min (ρ * Real.sqrt (Real.log M / n)) (ρ ^ 2 / R) ≤
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i := by
  have hL0 := L₀_pos
  refine ⟨1 / L₀, by positivity, fun n M u ρ R hn hρ hR hsep hub => ?_⟩
  rw [← inv_mul_bernoulliSup]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hBnn : 0 ≤ bernoulliSup u := bernoulliSup_nonneg' u
  rcases lt_or_ge M 2 with hM | hM
  · -- `M ≤ 1`: the right-hand side is `0`
    have hlog : Real.log M ≤ 0 :=
      Real.log_nonpos (Nat.cast_nonneg M) (by exact_mod_cast Nat.lt_succ_iff.mp hM)
    have hsqrt : √(Real.log M / n) = 0 :=
      Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonpos_of_nonneg hlog hn'.le)
    rw [hsqrt, mul_zero, min_eq_left (by positivity), mul_zero]
    positivity
  -- `M ≥ 2`: unnormalise and apply the multiscale minoration
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn'
  set a : ℝ := ρ * √n with ha
  have ha0 : 0 < a := by positivity
  have hsep' : ∀ j l, j ≠ l → a ^ 2 ≤ ∑ i, (u j i - u l i) ^ 2 := fun j l hjl => by
    have h := hsep j l hjl
    have hsum : 0 ≤ (1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2 := by positivity
    have h2 : ρ ^ 2 ≤ (1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2 :=
      (Real.le_sqrt hρ.le hsum).mp h
    simp only [sq_abs] at h2
    rw [ha, mul_pow, Real.sq_sqrt hn'.le]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hn'] at h2
    linarith
  have hB11 := bernoulli_multiscale hM u ha0 hR hub hsep'
  have hlogM : 0 ≤ Real.log M :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  calc 1 / L₀ * min (ρ * √(Real.log M / n)) (ρ ^ 2 / R)
      = 1 / L₀ * ((n : ℝ)⁻¹ * min (ρ * √n * √(Real.log M)) ((ρ * √n) ^ 2 / R)) := by
        rw [inv_mul_min_sqrt_eq hn hlogM]
    _ = (n : ℝ)⁻¹ * (min (a * √(Real.log M)) (a ^ 2 / R) / L₀) := by
        rw [ha]; ring
    _ ≤ (n : ℝ)⁻¹ * bernoulliSup u := by gcongr

end FoML.ToFoML
