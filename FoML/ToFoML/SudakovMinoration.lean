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
import FoML.ToFoML.VectorHoeffding

/-!
# Sudakov minoration for Bernoulli (Rademacher) processes on `Signs n`

FoML realises the uniform distribution on the Rademacher signs `σ : Signs n = Fin n → {-1, 1}`
as the counting average over the `2^n` sign patterns. For a finite family of vectors
`u : Fin M → (Fin n → ℝ)` (a finite function class evaluated on the sample) the quantity

`𝔼_σ max_j (1/n) ∑ᵢ σᵢ u j i = (1/2^n) ∑_σ ⨆ j, (1/n) ∑ᵢ σᵢ u j i`

is FoML's `empiricalRademacherComplexity_without_abs n u id` (sample `id : Fin n → Fin n`).

The **Bernoulli–Sudakov minoration** (Talagrand) states: if the `u j` are pairwise
`ρ`-separated in the normalised Euclidean metric `‖u j − u l‖_S = √((1/n) ∑ᵢ |u j i − u l i|²)`
and uniformly bounded, `|u j i| ≤ R`, then

`𝔼_σ max_j (1/n) ∑ᵢ σᵢ u j i ≥ c · min{ρ √(log M / n), ρ² / R}`

for a universal constant `c > 0` (`thm:bernoulli-sudakov`). It is proved, with an explicit
constant, in `FoML.ToFoML.BernoulliSudakov` (through the Gaussian Sudakov minoration
`FoML.ToMathlib.GaussianSudakov` and Talagrand's comparison of Bernoulli with Gaussian
averages under an `ℓ^∞` bound, `FoML.ToFoML.BernoulliSudakov*`); it is the key ingredient
of the conditional Sudakov-type lower bound `thm:sudakov-type` (`LeanDeepgen.Bounds.Sudakov` in lean-deepgen).
This file contains the elementary Bernoulli-side facts on which that development is built.

What *is* proved here, elementarily:

* the exact second moment `∑_σ (∑ᵢ σᵢ aᵢ)² = 2^n ∑ᵢ aᵢ²` and the fourth-moment bound
  `∑_σ (∑ᵢ σᵢ aᵢ)⁴ ≤ 3 · 2^n (∑ᵢ aᵢ²)²` (induction on `n`);
* the **Khintchine lower bound** `𝔼_σ |∑ᵢ σᵢ aᵢ| ≥ (∑ᵢ aᵢ²)^{1/2} / √3`
  (`lem:khintchine-lower`), via `𝔼|X| ≥ (𝔼X²)^{3/2} / (𝔼X⁴)^{1/2}` (Cauchy–Schwarz twice);
* nonnegativity of the (one-sided) Rademacher average of a nonempty family whose sums are bounded
  above for each sign pattern (`lem:rademacher-avg-sup-nonneg`), by the symmetry `σ ↦ -σ`;
* the identification of the left-hand side of `thm:bernoulli-sudakov` with FoML's one-sided
  empirical Rademacher complexity (`lem:bernoulli-sudakov-foml`);
* the case `M = 2` of the minoration with the explicit constant `c = 1/(2√3)`
  (`lem:bernoulli-sudakov-two`), from the Khintchine lower bound.

This file depends only on Mathlib and FoML, and on `FoML.ToFoML.VectorHoeffding` for the
cardinality `|{±1}^n| = 2^n` (`card_signs`).

References: M. Talagrand, *Regularity of infinitely divisible processes*, Ann. Probab. 21
(1993), 362–432 (Sudakov minoration for Bernoulli processes); M. Talagrand, *Upper and Lower
Bounds for Stochastic Processes* (Springer, 2014), Ch. 5 (Bernoulli processes); M. Ledoux and
M. Talagrand, *Probability in Banach Spaces* (Springer, 1991), Ch. 4 (Rademacher averages).
-/

open Real
open scoped BigOperators

namespace FoML.ToFoML

variable {n : ℕ}

/-! ### The sign space -/

/- @[blueprint "lem:sum-pm"
  (statement := /-- For $g : \mathbb Z \to \mathbb R$,
    $\sum_{s \in \{-1,1\}} g(s) = g(-1) + g(1)$. -/)] -/
theorem sum_pm (g : ℤ → ℝ) : ∑ s : ({-1, 1} : Finset ℤ), g s = g (-1) + g 1 := by
  rw [Finset.sum_coe_sort ({-1, 1} : Finset ℤ) g, Finset.sum_pair (by decide)]

/- @[blueprint "lem:sum-signs-succ"
  (statement := /-- Splitting off the first coordinate: for $F : \{\pm1\}^{n+1} \to \mathbb R$,
    $\sum_{\sigma \in \{\pm1\}^{n+1}} F(\sigma) = \sum_{s \in \{\pm1\}} \sum_{\tau \in \{\pm1\}^n}
    F(s, \tau)$. -/)] -/
theorem sum_signs_succ (F : Signs (n + 1) → ℝ) :
    ∑ σ : Signs (n + 1), F σ =
      ∑ s : ({-1, 1} : Finset ℤ), ∑ τ : Signs n,
        F (Fin.cons (α := fun _ => ({-1, 1} : Finset ℤ)) s τ) := by
  change ∑ σ : Fin (n + 1) → ({-1, 1} : Finset ℤ), F σ =
    ∑ s : ({-1, 1} : Finset ℤ), ∑ τ : Fin n → ({-1, 1} : Finset ℤ),
      F (Fin.cons (α := fun _ => ({-1, 1} : Finset ℤ)) s τ)
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => ({-1, 1} : Finset ℤ))
    (fun p => F (Fin.cons p.1 p.2)) F (fun p => rfl), Fintype.sum_prod_type]

/-! ### Second and fourth moments of a Rademacher sum -/

/- @[blueprint "lem:rademacher-sum-cons"
  (statement := /-- $\sum_{i \le n} \sigma_i a_i = s a_0 + \sum_{i < n} \tau_i a_{i+1}$ for
    $\sigma = (s, \tau)$. -/)] -/
theorem rademacher_sum_cons (a : Fin (n + 1) → ℝ) (s : ({-1, 1} : Finset ℤ)) (τ : Signs n) :
    ∑ i : Fin (n + 1), ((Fin.cons (α := fun _ => ({-1, 1} : Finset ℤ)) s τ : Signs (n + 1)) i : ℝ)
        * a i =
      (s : ℝ) * a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/- @[blueprint "lem:sum-signs-succ-apply"
  (statement := /-- For $a \in \mathbb R^{n+1}$ and $\varphi : \mathbb R \to \mathbb R$,
    $\sum_{\sigma \in \{\pm1\}^{n+1}} \varphi\bigl(\sum_i \sigma_i a_i\bigr)
    = \sum_{\tau \in \{\pm1\}^n} \bigl[\varphi(-a_0 + Y_\tau) + \varphi(a_0 + Y_\tau)\bigr]$
    with $Y_\tau = \sum_{i < n} \tau_i a_{i+1}$. -/)] -/
theorem sum_signs_succ_apply (a : Fin (n + 1) → ℝ) (φ : ℝ → ℝ) :
    ∑ σ : Signs (n + 1), φ (∑ i : Fin (n + 1), (σ i : ℝ) * a i) =
      ∑ τ : Signs n, (φ (-a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ) +
        φ (a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ)) := by
  rw [sum_signs_succ]
  simp_rw [rademacher_sum_cons]
  rw [sum_pm (fun z : ℤ => ∑ τ : Signs n, φ ((z : ℝ) * a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ)),
    ← Finset.sum_add_distrib]
  push_cast
  simp only [neg_one_mul, one_mul]

/- @[blueprint "lem:sum-signs-sq"
  (statement := /-- \textbf{Second moment of a Rademacher sum.} For $a \in \mathbb R^n$,
    $\sum_{\sigma \in \{\pm1\}^n} \bigl(\sum_i \sigma_i a_i\bigr)^2 = 2^n \sum_i a_i^2$. -/)] -/
theorem sum_signs_sq (a : Fin n → ℝ) :
    ∑ σ : Signs n, (∑ i : Fin n, (σ i : ℝ) * a i) ^ 2 = 2 ^ n * ∑ i, a i ^ 2 := by
  /- Induction on $n$: $(-a_0 + Y)^2 + (a_0 + Y)^2 = 2 a_0^2 + 2 Y^2$. -/
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_signs_succ_apply a (fun x => x ^ 2), Fin.sum_univ_succ]
    have h : ∀ τ : Signs n, (-a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 2 +
        (a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 2 =
        2 * a 0 ^ 2 + 2 * (∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 2 := fun τ => by ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_signs,
      ← Finset.mul_sum, ih (fun i => a i.succ)]
    simp only [nsmul_eq_mul]
    push_cast
    ring

/- @[blueprint "lem:sum-signs-pow-four-le"
  (statement := /-- \textbf{Fourth moment of a Rademacher sum.} For $a \in \mathbb R^n$,
    $\sum_{\sigma \in \{\pm1\}^n} \bigl(\sum_i \sigma_i a_i\bigr)^4
    \le 3 \cdot 2^n \bigl(\sum_i a_i^2\bigr)^2$. -/)] -/
theorem sum_signs_pow_four_le (a : Fin n → ℝ) :
    ∑ σ : Signs n, (∑ i : Fin n, (σ i : ℝ) * a i) ^ 4 ≤ 3 * 2 ^ n * (∑ i, a i ^ 2) ^ 2 := by
  /- Induction on $n$: $(-a_0 + Y)^4 + (a_0 + Y)^4 = 2(a_0^4 + 6 a_0^2 Y^2 + Y^4)$, and
    $a_0^4 + 6 a_0^2 V + 3 V^2 \le 3 (a_0^2 + V)^2$. -/
  induction n with
  | zero => simp
  | succ n ih =>
    have hsq := sum_signs_sq (fun i : Fin n => a i.succ)
    have ih' := ih (fun i => a i.succ)
    rw [sum_signs_succ_apply a (fun x => x ^ 4), Fin.sum_univ_succ]
    have h : ∀ τ : Signs n, (-a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 4 +
        (a 0 + ∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 4 =
        2 * a 0 ^ 4 + 12 * a 0 ^ 2 * (∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 2 +
          2 * (∑ i : Fin n, (τ i : ℝ) * a i.succ) ^ 4 := fun τ => by ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      card_signs, ← Finset.mul_sum, ← Finset.mul_sum, hsq]
    simp only [nsmul_eq_mul]
    push_cast
    have hV : 0 ≤ ∑ i : Fin n, a i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [pow_succ (2 : ℝ) n]
    nlinarith [ih', mul_nonneg h2.le (sq_nonneg (a 0 ^ 2)), mul_nonneg h2.le (sq_nonneg (a 0)),
      mul_nonneg h2.le hV, mul_nonneg (mul_nonneg h2.le (sq_nonneg (a 0))) hV]

/-! ### The Khintchine lower bound -/

/- @[blueprint "lem:sq-sum-sq-le"
  (statement := /-- (Cauchy–Schwarz.) For $X : \Omega \to \mathbb R$ on a finite set $\Omega$,
    $\bigl(\sum_\omega X_\omega^2\bigr)^2 \le \bigl(\sum_\omega |X_\omega|\bigr)
    \bigl(\sum_\omega |X_\omega| X_\omega^2\bigr)$. -/)] -/
theorem sq_sum_sq_le_sum_abs_mul_sum_abs_mul_sq {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) :
    (∑ ω, X ω ^ 2) ^ 2 ≤ (∑ ω, |X ω|) * ∑ ω, |X ω| * X ω ^ 2 := by
  /- Write $X^2 = \sqrt{|X|} \cdot \sqrt{|X|}\,|X|$ and apply Cauchy–Schwarz. -/
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ω => Real.sqrt |X ω|)
    (fun ω => Real.sqrt |X ω| * |X ω|)
  have h1 : ∀ ω, Real.sqrt |X ω| * (Real.sqrt |X ω| * |X ω|) = X ω ^ 2 := fun ω => by
    rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _), ← sq, sq_abs]
  have h2 : ∀ ω, Real.sqrt |X ω| ^ 2 = |X ω| := fun ω => Real.sq_sqrt (abs_nonneg _)
  have h3 : ∀ ω, (Real.sqrt |X ω| * |X ω|) ^ 2 = |X ω| * X ω ^ 2 := fun ω => by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
  simpa only [h1, h2, h3] using h

/- @[blueprint "lem:sq-sum-abs-mul-sq-le"
  (statement := /-- (Cauchy–Schwarz.) $\bigl(\sum_\omega |X_\omega| X_\omega^2\bigr)^2
    \le \bigl(\sum_\omega X_\omega^2\bigr)\bigl(\sum_\omega X_\omega^4\bigr)$. -/)] -/
theorem sq_sum_abs_mul_sq_le_sum_sq_mul_sum_pow_four {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) :
    (∑ ω, |X ω| * X ω ^ 2) ^ 2 ≤ (∑ ω, X ω ^ 2) * ∑ ω, X ω ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ω => |X ω|) (fun ω => X ω ^ 2)
  have h2 : ∀ ω, (X ω ^ 2) ^ 2 = X ω ^ 4 := fun ω => by ring
  simpa only [sq_abs, h2] using h

/- @[blueprint "lem:abs-moment-lower"
  (statement := /-- \textbf{Moment comparison.} If $A, B, C, D \ge 0$ satisfy $B^2 \le A D$,
    $D^2 \le B C$, $B = N V$ and $C \le 3 N V^2$ with $N > 0$, $V \ge 0$, then
    $N^2 V \le 3 A^2$ (i.e. $\mathbb E|X| \ge \sqrt{V/3}$ when $A = \sum|X|$, $B = \sum X^2$,
    $D = \sum |X|^3$, $C = \sum X^4$ over $N$ atoms). -/)] -/
theorem sq_mul_le_three_mul_sq_of_moments {A B C D N V : ℝ} (hN : 0 < N)
    (hV : 0 ≤ V) (h1 : B ^ 2 ≤ A * D) (h2 : D ^ 2 ≤ B * C) (hB : B = N * V)
    (hC : C ≤ 3 * N * V ^ 2) : N ^ 2 * V ≤ 3 * A ^ 2 := by
  rcases hV.eq_or_lt with hV0 | hVpos
  · rw [← hV0]; simp only [mul_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hB4 : B ^ 4 ≤ A ^ 2 * D ^ 2 := by
    calc B ^ 4 = (B ^ 2) ^ 2 := by ring
      _ ≤ (A * D) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      _ = A ^ 2 * D ^ 2 := by ring
  have hD2 : A ^ 2 * D ^ 2 ≤ A ^ 2 * (B * C) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hBC : A ^ 2 * (B * C) ≤ A ^ 2 * (B * (3 * N * V ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hB0) (sq_nonneg _)
  have key : (N * V) ^ 4 ≤ 3 * A ^ 2 * (N ^ 2 * V ^ 3) := by
    calc (N * V) ^ 4 = B ^ 4 := by rw [hB]
      _ ≤ A ^ 2 * (B * (3 * N * V ^ 2)) := hB4.trans (hD2.trans hBC)
      _ = 3 * A ^ 2 * (N ^ 2 * V ^ 3) := by rw [hB]; ring
  have hpos : 0 < N ^ 2 * V ^ 3 := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  calc N ^ 2 * V * (N ^ 2 * V ^ 3) = (N * V) ^ 4 := by ring
    _ ≤ 3 * A ^ 2 * (N ^ 2 * V ^ 3) := key

/- @[blueprint "lem:khintchine-lower"
  (statement := /-- \textbf{Khintchine lower bound.} For $a \in \mathbb R^n$,
    $$\mathbb E_\sigma \Bigl|\sum_i \sigma_i a_i\Bigr|
    = 2^{-n} \sum_{\sigma \in \{\pm1\}^n} \Bigl|\sum_i \sigma_i a_i\Bigr|
    \ge \frac{1}{\sqrt3} \Bigl(\sum_i a_i^2\Bigr)^{1/2}.$$
    (Proof: $\mathbb E|X| \ge (\mathbb E X^2)^{3/2} / (\mathbb E X^4)^{1/2}$ by Cauchy–Schwarz,
    with $\mathbb E X^2 = \sum a_i^2$ and $\mathbb E X^4 \le 3 (\sum a_i^2)^2$. The optimal
    constant $1/\sqrt2$ (Szarek) is not needed.) -/)] -/
theorem khintchine_lower (a : Fin n → ℝ) :
    Real.sqrt (∑ i, a i ^ 2) / Real.sqrt 3 ≤
      (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * a i| := by
  have hN : (Fintype.card (Signs n) : ℝ) = 2 ^ n := by rw [card_signs]; push_cast; rfl
  have hNpos : (0 : ℝ) < 2 ^ n := by positivity
  have hV : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key := sq_mul_le_three_mul_sq_of_moments hNpos hV
    (sq_sum_sq_le_sum_abs_mul_sum_abs_mul_sq fun σ : Signs n => ∑ i : Fin n, (σ i : ℝ) * a i)
    (sq_sum_abs_mul_sq_le_sum_sq_mul_sum_pow_four fun σ : Signs n => ∑ i : Fin n, (σ i : ℝ) * a i)
    (sum_signs_sq a) (sum_signs_pow_four_le a)
  rw [hN, ← Real.sqrt_div hV, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3), mul_pow, inv_pow]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ n) ^ 2 := by positivity
  calc ∑ i, a i ^ 2 = (((2 : ℝ) ^ n) ^ 2)⁻¹ * (((2 : ℝ) ^ n) ^ 2 * ∑ i, a i ^ 2) := by
        field_simp
    _ ≤ (((2 : ℝ) ^ n) ^ 2)⁻¹ * (3 * (∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * a i|) ^ 2) := by
        gcongr
    _ = (((2 : ℝ) ^ n) ^ 2)⁻¹ * (∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * a i|) ^ 2 * 3 := by
        ring

/-! ### Nonnegativity of the one-sided Rademacher average -/

/- @[blueprint "def:neg-signs"
  (statement := /-- The sign flip $\sigma \mapsto -\sigma$ on $\{\pm1\}^n$. -/)] -/
def negSigns (σ : Signs n) : Signs n := fun i => -(σ i)

/- @[blueprint "lem:coe-neg-sign"
  (statement := /-- $(-s)$ as an integer is $-s$. -/)] -/
theorem coe_neg_sign (s : ({-1, 1} : Finset ℤ)) : ((-s : ({-1, 1} : Finset ℤ)) : ℤ) = -(s : ℤ) :=
  rfl

/- @[blueprint "lem:neg-signs-involutive"
  (statement := /-- $\sigma \mapsto -\sigma$ is an involution of $\{\pm1\}^n$. -/)] -/
theorem negSigns_involutive : Function.Involutive (negSigns (n := n)) := by
  intro σ
  funext i
  apply Subtype.ext
  change -(-((σ i : ℤ))) = (σ i : ℤ)
  exact neg_neg _

/- @[blueprint "lem:rademacher-avg-sup-nonneg"
  (statement := /-- \textbf{Nonnegativity of the one-sided Rademacher average.} Let
    $(u_j)_{j \in J}$ be a nonempty family of vectors in $\mathbb R^n$ such that for every
    $\sigma$ the family $\{\frac1n\sum_i \sigma_i u_{j,i}\}_j$ is bounded above. Then
    $2^{-n}\sum_\sigma \sup_j \frac1n \sum_i \sigma_i u_{j,i} \ge 0$. (Pair $\sigma$ with
    $-\sigma$: $\sup_j Z_j(\sigma) + \sup_j Z_j(-\sigma) \ge Z_{j_0}(\sigma) + Z_{j_0}(-\sigma)
    = 0$.) -/)] -/
theorem rademacherAvgSup_nonneg {ι : Type*} [Nonempty ι] (u : ι → Fin n → ℝ)
    (hbdd : ∀ σ : Signs n,
      BddAbove (Set.range fun j => (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i)) :
    0 ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i := by
  refine mul_nonneg (by positivity) ?_
  set G : Signs n → ℝ := fun σ => ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i with hG
  have hflip : ∑ σ, G σ = ∑ σ, G (negSigns σ) :=
    (Fintype.sum_equiv negSigns_involutive.toPerm (fun σ => G (negSigns σ)) G
      (fun σ => rfl)).symm
  have hpair : ∀ σ, 0 ≤ G σ + G (negSigns σ) := by
    intro σ
    obtain ⟨j₀⟩ := ‹Nonempty ι›
    have h1 : (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j₀ i ≤ G σ := le_ciSup (hbdd σ) j₀
    have h2 : (n : ℝ)⁻¹ * ∑ i : Fin n, (negSigns σ i : ℝ) * u j₀ i ≤ G (negSigns σ) :=
      le_ciSup (hbdd _) j₀
    have h3 : (n : ℝ)⁻¹ * ∑ i : Fin n, (negSigns σ i : ℝ) * u j₀ i =
        -((n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j₀ i) := by
      simp only [negSigns, coe_neg_sign, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
    linarith
  have h2 : 0 ≤ 2 * ∑ σ, G σ := by
    calc (0 : ℝ) ≤ ∑ σ, (G σ + G (negSigns σ)) := Finset.sum_nonneg fun σ _ => hpair σ
      _ = ∑ σ, G σ + ∑ σ, G (negSigns σ) := Finset.sum_add_distrib
      _ = 2 * ∑ σ, G σ := by rw [← hflip]; ring
  linarith

/-! ### The Bernoulli–Sudakov minoration: FoML form of the left-hand side -/

/- @[blueprint "lem:bernoulli-sudakov-foml"
  (statement := /-- The left-hand side of \texttt{thm:bernoulli-sudakov} is FoML's one-sided
    empirical Rademacher complexity of the class $\{u_j\}_j$ (functions on $\{1,\dots,n\}$) for
    the sample $(1, \dots, n)$. -/)] -/
theorem rademacherAvgSup_eq_empiricalRademacherComplexity_without_abs {M : ℕ}
    (u : Fin M → Fin n → ℝ) :
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i =
      empiricalRademacherComplexity_without_abs n u id :=
  rfl

/-! ### The case `M = 2` -/

/- @[blueprint "lem:isup-fin-two"
  (statement := /-- $\sup_{j \in \{0,1\}} f(j) = \max\{f(0), f(1)\}$. -/)] -/
theorem iSup_fin_two (f : Fin 2 → ℝ) : (⨆ j, f j) = max (f 0) (f 1) := by
  apply le_antisymm
  · exact ciSup_le fun j => by fin_cases j <;> simp
  · exact max_le (le_ciSup (Set.finite_range f).bddAbove 0)
      (le_ciSup (Set.finite_range f).bddAbove 1)

/- @[blueprint "lem:max-eq-half-add-abs"
  (statement := /-- $\max\{x,y\} = \frac{(x+y) + |x-y|}{2}$. -/)] -/
theorem max_eq_half_add_add_abs_sub (x y : ℝ) : max x y = ((x + y) + |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring

/- @[blueprint "lem:sum-signs-rademacher-sum-zero"
  (statement := /-- $\sum_{\sigma} \sum_i \sigma_i a_i = 0$. -/)] -/
theorem sum_signs_rademacher_sum (a : Fin n → ℝ) :
    ∑ σ : Signs n, ∑ i : Fin n, (σ i : ℝ) * a i = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_mul, sign_sum_eq_zero, zero_mul]

/- @[blueprint "lem:bernoulli-sudakov-two"
  (statement := /-- \textbf{The case $M = 2$ of the Bernoulli–Sudakov minoration}, with the
    explicit constant $c = 1/(2\sqrt3)$ (and no boundedness assumption, any $R$): if
    $\|u_0 - u_1\|_S \ge \rho > 0$ then
    $\mathbb E_\sigma \max_{j \in \{0,1\}} \frac1n \sum_i \sigma_i u_{j,i}
    \ge \frac{1}{2\sqrt3} \min\{\rho\sqrt{\log 2 / n},\ \rho^2/R\}$.
    Proof: $\max\{Z_0, Z_1\} = \frac{Z_0 + Z_1}2 + \frac{|Z_0 - Z_1|}2$, the first term has
    mean $0$, and the second is bounded below by the Khintchine lower bound
    $\frac1{2n}\cdot\frac{1}{\sqrt3}\bigl(\sum_i (u_{0,i} - u_{1,i})^2\bigr)^{1/2}
    \ge \frac{\rho}{2\sqrt{3n}}$; finally $\log 2 \le 1$. -/)] -/
theorem bernoulli_sudakov_two (u : Fin 2 → Fin n → ℝ) (ρ R : ℝ) (hn : 0 < n) (hρ : 0 < ρ)
    (hsep : ∀ j l, j ≠ l → ρ ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u j i - u l i| ^ 2)) :
    (1 / (2 * Real.sqrt 3)) * min (ρ * Real.sqrt (Real.log 2 / n)) (ρ ^ 2 / R) ≤
      (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set d : Fin n → ℝ := fun i => u 0 i - u 1 i with hd
  -- the right-hand side equals `(1/2) N⁻¹ n⁻¹ ∑_σ |∑_i σ_i d_i|`
  have hRHS : (Fintype.card (Signs n) : ℝ)⁻¹ *
      ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i =
      (Fintype.card (Signs n) : ℝ)⁻¹ * ((n : ℝ)⁻¹ *
        ∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * d i|) / 2 := by
    have hσ : ∀ σ : Signs n, (⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i) =
        ((n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u 0 i +
          (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u 1 i +
          (n : ℝ)⁻¹ * |∑ i : Fin n, (σ i : ℝ) * d i|) / 2 := by
      intro σ
      rw [iSup_fin_two, max_eq_half_add_add_abs_sub]
      have h1 : (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u 0 i -
          (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u 1 i =
          (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * d i := by
        simp only [hd, mul_sub, Finset.sum_sub_distrib]
      rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hn')]
    rw [Finset.sum_congr rfl fun σ _ => hσ σ, ← Finset.sum_div, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_signs_rademacher_sum, sum_signs_rademacher_sum]
    ring
  rw [hRHS]
  -- Khintchine: `N⁻¹ ∑_σ |∑ σ_i d_i| ≥ √(∑ d_i²)/√3 ≥ ρ √n / √3`
  have hK := khintchine_lower d
  have hsep01 := hsep 0 1 (by decide)
  have hsum : ρ * Real.sqrt n ≤ Real.sqrt (∑ i, d i ^ 2) := by
    have : Real.sqrt ((1 / (n : ℝ)) * ∑ i, |u 0 i - u 1 i| ^ 2) =
        Real.sqrt (∑ i, d i ^ 2) / Real.sqrt n := by
      rw [Real.sqrt_mul (by positivity), one_div, Real.sqrt_inv, inv_mul_eq_div]
      simp only [hd, sq_abs]
    rw [this, le_div_iff₀ (Real.sqrt_pos.mpr hn')] at hsep01
    exact hsep01
  have hlog : Real.sqrt (Real.log 2 / n) ≤ Real.sqrt (1 / n) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by linarith [Real.log_le_sub_one_of_pos two_pos]) hn'.le
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  calc (1 / (2 * Real.sqrt 3)) * min (ρ * Real.sqrt (Real.log 2 / n)) (ρ ^ 2 / R)
      ≤ (1 / (2 * Real.sqrt 3)) * (ρ * Real.sqrt (1 / n)) := by
        refine mul_le_mul_of_nonneg_left ((min_le_left _ _).trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hlog hρ.le
    _ = (n : ℝ)⁻¹ * (ρ * Real.sqrt n / Real.sqrt 3) / 2 := by
        have h : (n : ℝ)⁻¹ * Real.sqrt n = (Real.sqrt n)⁻¹ := by
          nth_rewrite 1 [← Real.mul_self_sqrt hn'.le]
          rw [mul_inv, mul_assoc, inv_mul_cancel₀ hsqrtn.ne', mul_one]
        rw [Real.sqrt_div' 1 hn'.le, Real.sqrt_one,
          show (n : ℝ)⁻¹ * (ρ * Real.sqrt n / Real.sqrt 3) / 2 =
            ρ * ((n : ℝ)⁻¹ * Real.sqrt n) / Real.sqrt 3 / 2 by ring, h]
        field_simp
    _ ≤ (n : ℝ)⁻¹ * (Real.sqrt (∑ i, d i ^ 2) / Real.sqrt 3) / 2 := by gcongr
    _ ≤ (n : ℝ)⁻¹ * ((Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * d i|) / 2 := by gcongr
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ * ((n : ℝ)⁻¹ *
          ∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * d i|) / 2 := by ring

end FoML.ToFoML
