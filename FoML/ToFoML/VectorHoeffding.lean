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
import FoML.ToMathlib.CoshInequalities

/-!
# Hoeffding's inequality for Rademacher sums on `Signs n`

FoML's Rademacher signs are `σ : Signs n = Fin n → {-1, 1}` with the uniform distribution
realised as the counting average over the `2^n` sign patterns; a probability
`ℙ_σ(p σ)` is therefore `#{σ | p σ} / 2^n`. This file proves, in this elementary
finite-probability form, the real-valued Hoeffding inequality for Rademacher sums

`ℙ_σ(|∑ᵢ σᵢ aᵢ| > t) ≤ 2 exp(-t² / (2 ∑ᵢ aᵢ²))`

by the classical Chernoff argument: `𝔼 exp(λ ∑ σᵢ aᵢ) = ∏ cosh(λ aᵢ) ≤ exp(λ² ∑ aᵢ² / 2)`,
Markov's inequality and the choice `λ = t / ∑ aᵢ²`.

The *vector-valued* analogue for a real Hilbert space `E`,

`ℙ_σ(‖∑ᵢ σᵢ vᵢ‖ > t) ≤ 2 exp(-t² / (2 ∑ᵢ ‖vᵢ‖²))`

(Pinelis' inequality for Rademacher sums in `(2,1)`-smooth spaces; Kahane–Khintchine-type
concentration), is not in Mathlib or FoML and is proved here as `rademacher_hilbert_tail` with
the sharp constant `2` in the exponent. The proof replaces `exp(λ ∑ σᵢ aᵢ)` by
`cosh(λ ‖∑ σᵢ vᵢ‖)`: the elementary Hilbert-space inequality
`cosh(λ‖x+v‖) + cosh(λ‖x−v‖) ≤ 2 cosh(λ‖x‖) cosh(λ‖v‖)` (`cosh_norm_add_add_cosh_norm_sub_le`
in `FoML.ToMathlib.CoshInequalities`, from the parallelogram identity, Cauchy–Schwarz and
convexity of `u ↦ cosh √u`) gives by
induction `∑_σ cosh(λ‖∑ σᵢ vᵢ‖) ≤ 2^n ∏ cosh(λ‖vᵢ‖) ≤ 2^n exp(λ² ∑ ‖vᵢ‖² / 2)`, and a
`cosh`-Chernoff bound with `λ = t / ∑ ‖vᵢ‖²` finishes. The one-dimensional specialisation is
`rademacher_hilbert_tail_real`. This file depends only on Mathlib, FoML and
`FoML.ToMathlib`.
-/

open Real
open scoped BigOperators

open FoML.ToMathlib

namespace FoML.ToFoML

variable {n : ℕ}

/- @[blueprint "lem:sum-signs-prod"
  (statement := /-- For functions $g_i : \{\pm1\} \to \mathbb R$,
    $\sum_{\sigma \in \{\pm1\}^n} \prod_i g_i(\sigma_i) = \prod_i (g_i(-1) + g_i(1))$. -/)] -/
theorem sum_signs_prod (g : Fin n → ℤ → ℝ) :
    ∑ σ : Signs n, ∏ i, g i (σ i) = ∏ i, (g i (-1) + g i 1) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ({-1, 1} : Finset ℤ)))
    (fun i (s : ({-1, 1} : Finset ℤ)) => g i s)
  rw [Fintype.piFinset_univ] at h
  rw [show (∑ σ : Signs n, ∏ i, g i (σ i)) =
      ∑ σ : Fin n → ({-1, 1} : Finset ℤ), ∏ i, g i (σ i) from rfl, ← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_coe_sort ({-1, 1} : Finset ℤ) (g i), Finset.sum_pair (by decide)]

/- @[blueprint "lem:card-signs"
  (statement := /-- $|\{\pm1\}^n| = 2^n$. -/)] -/
theorem card_signs : Fintype.card (Signs n) = 2 ^ n := by
  rw [show Fintype.card (Signs n) = Fintype.card (Fin n → ({-1, 1} : Finset ℤ)) from rfl,
    Fintype.card_pi]
  simp

/- @[blueprint "lem:signs-mgf-le"
  (statement := /-- \textbf{Moment generating function of a Rademacher sum.} For $a \in \mathbb R^n$
    and $\lambda \in \mathbb R$,
    $\sum_{\sigma} \exp\bigl(\lambda \sum_i \sigma_i a_i\bigr)
    = 2^n \prod_i \cosh(\lambda a_i) \le 2^n \exp\bigl(\lambda^2 \sum_i a_i^2 / 2\bigr)$
    (using $\cosh x \le e^{x^2/2}$). -/)] -/
theorem sum_signs_exp_le (a : Fin n → ℝ) (l : ℝ) :
    ∑ σ : Signs n, Real.exp (l * ∑ i, (σ i : ℝ) * a i) ≤
      Fintype.card (Signs n) * Real.exp (l ^ 2 * (∑ i, a i ^ 2) / 2) := by
  have h1 : ∀ σ : Signs n, Real.exp (l * ∑ i, (σ i : ℝ) * a i) =
      ∏ i, Real.exp (l * ((σ i : ℤ) : ℝ) * a i) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring_nf
  simp_rw [h1]
  rw [sum_signs_prod (fun i s => Real.exp (l * (s : ℝ) * a i))]
  have h2 : ∀ i, Real.exp (l * ((-1 : ℤ) : ℝ) * a i) + Real.exp (l * ((1 : ℤ) : ℝ) * a i) =
      2 * Real.cosh (l * a i) := by
    intro i
    rw [Real.cosh_eq]
    push_cast
    ring_nf
  simp_rw [h2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_signs]
  push_cast
  gcongr
  calc ∏ i, Real.cosh (l * a i) ≤ ∏ i, Real.exp ((l * a i) ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) fun i _ => Real.cosh_le_exp_half_sq _
    _ = Real.exp (l ^ 2 * (∑ i, a i ^ 2) / 2) := by
        rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/- @[blueprint "lem:chernoff-finite"
  (statement := /-- \textbf{Chernoff bound on a finite probability space.} For $f : \{\pm1\}^n \to
    \mathbb R$, $t \in \mathbb R$ and $\lambda \ge 0$,
    $\#\{\sigma : f(\sigma) > t\} \le e^{-\lambda t} \sum_\sigma e^{\lambda f(\sigma)}$. -/)] -/
theorem card_filter_lt_le_exp_mul_sum (f : Signs n → ℝ) (t l : ℝ) (hl : 0 ≤ l) :
    ((Finset.univ.filter fun σ => t < f σ).card : ℝ) ≤
      Real.exp (-l * t) * ∑ σ, Real.exp (l * f σ) := by
  rw [Finset.mul_sum]
  calc ((Finset.univ.filter fun σ => t < f σ).card : ℝ)
      = ∑ σ ∈ Finset.univ.filter fun σ => t < f σ, (1 : ℝ) := by simp
    _ ≤ ∑ σ ∈ Finset.univ.filter fun σ => t < f σ, Real.exp (-l * t) * Real.exp (l * f σ) := by
        refine Finset.sum_le_sum fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        rw [← Real.exp_add]
        refine Real.one_le_exp ?_
        nlinarith [hσ.2]
    _ ≤ ∑ σ, Real.exp (-l * t) * Real.exp (l * f σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun σ _ _ => by positivity

/- @[blueprint "lem:rademacher-real-tail-one-sided"
  (statement := /-- \textbf{One-sided Hoeffding inequality for Rademacher sums.} For
    $a \in \mathbb R^n$ and $t > 0$,
    $\mathbb P_\sigma\bigl(\sum_i \sigma_i a_i > t\bigr)
    \le \exp\bigl(-t^2 / (2 \sum_i a_i^2)\bigr)$, where $\mathbb P_\sigma$ is the uniform
    distribution on $\{\pm1\}^n$ (a counting fraction). -/)] -/
theorem rademacher_real_tail_one_sided (a : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * a i).card : ℝ) /
      Fintype.card (Signs n) ≤ Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by
  have hV0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcard : (0 : ℝ) < Fintype.card (Signs n) := by
    rw [card_signs]; positivity
  rcases hV0.lt_or_eq with hVpos | hVzero
  · -- Chernoff with `λ = t / V`
    have hl0 : 0 ≤ t / ∑ i, a i ^ 2 := by positivity
    have h1 := card_filter_lt_le_exp_mul_sum (fun σ : Signs n => ∑ i, (σ i : ℝ) * a i) t
      (t / ∑ i, a i ^ 2) hl0
    have h2 := sum_signs_exp_le a (t / ∑ i, a i ^ 2)
    have h3 : Real.exp (-(t / ∑ i, a i ^ 2) * t) *
        (Fintype.card (Signs n) * Real.exp ((t / ∑ i, a i ^ 2) ^ 2 * (∑ i, a i ^ 2) / 2)) =
        Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) * Fintype.card (Signs n) := by
      have hexp : -(t / ∑ i, a i ^ 2) * t + (t / ∑ i, a i ^ 2) ^ 2 * (∑ i, a i ^ 2) / 2 =
          -t ^ 2 / (2 * ∑ i, a i ^ 2) := by
        field_simp
        ring
      rw [mul_left_comm, ← Real.exp_add, hexp, mul_comm]
    rw [div_le_iff₀ hcard, ← h3]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  · -- all `aᵢ = 0`: the event is empty
    have hzero : ∀ i, a i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (a i)).mp hVzero.symm i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hempty : (Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * a i) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
      simp [hzero, ht.le]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/- @[blueprint "lem:rademacher-real-tail"
  (statement := /-- \textbf{Hoeffding's inequality for Rademacher sums.} For $a \in \mathbb R^n$ and
    $t > 0$,
    $\mathbb P_\sigma\bigl(\bigl|\sum_i \sigma_i a_i\bigr| > t\bigr)
    \le 2\exp\bigl(-t^2 / (2 \sum_i a_i^2)\bigr)$. -/)] -/
theorem rademacher_real_tail (a : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun σ : Signs n => t < |∑ i, (σ i : ℝ) * a i|).card : ℝ) /
      Fintype.card (Signs n) ≤ 2 * Real.exp (-t ^ 2 / (2 * ∑ i, a i ^ 2)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card (Signs n) := by
    rw [card_signs]; positivity
  have hsub : (Finset.univ.filter fun σ : Signs n => t < |∑ i, (σ i : ℝ) * a i|) ⊆
      (Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * a i) ∪
        (Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * (-a i)) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rcases lt_abs.mp hσ.2 with h | h
    · exact Or.inl h
    · right
      simp only [mul_neg, Finset.sum_neg_distrib]
      exact h
  have h1 := rademacher_real_tail_one_sided a ht
  have h2 := rademacher_real_tail_one_sided (fun i => -a i) ht
  simp only [neg_sq] at h2
  rw [div_le_iff₀ hcard] at h1 h2 ⊢
  calc ((Finset.univ.filter fun σ : Signs n => t < |∑ i, (σ i : ℝ) * a i|).card : ℝ)
      ≤ ((Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * a i) ∪
          (Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * (-a i))).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * a i).card : ℝ) +
          (Finset.univ.filter fun σ : Signs n => t < ∑ i, (σ i : ℝ) * (-a i)).card := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ _ := by linarith

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- @[blueprint "lem:signs-cosh-norm-le"
  (statement := /-- \textbf{Hyperbolic-cosine moment bound for Rademacher sums in a Hilbert
    space.} For $x, v_1, \dots, v_n \in \mathcal H$ and $\lambda \in \mathbb R$,
    $$\sum_{\sigma \in \{\pm1\}^n} \cosh\Bigl(\lambda\Bigl\|x + \sum_i \sigma_i v_i\Bigr\|\Bigr)
    \le 2^n \cosh(\lambda\|x\|) \prod_i \cosh(\lambda\|v_i\|),$$
    by induction on $n$ using \texttt{lem:cosh-norm-add-sub-le} one coordinate at a time. -/)] -/
theorem sum_signs_cosh_norm_le (l : ℝ) :
    ∀ (n : ℕ) (v : Fin n → E) (x : E),
      ∑ σ : Signs n, Real.cosh (l * ‖x + ∑ i, (σ i : ℝ) • v i‖) ≤
        2 ^ n * Real.cosh (l * ‖x‖) * ∏ i, Real.cosh (l * ‖v i‖) := by
  intro n
  induction n with
  | zero =>
    intro v x
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Finset.sum_const,
      Finset.card_univ, card_signs, pow_zero, Finset.prod_empty, one_mul, mul_one, one_nsmul]
    exact le_rfl
  | succ n ih =>
    intro v x
    have hS : ∀ g : ℤ → ℝ, ∑ s : ({-1, 1} : Finset ℤ), g s = g (-1) + g 1 := by
      intro g
      rw [Finset.sum_coe_sort ({-1, 1} : Finset ℤ) g, Finset.sum_pair (by decide)]
    have hsplit : ∑ σ : Signs (n + 1), Real.cosh (l * ‖x + ∑ i, (σ i : ℝ) • v i‖) =
        ∑ s : ({-1, 1} : Finset ℤ), ∑ τ : Signs n,
          Real.cosh (l * ‖(x + (s : ℝ) • v 0) + ∑ i, (τ i : ℝ) • v i.succ‖) := by
      rw [← Fintype.sum_prod_type']
      refine (Fintype.sum_equiv (Fin.consEquiv fun _ => ({-1, 1} : Finset ℤ)) _ _ fun p => ?_).symm
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        add_assoc]
    rw [hsplit]
    have hstep : ∀ s : ({-1, 1} : Finset ℤ), ∑ τ : Signs n,
          Real.cosh (l * ‖(x + (s : ℝ) • v 0) + ∑ i, (τ i : ℝ) • v i.succ‖) ≤
        2 ^ n * Real.cosh (l * ‖x + (s : ℝ) • v 0‖) * ∏ i : Fin n, Real.cosh (l * ‖v i.succ‖) :=
      fun s => ih (fun i => v i.succ) (x + (s : ℝ) • v 0)
    calc ∑ s : ({-1, 1} : Finset ℤ), ∑ τ : Signs n,
          Real.cosh (l * ‖(x + (s : ℝ) • v 0) + ∑ i, (τ i : ℝ) • v i.succ‖)
        ≤ ∑ s : ({-1, 1} : Finset ℤ),
            2 ^ n * Real.cosh (l * ‖x + (s : ℝ) • v 0‖) * ∏ i : Fin n, Real.cosh (l * ‖v i.succ‖) :=
          Finset.sum_le_sum fun s _ => hstep s
      _ = (2 ^ n * ∏ i : Fin n, Real.cosh (l * ‖v i.succ‖)) *
            (Real.cosh (l * ‖x - v 0‖) + Real.cosh (l * ‖x + v 0‖)) := by
          rw [hS (fun s : ℤ => 2 ^ n * Real.cosh (l * ‖x + (s : ℝ) • v 0‖) *
            ∏ i : Fin n, Real.cosh (l * ‖v i.succ‖))]
          simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul, ← sub_eq_add_neg]
          ring
      _ ≤ (2 ^ n * ∏ i : Fin n, Real.cosh (l * ‖v i.succ‖)) *
            (2 * Real.cosh (l * ‖x‖) * Real.cosh (l * ‖v 0‖)) := by
          have hpos : 0 ≤ 2 ^ n * ∏ i : Fin n, Real.cosh (l * ‖v i.succ‖) :=
            mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => (Real.cosh_pos _).le)
          refine mul_le_mul_of_nonneg_left ?_ hpos
          rw [add_comm]
          exact cosh_norm_add_add_cosh_norm_sub_le x (v 0) l
      _ = 2 ^ (n + 1) * Real.cosh (l * ‖x‖) * ∏ i, Real.cosh (l * ‖v i‖) := by
          rw [Fin.prod_univ_succ, pow_succ]
          ring

/- @[blueprint "lem:chernoff-cosh-finite"
  (statement := /-- \textbf{Chernoff bound with $\cosh$ on a finite probability space.} For
    $f : \{\pm1\}^n \to \mathbb R$, $t \in \mathbb R$ and $\lambda \ge 0$,
    $\#\{\sigma : f(\sigma) > t\} \le 2 e^{-\lambda t} \sum_\sigma \cosh(\lambda f(\sigma))$,
    since $2\cosh(\lambda f) \ge e^{\lambda f} \ge e^{\lambda t}$ on the event. -/)] -/
theorem card_filter_lt_le_exp_mul_sum_cosh (f : Signs n → ℝ) (t l : ℝ) (hl : 0 ≤ l) :
    ((Finset.univ.filter fun σ => t < f σ).card : ℝ) ≤
      2 * Real.exp (-l * t) * ∑ σ, Real.cosh (l * f σ) := by
  rw [Finset.mul_sum]
  calc ((Finset.univ.filter fun σ => t < f σ).card : ℝ)
      = ∑ σ ∈ Finset.univ.filter fun σ => t < f σ, (1 : ℝ) := by simp
    _ ≤ ∑ σ ∈ Finset.univ.filter fun σ => t < f σ,
          2 * Real.exp (-l * t) * Real.cosh (l * f σ) := by
        refine Finset.sum_le_sum fun σ hσ => ?_
        rw [Finset.mem_filter] at hσ
        have h1 : Real.exp (l * t) ≤ Real.exp (l * f σ) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.2.le hl)
        have h2 : Real.exp (l * f σ) ≤ 2 * Real.cosh (l * f σ) := by
          rw [Real.cosh_eq]; have := Real.exp_pos (-(l * f σ)); linarith
        have h3 : Real.exp (-l * t) * Real.exp (l * t) = 1 := by
          rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
        calc (1 : ℝ) = Real.exp (-l * t) * Real.exp (l * t) := h3.symm
          _ ≤ Real.exp (-l * t) * (2 * Real.cosh (l * f σ)) := by
              gcongr; exact h1.trans h2
          _ = 2 * Real.exp (-l * t) * Real.cosh (l * f σ) := by ring
    _ ≤ ∑ σ, 2 * Real.exp (-l * t) * Real.cosh (l * f σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun σ _ _ => mul_nonneg (by positivity) (Real.cosh_pos _).le

/- @[blueprint "lem:rademacher-hilbert-tail"
  (statement := /-- \textbf{Hoeffding's inequality for Rademacher sums in a Hilbert space.} Let
    $\mathcal H$ be a real Hilbert space, $v_1, \dots, v_n \in \mathcal H$ and $t > 0$. Then
    $$\mathbb P_\sigma\Bigl(\Bigl\|\sum_{i=1}^n \sigma_i v_i\Bigr\| > t\Bigr)
    \le 2 \exp\Bigl(-\frac{t^2}{2\sum_{i=1}^n \|v_i\|^2}\Bigr),$$
    where $\sigma$ is uniform on $\{\pm1\}^n$. (This is the vector-valued Hoeffding / Pinelis
    inequality for Rademacher sums in $(2,1)$-smooth spaces.) Proof: by
    \texttt{lem:chernoff-cosh-finite}, \texttt{lem:signs-cosh-norm-le} and $\cosh s \le e^{s^2/2}$,
    $\mathbb P_\sigma(\|S\| > t) \le 2 e^{-\lambda t} e^{\lambda^2 V/2}$ with
    $V = \sum_i \|v_i\|^2$; take $\lambda = t/V$. -/)] -/
theorem rademacher_hilbert_tail (v : Fin n → E) {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun σ : Signs n => t < ‖∑ i, (σ i : ℝ) • v i‖).card : ℝ) /
      Fintype.card (Signs n) ≤ 2 * Real.exp (-t ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2)) := by
  have hV0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcard : (0 : ℝ) < Fintype.card (Signs n) := by
    rw [card_signs]; positivity
  rcases hV0.lt_or_eq with hVpos | hVzero
  · -- Chernoff with `λ = t / V`
    have hl0 : 0 ≤ t / ∑ i, ‖v i‖ ^ 2 := by positivity
    have h1 := card_filter_lt_le_exp_mul_sum_cosh (fun σ : Signs n => ‖∑ i, (σ i : ℝ) • v i‖) t
      (t / ∑ i, ‖v i‖ ^ 2) hl0
    have h2 := sum_signs_cosh_norm_le (t / ∑ i, ‖v i‖ ^ 2) n v 0
    simp only [zero_add, norm_zero, mul_zero, Real.cosh_zero, mul_one] at h2
    have h3 : ∏ i, Real.cosh (t / (∑ i, ‖v i‖ ^ 2) * ‖v i‖) ≤
        Real.exp ((t / ∑ i, ‖v i‖ ^ 2) ^ 2 * (∑ i, ‖v i‖ ^ 2) / 2) := by
      calc ∏ i, Real.cosh (t / (∑ i, ‖v i‖ ^ 2) * ‖v i‖)
          ≤ ∏ i, Real.exp ((t / (∑ i, ‖v i‖ ^ 2) * ‖v i‖) ^ 2 / 2) :=
            Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le)
              fun i _ => Real.cosh_le_exp_half_sq _
        _ = Real.exp ((t / ∑ i, ‖v i‖ ^ 2) ^ 2 * (∑ i, ‖v i‖ ^ 2) / 2) := by
            rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_div]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    have hexp : -(t / ∑ i, ‖v i‖ ^ 2) * t + (t / ∑ i, ‖v i‖ ^ 2) ^ 2 * (∑ i, ‖v i‖ ^ 2) / 2 =
        -t ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2) := by
      field_simp
      ring
    rw [div_le_iff₀ hcard]
    calc ((Finset.univ.filter fun σ : Signs n => t < ‖∑ i, (σ i : ℝ) • v i‖).card : ℝ)
        ≤ 2 * Real.exp (-(t / ∑ i, ‖v i‖ ^ 2) * t) *
            ∑ σ : Signs n, Real.cosh (t / (∑ i, ‖v i‖ ^ 2) * ‖∑ i, (σ i : ℝ) • v i‖) := h1
      _ ≤ 2 * Real.exp (-(t / ∑ i, ‖v i‖ ^ 2) * t) *
            (2 ^ n * ∏ i, Real.cosh (t / (∑ i, ‖v i‖ ^ 2) * ‖v i‖)) := by gcongr
      _ ≤ 2 * Real.exp (-(t / ∑ i, ‖v i‖ ^ 2) * t) *
            (2 ^ n * Real.exp ((t / ∑ i, ‖v i‖ ^ 2) ^ 2 * (∑ i, ‖v i‖ ^ 2) / 2)) := by gcongr
      _ = 2 * Real.exp (-t ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2)) * Fintype.card (Signs n) := by
          rw [card_signs, ← hexp, Real.exp_add]
          push_cast
          ring
  · -- all `vᵢ = 0`: the event is empty
    have hzero : ∀ i, v i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖v i‖).mp hVzero.symm i
        (Finset.mem_univ _)
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
    have hempty : (Finset.univ.filter fun σ : Signs n => t < ‖∑ i, (σ i : ℝ) • v i‖) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun σ _ => ?_
      simp [hzero, ht.le]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/- @[blueprint "lem:rademacher-hilbert-tail-real"
  (statement := /-- \texttt{lem:rademacher-hilbert-tail} for $\mathcal H = \mathbb R$: it is
    \texttt{lem:rademacher-real-tail}. -/)] -/
theorem rademacher_hilbert_tail_real (v : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun σ : Signs n => t < ‖∑ i, (σ i : ℝ) • v i‖).card : ℝ) /
      Fintype.card (Signs n) ≤ 2 * Real.exp (-t ^ 2 / (2 * ∑ i, ‖v i‖ ^ 2)) := by
  simpa [Real.norm_eq_abs, smul_eq_mul, sq_abs] using rademacher_real_tail v ht

end Hilbert

section Tools

/- @[blueprint "lem:union-bound-absorb"
  (statement := /-- \textbf{Absorbing a union bound into the exponent.} Let $m \ge 1$,
    $x \in \mathbb R$ and $A_m^2 := 1 + \log m / \log 2$. If $P \le 1$ and $P \le 2 m e^{-x}$ then
    $P \le 2 \exp(-x / A_m^2)$. (For $x \le \log(2m) = A_m^2 \log 2$ the right-hand side is
    $\ge 1$; for $x \ge \log(2m)$ one has $m e^{-x} \le e^{-x/A_m^2}$.) -/)] -/
theorem union_bound_absorb (m : ℕ) (hm : 1 ≤ m) {x P : ℝ} (hP1 : P ≤ 1)
    (hPm : P ≤ 2 * m * Real.exp (-x)) :
    P ≤ 2 * Real.exp (-x / (1 + Real.log m / Real.log 2)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A := 1 + Real.log m / Real.log 2 with hA
  have hA1 : 1 ≤ A := by
    rw [hA]; have := div_nonneg hlogm hlog2.le; linarith
  have hApos : 0 < A := by linarith
  have hAlog : A * Real.log 2 = Real.log 2 + Real.log m := by
    rw [hA]; field_simp
  by_cases hcase : x ≤ A * Real.log 2
  · -- small-$x$ regime: the right-hand side is at least $1$
    have h1 : Real.exp (-Real.log 2) ≤ Real.exp (-x / A) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ hApos]
      linarith
    rw [Real.exp_neg, Real.exp_log two_pos] at h1
    linarith
  · -- large-$x$ regime: $m e^{-x} \le e^{-x / A}$
    rw [not_le] at hcase
    have hlm : Real.log m = (A - 1) * Real.log 2 := by linear_combination -hAlog
    have hkey : Real.log m + -x ≤ -x / A := by
      rw [le_div_iff₀ hApos]
      have h1 : (A - 1) * (A * Real.log 2) ≤ (A - 1) * x :=
        mul_le_mul_of_nonneg_left hcase.le (by linarith)
      linear_combination h1 + A * hlm
    have h2 : (m : ℝ) * Real.exp (-x) ≤ Real.exp (-x / A) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < m), ← Real.exp_add]
      exact Real.exp_le_exp.mpr hkey
    calc P ≤ 2 * m * Real.exp (-x) := hPm
      _ = 2 * (m * Real.exp (-x)) := by ring
      _ ≤ 2 * Real.exp (-x / A) := by gcongr

end Tools

end FoML.ToFoML
