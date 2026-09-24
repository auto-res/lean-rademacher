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
import FoML.ToFoML.VectorHoeffding
import FoML.ToFoML.DudleySubGaussian

/-!
# Bernoulli-side tools for the Sudakov minoration (B2, B4, B8, B10)

This file collects the elementary, purely Bernoulli/combinatorial ingredients of the proof of the
Bernoulli–Sudakov minoration `bernoulli_sudakov` (`FoML.ToFoML.BernoulliSudakov`),
following the blueprint lean-deepgen's `00note/sudakov-math.md` (route ULB §6.4 + Sudakov–Fernique). Nothing
here depends on the Gaussian side.

Notation. For `u : Fin M → Fin n → ℝ` the **Bernoulli supremum** is the counting average over
the `2^n` sign patterns

`b(u) = bernoulliSup u = 2^{-n} ∑_σ max_j ∑_i σ_i u_{j,i}`

(`def:bernoulli-sup`; `⨆ j : Fin 0` is `0`).

* **B8** (`lem:bernoulli-sup-sub-const`, `lem:bernoulli-sup-comp-injective`,
  `lem:bernoulli-sup-eq-target`): shift invariance `b(u - t) = b(u)`, monotonicity in
  sub-families `b(u ∘ ι) ≤ b(u)`, nonnegativity, and the identity relating `(1/n) b(u)` to the
  right-hand side of `bernoulli_sudakov`.
* **B2** (`lem:bernoulli-contraction-pointwise`): the deterministic contraction principle
  `b((α_i u_{j,i})_{j,i}) ≤ c · b(u)` for `|α_i| ≤ c`, through the product-weight convex
  combination `α = c ∑_τ w(τ) τ`, `w(τ) = ∏_i (1 + τ_i α_i / c)/2` (`def:sign-weight`), and the
  bijection `σ ↦ τ ⊙ σ` of `Signs n` (`def:mul-signs`).
* **B4** (`lem:max-le-log-sum-exp-expect`, `lem:max-le-log-sum-exp-integral`): the
  finite-maximum-via-MGF bound `E max_j Y_j ≤ λ^{-1} log ∑_j E exp(λ Y_j)`, for the counting
  average on a finite type and for a probability measure; the proof is the pointwise inequality
  `max_j y_j ≤ s + λ^{-1}(e^{-λ s} ∑_j e^{λ y_j} - 1)` (`lem:max-le-log-sum-exp-pointwise`)
  with `s = λ^{-1} log ∑_j E e^{λ Y_j}` — no Jensen needed. (The blueprint's `1 + log` form
  follows a fortiori.)
* **B10** (`lem:separated-net-counting` and its pieces): the multiscale counting lemma of the
  blueprint's S11, in a standalone metric/combinatorial form on an indexed finite family
  `u : ι → X` in a pseudo-metric space: a maximal `r`-separated subfamily is an `r`-net
  (`lem:exists-separated-net`), the ball-count growth `N(2r) ≤ K · N(r)` when every
  `r`-separated subfamily of a `2r`-ball has at most `K` points (`lem:ball-count-two-mul-le`),
  and the iteration `|ι| ≤ ∏_{k<K} κ_k` (`lem:separated-net-counting`). The Bernoulli bound
  `b(u)` enters only through the hypothesis `κ_k` (supplied by B9 in B11); the geometric sum
  `∑_{k<K} 4·(1/4)^k ≤ 16/3` (`lem:geom-sum-four-le`), the elementary
  `log(N+1) ≤ 2 log N` for `N ≥ 2` (`lem:log-two-le`) and the Euclidean distance formula
  (`lem:euclidean-dist-eq`) are provided for B11.

This file depends only on Mathlib, FoML and the `ToFoML` modules `SudakovMinoration`,
`VectorHoeffding`, `DudleySubGaussian`.
-/

open Real MeasureTheory
open scoped BigOperators

namespace FoML.ToFoML

variable {n : ℕ}

/-! ### The Bernoulli supremum functional -/

/- @[blueprint "def:bernoulli-sup"
  (statement := /-- For $u_1, \dots, u_M \in \mathbb R^n$ the \textbf{Bernoulli supremum} is
    $$b(u) := 2^{-n} \sum_{\sigma \in \{\pm1\}^n} \max_{j \le M} \sum_{i} \sigma_i u_{j,i}$$
    (the one-sided Rademacher average of the family; for $M = 0$ the maximum is $0$). -/)] -/
noncomputable def bernoulliSup {M : ℕ} (u : Fin M → Fin n → ℝ) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, ⨆ j, ∑ i, (σ i : ℝ) * u j i

/- @[blueprint "lem:bernoulli-sup-empty"
  (statement := /-- $b(u) = 0$ for the empty family ($M = 0$). -/)] -/
theorem bernoulliSup_of_isEmpty {M : ℕ} [IsEmpty (Fin M)] (u : Fin M → Fin n → ℝ) :
    bernoulliSup u = 0 := by
  simp [bernoulliSup, Real.iSup_of_isEmpty]

/- @[blueprint "lem:bernoulli-sup-nonneg"
  (statement := /-- $b(u) \ge 0$ for a nonempty family (pair $\sigma$ with $-\sigma$). -/)] -/
theorem bernoulliSup_nonneg {M : ℕ} [Nonempty (Fin M)] (u : Fin M → Fin n → ℝ) :
    0 ≤ bernoulliSup u := by
  unfold bernoulliSup
  refine mul_nonneg (by positivity) ?_
  set G : Signs n → ℝ := fun σ => ⨆ j, ∑ i : Fin n, (σ i : ℝ) * u j i with hG
  have hflip : ∑ σ, G σ = ∑ σ, G (negSigns σ) :=
    (Fintype.sum_equiv negSigns_involutive.toPerm (fun σ => G (negSigns σ)) G
      (fun σ => rfl)).symm
  have hpair : ∀ σ, 0 ≤ G σ + G (negSigns σ) := by
    intro σ
    obtain ⟨j₀⟩ := ‹Nonempty (Fin M)›
    have h1 : ∑ i : Fin n, (σ i : ℝ) * u j₀ i ≤ G σ :=
      le_ciSup (f := fun j => ∑ i : Fin n, (σ i : ℝ) * u j i) (Set.finite_range _).bddAbove j₀
    have h2 : ∑ i : Fin n, (negSigns σ i : ℝ) * u j₀ i ≤ G (negSigns σ) :=
      le_ciSup (f := fun j => ∑ i : Fin n, (negSigns σ i : ℝ) * u j i)
        (Set.finite_range _).bddAbove j₀
    have h3 : ∑ i : Fin n, (negSigns σ i : ℝ) * u j₀ i =
        -(∑ i : Fin n, (σ i : ℝ) * u j₀ i) := by
      simp only [negSigns, coe_neg_sign, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    linarith
  have h2 : 0 ≤ 2 * ∑ σ, G σ := by
    calc (0 : ℝ) ≤ ∑ σ, (G σ + G (negSigns σ)) := Finset.sum_nonneg fun σ _ => hpair σ
      _ = ∑ σ, G σ + ∑ σ, G (negSigns σ) := Finset.sum_add_distrib
      _ = 2 * ∑ σ, G σ := by rw [← hflip]; ring
  linarith

/-! ### B8: shift invariance, monotonicity, normalisation -/

/- @[blueprint "lem:bernoulli-sup-sub-const"
  (statement := /-- \textbf{Shift invariance.} For a fixed $t \in \mathbb R^n$,
    $b\bigl((u_j - t)_j\bigr) = b(u)$, since $\sum_\sigma \sum_i \sigma_i t_i = 0$. -/)] -/
theorem bernoulliSup_sub_const {M : ℕ} (u : Fin M → Fin n → ℝ) (t : Fin n → ℝ) :
    bernoulliSup (fun j i => u j i - t i) = bernoulliSup u := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [bernoulliSup, Real.iSup_of_isEmpty]
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  unfold bernoulliSup
  congr 1
  have hσ : ∀ σ : Signs n, (⨆ j, ∑ i, (σ i : ℝ) * (u j i - t i)) =
      (⨆ j, ∑ i, (σ i : ℝ) * u j i) - ∑ i, (σ i : ℝ) * t i := by
    intro σ
    rw [ciSup_sub (Set.finite_range _).bddAbove]
    refine iSup_congr fun j => ?_
    simp only [mul_sub, Finset.sum_sub_distrib]
  simp_rw [hσ]
  rw [Finset.sum_sub_distrib, sum_signs_rademacher_sum, sub_zero]

/- @[blueprint "lem:bernoulli-sup-comp-injective"
  (statement := /-- \textbf{Monotonicity in sub-families.} For any map
    $\iota : \{1,\dots,M'\} \to \{1,\dots,M\}$ (in particular an injection selecting a
    sub-family), $b(u \circ \iota) \le b(u)$. (Injectivity is not needed: for $M' \ge 1$ the
    maximum over the image is at most the maximum over all of $u$; for $M' = 0$ the left-hand
    side is $0 \le b(u)$.) -/)] -/
theorem bernoulliSup_comp_le {M M' : ℕ} (u : Fin M → Fin n → ℝ) (ι : Fin M' → Fin M) :
    bernoulliSup (u ∘ ι) ≤ bernoulliSup u := by
  rcases Nat.eq_zero_or_pos M' with hM' | hM'
  · subst hM'
    rw [bernoulliSup_of_isEmpty]
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; rw [bernoulliSup_of_isEmpty]
    · haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
      exact bernoulliSup_nonneg u
  haveI : Nonempty (Fin M') := ⟨⟨0, hM'⟩⟩
  unfold bernoulliSup
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  exact ciSup_le fun j' =>
    le_ciSup (f := fun j => ∑ i, (σ i : ℝ) * u j i) (Set.finite_range _).bddAbove (ι j')

/- @[blueprint "lem:bernoulli-sup-eq-target"
  (statement := /-- \textbf{Normalisation.} $\frac1n b(u) = 2^{-n}\sum_\sigma \max_j \frac1n
    \sum_i \sigma_i u_{j,i}$, the right-hand side of \texttt{thm:bernoulli-sudakov}. -/)] -/
theorem inv_mul_bernoulliSup {M : ℕ} (u : Fin M → Fin n → ℝ) :
    (n : ℝ)⁻¹ * bernoulliSup u =
      (Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n, ⨆ j, (n : ℝ)⁻¹ * ∑ i : Fin n, (σ i : ℝ) * u j i := by
  unfold bernoulliSup
  rw [mul_left_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact Real.mul_iSup_of_nonneg (by positivity) _

/-! ### Signs: elementary facts and the product `τ ⊙ σ` -/

/- @[blueprint "lem:sign-mem"
  (statement := /-- An element of $\{-1, 1\}$ is $-1$ or $1$. -/)] -/
theorem sign_mem (s : ({-1, 1} : Finset ℤ)) : (s : ℤ) = -1 ∨ (s : ℤ) = 1 := by
  have := s.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  exact this

/- @[blueprint "lem:coe-sign-eq"
  (statement := /-- As a real number, a sign is $-1$ or $1$. -/)] -/
theorem coe_sign_eq (s : ({-1, 1} : Finset ℤ)) : ((s : ℤ) : ℝ) = -1 ∨ ((s : ℤ) : ℝ) = 1 := by
  rcases sign_mem s with h | h
  · left; rw [h]; push_cast; rfl
  · right; rw [h]; push_cast; rfl

/- @[blueprint "lem:sign-mul-self"
  (statement := /-- $s \cdot s = 1$ for $s \in \{-1, 1\}$. -/)] -/
theorem sign_mul_self (s : ({-1, 1} : Finset ℤ)) : (s : ℤ) * s = 1 := by
  rcases sign_mem s with h | h <;> rw [h] <;> norm_num

/- @[blueprint "def:mul-signs"
  (statement := /-- The coordinatewise product $\tau \odot \sigma := (\tau_i \sigma_i)_i$ on
    $\{\pm1\}^n$. -/)] -/
def mulSigns (τ σ : Signs n) : Signs n := fun i =>
  ⟨(τ i : ℤ) * (σ i : ℤ), by
    rcases sign_mem (τ i) with h1 | h1 <;> rcases sign_mem (σ i) with h2 | h2 <;>
      simp [h1, h2]⟩

/- @[blueprint "lem:coe-mul-signs"
  (statement := /-- $(\tau \odot \sigma)_i = \tau_i \sigma_i$ as real numbers. -/)] -/
theorem coe_mulSigns (τ σ : Signs n) (i : Fin n) :
    ((mulSigns τ σ i : ℤ) : ℝ) = (τ i : ℝ) * (σ i : ℝ) := by
  simp [mulSigns]

/- @[blueprint "lem:mul-signs-involutive"
  (statement := /-- For fixed $\tau$, $\sigma \mapsto \tau \odot \sigma$ is an involution
    (hence a bijection) of $\{\pm1\}^n$, since $\tau_i^2 = 1$. -/)] -/
theorem mulSigns_involutive (τ : Signs n) : Function.Involutive (mulSigns τ) := by
  intro σ
  funext i
  apply Subtype.ext
  change (τ i : ℤ) * ((τ i : ℤ) * (σ i : ℤ)) = (σ i : ℤ)
  rw [← mul_assoc, sign_mul_self, one_mul]

/- @[blueprint "lem:sum-mul-signs"
  (statement := /-- $\sum_\sigma F(\tau \odot \sigma) = \sum_\sigma F(\sigma)$. -/)] -/
theorem sum_mulSigns (τ : Signs n) (F : Signs n → ℝ) :
    ∑ σ : Signs n, F (mulSigns τ σ) = ∑ σ : Signs n, F σ :=
  Fintype.sum_equiv (mulSigns_involutive τ).toPerm _ _ (fun _ => rfl)

/-! ### Product weights -/

/- @[blueprint "def:sign-weight"
  (statement := /-- For $p \in [-1,1]^n$ the \textbf{product weights}
    $w_p(\tau) := \prod_i \frac{1 + \tau_i p_i}{2}$ on $\{\pm1\}^n$: the law of independent
    signs $\tau_i$ with $\mathbb P(\tau_i = \pm1) = (1 \pm p_i)/2$, so that
    $\mathbb E \tau_i = p_i$. -/)] -/
noncomputable def signWeight (p : Fin n → ℝ) (τ : Signs n) : ℝ :=
  ∏ k, (1 + (τ k : ℝ) * p k) / 2

/- @[blueprint "lem:sign-weight-nonneg"
  (statement := /-- $w_p(\tau) \ge 0$ when $|p_i| \le 1$ for all $i$. -/)] -/
theorem signWeight_nonneg {p : Fin n → ℝ} (hp : ∀ i, |p i| ≤ 1) (τ : Signs n) :
    0 ≤ signWeight p τ := by
  unfold signWeight
  refine Finset.prod_nonneg fun k _ => ?_
  obtain ⟨h1, h2⟩ := abs_le.mp (hp k)
  rcases coe_sign_eq (τ k) with h | h <;> rw [h] <;> linarith

/- @[blueprint "lem:sum-sign-weight"
  (statement := /-- $\sum_{\tau \in \{\pm1\}^n} w_p(\tau) = \prod_i \bigl(\frac{1-p_i}2 +
    \frac{1+p_i}2\bigr) = 1$. -/)] -/
theorem sum_signWeight (p : Fin n → ℝ) : ∑ τ : Signs n, signWeight p τ = 1 := by
  unfold signWeight
  rw [sum_signs_prod (fun k (s : ℤ) => (1 + (s : ℝ) * p k) / 2)]
  refine Finset.prod_eq_one fun k _ => ?_
  push_cast
  ring

/- @[blueprint "lem:sum-sign-weight-mul"
  (statement := /-- $\sum_{\tau} w_p(\tau)\, \tau_i = p_i$: the $i$-th factor contributes
    $\frac{1-p_i}2 \cdot (-1) + \frac{1+p_i}2 \cdot 1 = p_i$ and the others contribute $1$. -/)] -/
theorem sum_signWeight_mul (p : Fin n → ℝ) (i : Fin n) :
    ∑ τ : Signs n, signWeight p τ * (τ i : ℝ) = p i := by
  classical
  have h : ∀ τ : Signs n, signWeight p τ * (τ i : ℝ) =
      ∏ k, ((1 + (τ k : ℝ) * p k) / 2 * if k = i then (τ k : ℝ) else 1) := by
    intro τ
    rw [signWeight, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ i)]
  simp_rw [h]
  rw [sum_signs_prod (fun k (s : ℤ) => (1 + (s : ℝ) * p k) / 2 * if k = i then (s : ℝ) else 1)]
  rw [Finset.prod_eq_single i]
  · simp only [if_true]; push_cast; ring
  · intro k _ hk; simp only [if_neg hk]; push_cast; ring
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ### B2: the deterministic contraction principle -/

/- @[blueprint "lem:bernoulli-contraction-pointwise"
  (statement := /-- \textbf{Contraction principle (deterministic, finite).} Let
    $u_1,\dots,u_M \in \mathbb R^n$, $c \ge 0$ and $\alpha \in \mathbb R^n$ with $|\alpha_i| \le c$
    for all $i$. Then
    $$2^{-n} \sum_{\sigma} \max_j \sum_i \sigma_i \alpha_i u_{j,i} \ \le\ c\, b(u).$$
    Proof: for $c > 0$ write $\alpha = c \sum_\tau w(\tau)\, \tau$ with the product weights
    $w = w_{\alpha/c}$ (\texttt{lem:sum-sign-weight-mul}); then for each $\sigma$,
    $\max_j \sum_i \sigma_i \alpha_i u_{j,i} = \max_j \sum_\tau w(\tau)\, c \sum_i
    (\tau \odot \sigma)_i u_{j,i} \le \sum_\tau w(\tau)\, c \max_j \sum_i (\tau\odot\sigma)_i
    u_{j,i}$ (convexity of the maximum), and averaging over $\sigma$ with the bijection
    $\sigma \mapsto \tau \odot \sigma$ gives $\le \sum_\tau w(\tau)\, c\, b(u) = c\,b(u)$.
    For $c = 0$ both sides vanish. (ULB Lemma 6.4.4 / LT Thm 4.4, one-sided version.) -/)] -/
theorem bernoulliSup_mul_le {M : ℕ} (u : Fin M → Fin n → ℝ) (α : Fin n → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hα : ∀ i, |α i| ≤ c) :
    bernoulliSup (fun j i => α i * u j i) ≤ c * bernoulliSup u := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [bernoulliSup, Real.iSup_of_isEmpty]
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  rcases hc.eq_or_lt with hc0 | hcpos
  · subst hc0
    have hα0 : ∀ i, α i = 0 := fun i => abs_nonpos_iff.mp (hα i)
    simp [bernoulliSup, hα0, ciSup_const]
  -- the weights
  obtain ⟨p, hp⟩ : ∃ p : Fin n → ℝ, p = fun i => α i / c := ⟨_, rfl⟩
  have hp1 : ∀ i, |p i| ≤ 1 := fun i => by
    rw [hp, abs_div, abs_of_pos hcpos, div_le_one hcpos]
    exact hα i
  have hα_eq : ∀ i, α i = c * ∑ τ, signWeight p τ * (τ i : ℝ) := fun i => by
    rw [sum_signWeight_mul p i, hp]
    field_simp
  obtain ⟨f, hf⟩ : ∃ f : Signs n → ℝ, f = fun σ => ⨆ j, ∑ i, (σ i : ℝ) * u j i := ⟨_, rfl⟩
  have hbdd : ∀ σ : Signs n, BddAbove (Set.range fun j => ∑ i, (σ i : ℝ) * u j i) :=
    fun σ => (Set.finite_range _).bddAbove
  -- pointwise in `σ`: the maximum of a convex combination is at most the combination of maxima
  have hpt : ∀ σ : Signs n, (⨆ j, ∑ i, (σ i : ℝ) * (α i * u j i)) ≤
      ∑ τ, signWeight p τ * (c * f (mulSigns τ σ)) := by
    intro σ
    refine ciSup_le fun j => ?_
    calc ∑ i, (σ i : ℝ) * (α i * u j i)
        = ∑ i, ∑ τ, signWeight p τ * (c * ((mulSigns τ σ i : ℝ) * u j i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hα_eq i, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [coe_mulSigns]
          ring
      _ = ∑ τ, signWeight p τ * (c * ∑ i, (mulSigns τ σ i : ℝ) * u j i) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ τ, signWeight p τ * (c * f (mulSigns τ σ)) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hcpos.le)
            (signWeight_nonneg hp1 τ)
          rw [hf]
          exact le_ciSup (hbdd _) j
  -- average over `σ`
  have hsum : ∑ σ : Signs n, (⨆ j, ∑ i, (σ i : ℝ) * (α i * u j i)) ≤ c * ∑ σ, f σ := by
    calc ∑ σ : Signs n, (⨆ j, ∑ i, (σ i : ℝ) * (α i * u j i))
        ≤ ∑ σ, ∑ τ, signWeight p τ * (c * f (mulSigns τ σ)) :=
          Finset.sum_le_sum fun σ _ => hpt σ
      _ = ∑ τ, signWeight p τ * (c * ∑ σ, f (mulSigns τ σ)) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ = ∑ τ, signWeight p τ * (c * ∑ σ, f σ) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [sum_mulSigns]
      _ = c * ∑ σ, f σ := by rw [← Finset.sum_mul, sum_signWeight, one_mul]
  unfold bernoulliSup
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  subst hf
  exact hsum

/-! ### B4: a finite maximum through the moment generating function -/

/- @[blueprint "lem:max-le-log-sum-exp-pointwise"
  (statement := /-- For $y_1,\dots,y_m \in \mathbb R$ ($m \ge 1$), $\lambda > 0$ and any
    $s \in \mathbb R$,
    $$\max_j y_j \le s + \lambda^{-1}\Bigl(e^{-\lambda s}\sum_j e^{\lambda y_j} - 1\Bigr),$$
    from $\lambda(y_j - s) + 1 \le e^{\lambda(y_j - s)} \le \sum_k e^{\lambda(y_k - s)}$. -/)] -/
theorem iSup_le_add_inv_mul_sum_exp {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → ℝ) {l : ℝ}
    (hl : 0 < l) (s : ℝ) :
    (⨆ j, y j) ≤ s + l⁻¹ * (Real.exp (-(l * s)) * ∑ j, Real.exp (l * y j) - 1) := by
  refine ciSup_le fun j => ?_
  have h1 : l * (y j - s) + 1 ≤ Real.exp (l * (y j - s)) := Real.add_one_le_exp _
  have h2 : Real.exp (l * (y j - s)) ≤ ∑ k, Real.exp (l * (y k - s)) :=
    Finset.single_le_sum (f := fun k => Real.exp (l * (y k - s)))
      (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)
  have h3 : ∑ k, Real.exp (l * (y k - s)) = Real.exp (-(l * s)) * ∑ k, Real.exp (l * y k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.exp_add]
    ring_nf
  rw [← h3]
  have h4 : y j - s ≤ l⁻¹ * (∑ k, Real.exp (l * (y k - s)) - 1) := by
    rw [le_inv_mul_iff₀ hl]
    linarith
  linarith

/- @[blueprint "lem:max-le-log-sum-exp-expect"
  (statement := /-- \textbf{Finite maximum via the MGF (counting average).} Let $\Omega$ be a
    finite nonempty set with the uniform distribution, $Y_1,\dots,Y_m : \Omega \to \mathbb R$
    ($m \ge 1$) and $\lambda > 0$. Then
    $$\mathbb E \max_j Y_j \le \lambda^{-1} \log \sum_j \mathbb E\, e^{\lambda Y_j}.$$
    Proof: average \texttt{lem:max-le-log-sum-exp-pointwise} and take
    $s = \lambda^{-1}\log\sum_j \mathbb E e^{\lambda Y_j}$, for which the bracket vanishes.
    (This is sharper than the blueprint's $\lambda^{-1}(1 + \log \sum_j \cdots)$.) -/)] -/
theorem uniformExpect_iSup_le_log_sum_exp {Ω : Type*} [Fintype Ω] [Nonempty Ω] {ι : Type*}
    [Fintype ι] [Nonempty ι] (Y : ι → Ω → ℝ) {l : ℝ} (hl : 0 < l) :
    uniformExpect (fun ω => ⨆ j, Y j ω) ≤
      l⁻¹ * Real.log (∑ j, uniformExpect fun ω => Real.exp (l * Y j ω)) := by
  set S : ℝ := ∑ j, uniformExpect fun ω => Real.exp (l * Y j ω) with hS
  have hSpos : 0 < S := by
    rw [hS]
    refine Finset.sum_pos (fun j _ => ?_) Finset.univ_nonempty
    unfold uniformExpect
    exact mul_pos (by positivity)
      (Finset.sum_pos (fun ω _ => Real.exp_pos _) Finset.univ_nonempty)
  set s : ℝ := l⁻¹ * Real.log S with hs
  have hexp : Real.exp (-(l * s)) = S⁻¹ := by
    rw [hs, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul, Real.exp_neg, Real.exp_log hSpos]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc uniformExpect (fun ω => ⨆ j, Y j ω)
      ≤ uniformExpect (fun ω =>
          s + l⁻¹ * (Real.exp (-(l * s)) * ∑ j, Real.exp (l * Y j ω) - 1)) :=
        uniformExpect_mono fun ω => iSup_le_add_inv_mul_sum_exp (fun j => Y j ω) hl s
    _ = s + l⁻¹ * (Real.exp (-(l * s)) * S - 1) := by
        rw [hS]
        unfold uniformExpect
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
        rw [Finset.sum_comm]
        field_simp
    _ = s := by rw [hexp, inv_mul_cancel₀ hSpos.ne', sub_self, mul_zero, add_zero]

/- @[blueprint "lem:max-le-log-sum-exp-integral"
  (statement := /-- \textbf{Finite maximum via the MGF (probability measure).} Let $\mu$ be a
    probability measure, $Y_1,\dots,Y_m$ ($m \ge 1$) real random variables with $\max_j Y_j$
    and each $e^{\lambda Y_j}$ integrable, $\lambda > 0$. Then
    $$\int \max_j Y_j \,d\mu \le \lambda^{-1} \log \sum_j \int e^{\lambda Y_j}\,d\mu.$$
    Same proof as \texttt{lem:max-le-log-sum-exp-expect}. -/)] -/
theorem integral_iSup_le_log_sum_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [Nonempty ι] (Y : ι → Ω → ℝ) {l : ℝ}
    (hl : 0 < l) (hsup : Integrable (fun ω => ⨆ j, Y j ω) μ)
    (hexp : ∀ j, Integrable (fun ω => Real.exp (l * Y j ω)) μ) :
    ∫ ω, (⨆ j, Y j ω) ∂μ ≤ l⁻¹ * Real.log (∑ j, ∫ ω, Real.exp (l * Y j ω) ∂μ) := by
  set S : ℝ := ∑ j, ∫ ω, Real.exp (l * Y j ω) ∂μ with hS
  have hSpos : 0 < S := by
    rw [hS]
    refine Finset.sum_pos (fun j _ => ?_) Finset.univ_nonempty
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun ω =>
      (Real.exp_pos _).le) (hexp j)]
    have hsupp : Function.support (fun ω => Real.exp (l * Y j ω)) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (Real.exp_pos _).ne'
    rw [hsupp]
    simp
  set s : ℝ := l⁻¹ * Real.log S with hs
  have hexps : Real.exp (-(l * s)) = S⁻¹ := by
    rw [hs, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul, Real.exp_neg, Real.exp_log hSpos]
  have hI1 : Integrable (fun ω => ∑ j, Real.exp (l * Y j ω)) μ :=
    integrable_finsetSum _ fun j _ => hexp j
  have hI2 : Integrable
      (fun ω => l⁻¹ * (Real.exp (-(l * s)) * ∑ j, Real.exp (l * Y j ω) - 1)) μ :=
    ((hI1.const_mul _).sub (integrable_const 1)).const_mul _
  calc ∫ ω, (⨆ j, Y j ω) ∂μ
      ≤ ∫ ω, (s + l⁻¹ * (Real.exp (-(l * s)) * ∑ j, Real.exp (l * Y j ω) - 1)) ∂μ :=
        integral_mono hsup ((integrable_const s).add hI2)
          fun ω => iSup_le_add_inv_mul_sum_exp (fun j => Y j ω) hl s
    _ = s + l⁻¹ * (Real.exp (-(l * s)) * S - 1) := by
        rw [integral_add (integrable_const s) hI2, integral_const, integral_const_mul,
          integral_sub (hI1.const_mul _) (integrable_const 1), integral_const_mul,
          integral_finsetSum _ fun j _ => hexp j, integral_const, probReal_univ, one_smul,
          one_smul, hS]
    _ = s := by rw [hexps, inv_mul_cancel₀ hSpos.ne', sub_self, mul_zero, add_zero]

/-! ### B10: the multiscale counting lemma (metric/combinatorial skeleton) -/

section Counting

variable {X : Type*} [PseudoMetricSpace X] {ι : Type*}

/- @[blueprint "def:ball-count"
  (statement := /-- For a finite family $u : I \to X$ in a pseudo-metric space and $r \ge 0$,
    $N_u(r) := \max_{t \in I} \bigl|\{j \in I : d(u_j, u_t) \le r\}\bigr|$, the largest number
    of points of the family in a closed $r$-ball centred at a point of the family. -/)] -/
noncomputable def ballCount [Fintype ι] (u : ι → X) (r : ℝ) : ℕ :=
  Finset.univ.sup fun t => (Finset.univ.filter fun j => dist (u j) (u t) ≤ r).card

/- @[blueprint "lem:exists-separated-net"
  (statement := /-- \textbf{A maximal separated subfamily is a net.} Let $u : I \to X$, $r > 0$
    and $S \subseteq I$ finite. There is $J \subseteq S$ which is $r$-separated
    ($d(u_j, u_l) \ge r$ for $j \ne l$ in $J$) and such that every $x \in S$ satisfies
    $d(u_x, u_j) < r$ for some $j \in J$. (Take $J$ of maximal cardinality among the
    $r$-separated subsets of $S$; a point at distance $\ge r$ from all of $J$ could be added.) -/)] -/
theorem exists_separated_net (u : ι → X) {r : ℝ} (hr : 0 < r) (S : Finset ι) :
    ∃ J ⊆ S, (∀ j ∈ J, ∀ l ∈ J, j ≠ l → r ≤ dist (u j) (u l)) ∧
      ∀ x ∈ S, ∃ j ∈ J, dist (u x) (u j) < r := by
  classical
  obtain ⟨J, hJmem, hJmax⟩ := Finset.exists_max_image
    (S.powerset.filter fun J => ∀ j ∈ J, ∀ l ∈ J, j ≠ l → r ≤ dist (u j) (u l))
    Finset.card ⟨∅, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
  refine ⟨J, hJmem.1, hJmem.2, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxJ : x ∉ J := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hins : ∀ j ∈ insert x J, ∀ l ∈ insert x J, j ≠ l → r ≤ dist (u j) (u l) := by
    intro j hj l hl hjl
    rw [Finset.mem_insert] at hj hl
    rcases hj with rfl | hj <;> rcases hl with rfl | hl
    · exact absurd rfl hjl
    · exact hcon l hl
    · rw [dist_comm]; exact hcon j hj
    · exact hJmem.2 j hj l hl hjl
  have hle := hJmax (insert x J) (by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hx hJmem.1, hins⟩)
  rw [Finset.card_insert_of_notMem hxJ] at hle
  omega

/- @[blueprint "lem:ball-count-two-mul-le"
  (statement := /-- \textbf{Ball-count growth.} Let $u : I \to X$ ($I$ finite nonempty),
    $r > 0$, and suppose that every $r$-separated subfamily of the family contained in a closed
    $2r$-ball centred at a point of the family has at most $K$ elements. Then
    $N_u(2r) \le K \cdot N_u(r)$. (Cover the $2r$-ball by the $r$-balls around a maximal
    $r$-separated subfamily, \texttt{lem:exists-separated-net}, and use a union bound.) -/)] -/
theorem ballCount_two_mul_le [Fintype ι] [Nonempty ι] (u : ι → X) {r : ℝ} (hr : 0 < r) {K : ℝ}
    (hpack : ∀ t, ∀ J : Finset ι, (∀ j ∈ J, dist (u j) (u t) ≤ 2 * r) →
      (∀ j ∈ J, ∀ l ∈ J, j ≠ l → r ≤ dist (u j) (u l)) → (J.card : ℝ) ≤ K) :
    (ballCount u (2 * r) : ℝ) ≤ K * ballCount u r := by
  classical
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun t => (Finset.univ.filter fun j => dist (u j) (u t) ≤ 2 * r).card)
  unfold ballCount
  rw [ht]
  set S := Finset.univ.filter fun j => dist (u j) (u t) ≤ 2 * r with hSdef
  obtain ⟨J, hJS, hJsep, hJnet⟩ := exists_separated_net u hr S
  have hcover : S ⊆ J.biUnion fun j => Finset.univ.filter fun x => dist (u x) (u j) ≤ r := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hJnet x hx
    rw [Finset.mem_biUnion]
    exact ⟨j, hj, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hxj.le⟩⟩
  have hcard : S.card ≤ J.card * ballCount u r := by
    calc S.card ≤ (J.biUnion fun j => Finset.univ.filter fun x => dist (u x) (u j) ≤ r).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ j ∈ J, (Finset.univ.filter fun x => dist (u x) (u j) ≤ r).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, ballCount u r :=
          Finset.sum_le_sum fun j _ => Finset.le_sup (f := fun t =>
            (Finset.univ.filter fun x => dist (u x) (u t) ≤ r).card) (Finset.mem_univ j)
      _ = J.card * ballCount u r := by rw [Finset.sum_const, smul_eq_mul]
  have hJK : (J.card : ℝ) ≤ K := hpack t J
    (fun j hj => by have := hJS hj; rw [hSdef, Finset.mem_filter] at this; exact this.2) hJsep
  calc (S.card : ℝ) ≤ (J.card : ℝ) * ballCount u r := by exact_mod_cast hcard
    _ ≤ K * ballCount u r := mul_le_mul_of_nonneg_right hJK (Nat.cast_nonneg _)

/- @[blueprint "lem:ball-count-le-one"
  (statement := /-- If the family is $a$-separated and $r < a$ then $N_u(r) \le 1$: a closed
    $r$-ball centred at $u_t$ contains no other point of the family. -/)] -/
theorem ballCount_le_one_of_separated [Fintype ι] (u : ι → X) {a r : ℝ} (hra : r < a)
    (hsep : ∀ j l, j ≠ l → a ≤ dist (u j) (u l)) : ballCount u r ≤ 1 := by
  classical
  unfold ballCount
  refine Finset.sup_le fun t _ => ?_
  refine Finset.card_le_one.mpr fun x hx y hy => ?_
  rw [Finset.mem_filter] at hx hy
  have hx' : x = t := by
    by_contra h
    have := hsep x t h
    linarith [hx.2]
  have hy' : y = t := by
    by_contra h
    have := hsep y t h
    linarith [hy.2]
  rw [hx', hy']

/- @[blueprint "lem:card-le-ball-count"
  (statement := /-- If $d(u_j, u_l) \le r$ for all $j, l$ (e.g. $r \ge \operatorname{diam}$)
    then $|I| \le N_u(r)$. -/)] -/
theorem card_le_ballCount [Fintype ι] (u : ι → X) {r : ℝ} (hdiam : ∀ j l, dist (u j) (u l) ≤ r) :
    Fintype.card ι ≤ ballCount u r := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨t⟩ := hι
  unfold ballCount
  refine le_trans ?_ (Finset.le_sup (f := fun t =>
    (Finset.univ.filter fun j => dist (u j) (u t) ≤ r).card) (Finset.mem_univ t))
  change Fintype.card ι ≤ (Finset.univ.filter fun j => dist (u j) (u t) ≤ r).card
  rw [Finset.filter_true_of_mem fun j _ => hdiam j t, Finset.card_univ]

/- @[blueprint "lem:ball-count-pow-le"
  (statement := /-- \textbf{Iterated growth.} Let $u : I \to X$ ($I$ finite nonempty),
    $r_0 > 0$, and $\kappa_0, \dots, \kappa_{K-1}$ such that for each $k < K$ every
    $2^k r_0$-separated subfamily inside a closed $2^{k+1} r_0$-ball centred at a point of the
    family has at most $\kappa_k$ elements. Then
    $N_u(2^K r_0) \le \bigl(\prod_{k<K} \kappa_k\bigr) N_u(r_0)$. -/)] -/
theorem ballCount_pow_le [Fintype ι] [Nonempty ι] (u : ι → X) {r₀ : ℝ} (hr₀ : 0 < r₀) (K : ℕ)
    (κ : ℕ → ℝ)
    (hpack : ∀ k < K, ∀ t, ∀ J : Finset ι, (∀ j ∈ J, dist (u j) (u t) ≤ 2 ^ (k + 1) * r₀) →
      (∀ j ∈ J, ∀ l ∈ J, j ≠ l → 2 ^ k * r₀ ≤ dist (u j) (u l)) → (J.card : ℝ) ≤ κ k) :
    (ballCount u (2 ^ K * r₀) : ℝ) ≤ (∏ k ∈ Finset.range K, κ k) * ballCount u r₀ := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ih' := ih fun k hk => hpack k (by omega)
    have hκ : 0 ≤ κ K := by
      obtain ⟨t⟩ := ‹Nonempty ι›
      have := hpack K (Nat.lt_succ_self K) t ∅ (by simp) (by simp)
      simpa using this
    have e : (2 : ℝ) ^ (K + 1) * r₀ = 2 * (2 ^ K * r₀) := by ring
    have hstep := ballCount_two_mul_le u (r := 2 ^ K * r₀) (by positivity) (K := κ K)
      fun t J h1 h2 => hpack K (Nat.lt_succ_self K) t J (fun j hj => by rw [e]; exact h1 j hj) h2
    rw [e, Finset.prod_range_succ]
    calc (ballCount u (2 * (2 ^ K * r₀)) : ℝ) ≤ κ K * ballCount u (2 ^ K * r₀) := hstep
      _ ≤ κ K * ((∏ k ∈ Finset.range K, κ k) * ballCount u r₀) :=
          mul_le_mul_of_nonneg_left ih' hκ
      _ = (∏ k ∈ Finset.range K, κ k) * κ K * ballCount u r₀ := by ring

/- @[blueprint "lem:separated-net-counting"
  (statement := /-- \textbf{Multiscale counting lemma} (skeleton of ULB p.~186--187 / blueprint
    S11). Let $u : I \to X$ be a finite nonempty family in a pseudo-metric space which is
    $a$-separated ($d(u_j,u_l) \ge a$ for $j \ne l$), let $0 < r_0 < a$, $K \in \mathbb N$ with
    $d(u_j, u_l) \le 2^K r_0$ for all $j, l$, and let $\kappa_0,\dots,\kappa_{K-1}$ be such that
    for each $k < K$, every $2^k r_0$-separated subfamily contained in a closed $2^{k+1}r_0$-ball
    centred at a point of the family has at most $\kappa_k$ elements. Then
    $$|I| \le \prod_{k < K} \kappa_k .$$
    (In S11: $r_0 = a/2$, $N_u(r_0) = 1$, $\kappa_k = e^{4^{1-k} C}$ with
    $C = L_2^2 b(u)^2/a^2$ supplied by the subset-selection lemma B9, and
    $\sum_{k<K} 4^{1-k} \le 16/3$, \texttt{lem:geom-sum-four-le}.) -/)] -/
theorem card_le_prod_of_separated [Fintype ι] [Nonempty ι] (u : ι → X) {a r₀ : ℝ} (hr₀ : 0 < r₀)
    (hra : r₀ < a) (hsep : ∀ j l, j ≠ l → a ≤ dist (u j) (u l)) (K : ℕ) (κ : ℕ → ℝ)
    (hpack : ∀ k < K, ∀ t, ∀ J : Finset ι, (∀ j ∈ J, dist (u j) (u t) ≤ 2 ^ (k + 1) * r₀) →
      (∀ j ∈ J, ∀ l ∈ J, j ≠ l → 2 ^ k * r₀ ≤ dist (u j) (u l)) → (J.card : ℝ) ≤ κ k)
    (hdiam : ∀ j l, dist (u j) (u l) ≤ 2 ^ K * r₀) :
    (Fintype.card ι : ℝ) ≤ ∏ k ∈ Finset.range K, κ k := by
  have hκ : ∀ k ∈ Finset.range K, 0 ≤ κ k := fun k hk => by
    obtain ⟨t⟩ := ‹Nonempty ι›
    have := hpack k (Finset.mem_range.mp hk) t ∅ (by simp) (by simp)
    simpa using this
  have hprod : 0 ≤ ∏ k ∈ Finset.range K, κ k := Finset.prod_nonneg hκ
  calc (Fintype.card ι : ℝ) ≤ ballCount u (2 ^ K * r₀) := by
        exact_mod_cast card_le_ballCount u hdiam
    _ ≤ (∏ k ∈ Finset.range K, κ k) * ballCount u r₀ := ballCount_pow_le u hr₀ K κ hpack
    _ ≤ (∏ k ∈ Finset.range K, κ k) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hprod
        exact_mod_cast ballCount_le_one_of_separated u hra hsep
    _ = ∏ k ∈ Finset.range K, κ k := mul_one _

end Counting

/-! ### Elementary facts for B11 -/

/- @[blueprint "lem:geom-sum-four-le"
  (statement := /-- $\sum_{k < K} 4 \cdot 4^{-k} \le 16/3$ (the series $\sum_{k \ge 1} 4^{2-k}$
    of S11). -/)] -/
theorem geom_sum_four_le (K : ℕ) : ∑ k ∈ Finset.range K, (4 : ℝ) * (1 / 4) ^ k ≤ 16 / 3 := by
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  have h : (0 : ℝ) ≤ (1 / 4) ^ K := by positivity
  rw [show ((1 / 4 : ℝ) ^ K - 1) / (1 / 4 - 1) = (1 - (1 / 4) ^ K) * (4 / 3) by ring]
  nlinarith

/- @[blueprint "lem:log-two-le"
  (statement := /-- For an integer $N \ge 2$, $\log(N+1) \le 2\log N$, i.e.
    $\log N \ge \frac12 \log(N+1)$ (since $N^2 \ge N + 1$). -/)] -/
theorem log_add_one_le_two_mul_log {N : ℕ} (hN : 2 ≤ N) :
    Real.log ((N : ℝ) + 1) ≤ 2 * Real.log N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [show (2 : ℝ) * Real.log N = Real.log ((N : ℝ) ^ 2) by
    rw [Real.log_pow]; push_cast; ring]
  apply Real.log_le_log (by positivity)
  nlinarith

/- @[blueprint "lem:euclidean-dist-eq"
  (statement := /-- For $x, y \in \mathbb R^n$ viewed in the Euclidean space
    $\ell^2(\{1,\dots,n\})$, $d(x, y) = \bigl(\sum_i (x_i - y_i)^2\bigr)^{1/2}$: the metric in
    which the separation hypothesis of \texttt{thm:bernoulli-sudakov} is stated. -/)] -/
theorem dist_toLp_two_eq_sqrt_sum (x y : Fin n → ℝ) :
    dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) =
      Real.sqrt (∑ i, (x i - y i) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Real.dist_eq, sq_abs]

end FoML.ToFoML
