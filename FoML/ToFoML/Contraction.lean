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

/-!
# Rademacher contraction for arbitrary (infinite) hypothesis types

FoML proves the Rademacher contraction inequalities only for *finite* hypothesis types
(`empiricalRademacherComplexity_without_abs_contraction_finite`, constant `L`, and
`empiricalRademacherComplexity_contraction_finite`, constant `2L`). This file removes the
finiteness assumption by finite approximation of the suprema: since the Rademacher average is a
finite average over the `2^n` sign patterns, for every `ε > 0` there is a finite index set `T`
(one near-maximizer per sign pattern) such that the empirical Rademacher functional of the whole
class is at most the one of the class restricted to `T` plus `ε`; restriction can only decrease
the functional. Applying the finite contraction to `T` and letting `ε → 0` gives the general
statement.

Main results:
* `empiricalRademacherComplexity_without_abs_contraction`: one-sided contraction, constant `L`,
  `ψ` need not vanish at `0`;
* `empiricalRademacherComplexity_contraction`: absolute contraction, constant `2L`, `ψ x 0 = 0`.

Both are stated for an arbitrary nonempty index type with a uniform bound on the class.
This file depends only on Mathlib and FoML.
-/

open Real
open scoped BigOperators

namespace FoML.ToFoML

variable {H 𝒳 : Type*} {n : ℕ}

/- The sign type is nonempty. -/
instance instNonemptySigns : Nonempty (Signs n) := ⟨fun _ => ⟨1, by simp⟩⟩

/- @[blueprint "lem:abs-normalized-rademacher-sum-le"
  (statement := /-- $\bigl|\tfrac1n \sum_k \sigma_k F_h(x_k)\bigr|
    \le \tfrac1n \sum_k |F_h(x_k)|$. -/)] -/
theorem abs_normalizedRademacherSum_le (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) (σ : Signs n) (h : H) :
    |normalizedRademacherSum n F S σ h| ≤ (n : ℝ)⁻¹ * ∑ k, |F h (S k)| := by
  unfold normalizedRademacherSum
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [abs_mul, abs_sigma, one_mul]

/- @[blueprint "lem:abs-normalized-rademacher-sum-le-of-bound"
  (statement := /-- If $|F_h(x_k)| \le b$ for all $h, k$ (with $b \ge 0$) then
    $\bigl|\tfrac1n \sum_k \sigma_k F_h(x_k)\bigr| \le b$. -/)] -/
theorem abs_normalizedRademacherSum_le_of_bound (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) {b : ℝ}
    (hb : 0 ≤ b) (hF : ∀ h k, |F h (S k)| ≤ b) (σ : Signs n) (h : H) :
    |normalizedRademacherSum n F S σ h| ≤ b := by
  refine (abs_normalizedRademacherSum_le F S σ h).trans ?_
  calc (n : ℝ)⁻¹ * ∑ k, |F h (S k)| ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b := by
        gcongr with k; exact hF h k
    _ = (n : ℝ)⁻¹ * (n * b) := by simp
    _ ≤ b := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simpa using hb
        · rw [inv_mul_cancel_left₀ (by exact_mod_cast hn.ne')]

/- Bounded ranges of the (post-processed) Rademacher sums from a uniform bound on the class. -/
theorem bddAbove_range_normalizedRademacherSum_of_bound (φ : ℝ → ℝ) (hφ : ∀ u, |φ u| ≤ |u| ∨ φ = id)
    (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) {b : ℝ} (hb : 0 ≤ b) (hF : ∀ h k, |F h (S k)| ≤ b)
    (σ : Signs n) :
    BddAbove (Set.range fun h => φ (normalizedRademacherSum n F S σ h)) := by
  refine ⟨b, ?_⟩
  rintro _ ⟨h, rfl⟩
  have hs := abs_normalizedRademacherSum_le_of_bound F S hb hF σ h
  rcases hφ (normalizedRademacherSum n F S σ h) with h1 | h1
  · exact (le_abs_self _).trans (h1.trans hs)
  · rw [h1]; exact (le_abs_self _).trans hs

section Approximation

/- Restricting a class to a nonempty finite index set can only decrease the empirical Rademacher
functional (for any post-processing `φ`), provided the ranges are bounded above. -/
theorem empiricalRademacherFunctional_restrict_le (φ : ℝ → ℝ) (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (T : Finset H) (hT : T.Nonempty)
    (hbdd : ∀ σ : Signs n, BddAbove (Set.range fun h => φ (normalizedRademacherSum n F S σ h))) :
    empiricalRademacherFunctional n φ (fun t : T => F t) S ≤
      empiricalRademacherFunctional n φ F S := by
  haveI : Nonempty T := hT.to_subtype
  unfold empiricalRademacherFunctional
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
  exact ciSup_le fun t => le_ciSup (hbdd σ) (t : H)

/- @[blueprint "lem:rademacher-finite-approximation"
  (statement := /-- Let $F = (F_h)_{h \in H}$ be a class indexed by a nonempty set, $\varphi$ a
    post-processing map and assume the sets $\{\varphi(\tfrac1n\sum_k \sigma_k F_h(x_k)) : h\}$
    are bounded above for every sign pattern $\sigma$. Then for every $\varepsilon > 0$ there is a
    nonempty finite $T \subseteq H$ with
    $\mathbb E_\sigma \sup_{h \in H} \varphi(\cdot) \le
    \mathbb E_\sigma \sup_{h \in T} \varphi(\cdot) + \varepsilon$
    (take one $\varepsilon$-near-maximizer for each of the finitely many $\sigma$). -/)] -/
theorem exists_finset_empiricalRademacherFunctional_le [Nonempty H] (φ : ℝ → ℝ) (F : H → 𝒳 → ℝ)
    (S : Fin n → 𝒳) {ε : ℝ} (hε : 0 < ε)
    (hbdd : ∀ σ : Signs n, BddAbove (Set.range fun h => φ (normalizedRademacherSum n F S σ h))) :
    ∃ T : Finset H, T.Nonempty ∧
      empiricalRademacherFunctional n φ F S ≤
        empiricalRademacherFunctional n φ (fun t : T => F t) S + ε := by
  classical
  have hex : ∀ σ : Signs n, ∃ h : H,
      (⨆ h, φ (normalizedRademacherSum n F S σ h)) - ε < φ (normalizedRademacherSum n F S σ h) :=
    fun σ => exists_lt_of_lt_ciSup (by linarith)
  choose hσ hhσ using hex
  refine ⟨Finset.univ.image hσ, Finset.image_nonempty.mpr Finset.univ_nonempty, ?_⟩
  set T := Finset.univ.image hσ with hTdef
  haveI : Nonempty T := (Finset.image_nonempty.mpr Finset.univ_nonempty).to_subtype
  have hstep : ∀ σ : Signs n, (⨆ h, φ (normalizedRademacherSum n F S σ h)) ≤
      (⨆ t : T, φ (normalizedRademacherSum n F S σ t)) + ε := by
    intro σ
    have hmem : hσ σ ∈ T := Finset.mem_image_of_mem hσ (Finset.mem_univ σ)
    have hbT : BddAbove (Set.range fun t : T => φ (normalizedRademacherSum n F S σ t)) :=
      (hbdd σ).mono (Set.range_comp_subset_range (Subtype.val : T → H)
        fun h => φ (normalizedRademacherSum n F S σ h))
    have := le_ciSup hbT ⟨hσ σ, hmem⟩
    linarith [hhσ σ]
  unfold empiricalRademacherFunctional
  calc (Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ, ⨆ h, φ (normalizedRademacherSum n F S σ h)
      ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ, ((⨆ t : T, φ (normalizedRademacherSum n F S σ t)) + ε) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hstep σ) (by positivity)
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ, (⨆ t : T, φ (normalizedRademacherSum n F S σ t)) + ε := by
        rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          inv_mul_cancel_left₀ (by positivity)]
    _ = _ := rfl

end Approximation

section Contraction

/- @[blueprint "lem:contraction-without-abs"
  (statement := /-- \textbf{One-sided Rademacher contraction (general index type).}
    Let $H$ be nonempty, $F = (F_h)_{h\in H}$ with $|F_h(x_k)| \le b$ on the sample, $L \ge 0$, and
    let $\psi : \mathcal X \times \mathbb R \to \mathbb R$ satisfy
    $|\psi(x,u) - \psi(x,v)| \le L |u - v|$. Then
    $\mathbb E_\sigma \sup_h \tfrac1n \sum_k \sigma_k \psi(x_k, F_h(x_k))
    \le L\, \mathbb E_\sigma \sup_h \tfrac1n \sum_k \sigma_k F_h(x_k)$.
    ($\psi(x,0) = 0$ is not needed for the one-sided version.) -/)] -/
theorem empiricalRademacherComplexity_without_abs_contraction [Nonempty H] (n : ℕ)
    (F : H → 𝒳 → ℝ) (ψ : 𝒳 → ℝ → ℝ) (S : Fin n → 𝒳) {L b : ℝ} (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hF : ∀ h k, |F h (S k)| ≤ b) (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ L * |u - v|) :
    empiricalRademacherComplexity_without_abs n (fun h x => ψ x (F h x)) S ≤
      L * empiricalRademacherComplexity_without_abs n F S := by
  /- Fix $\varepsilon > 0$ and a finite $T$ with $R(\psi \circ F) \le R(\psi\circ F|_T) +
    \varepsilon$. By the finite contraction $R(\psi \circ F|_T) \le L R(F|_T) \le L R(F)$. -/
  set G : H → 𝒳 → ℝ := fun h x => ψ x (F h x) with hG
  have hGb : ∀ h k, |G h (S k)| ≤ L * b + ⨆ k : Fin n, |ψ (S k) 0| := by
    intro h k
    have h1 : |ψ (S k) (F h (S k))| ≤ |ψ (S k) (F h (S k)) - ψ (S k) 0| + |ψ (S k) 0| := by
      have := abs_sub_abs_le_abs_sub (ψ (S k) (F h (S k))) (ψ (S k) 0)
      linarith
    have h2 : |ψ (S k) (F h (S k)) - ψ (S k) 0| ≤ L * b := by
      refine (hψ _ _ _).trans ?_
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left (hF h k) hL
    have h3 : |ψ (S k) 0| ≤ ⨆ k : Fin n, |ψ (S k) 0| :=
      le_ciSup (f := fun k : Fin n => |ψ (S k) 0|) (Set.finite_range _).bddAbove k
    change |ψ (S k) (F h (S k))| ≤ _
    linarith
  have hGb0 : 0 ≤ L * b + ⨆ k : Fin n, |ψ (S k) 0| :=
    add_nonneg (mul_nonneg hL hb) (Real.iSup_nonneg fun _ => abs_nonneg _)
  have hbddG : ∀ σ : Signs n,
      BddAbove (Set.range fun h => id (normalizedRademacherSum n G S σ h)) :=
    bddAbove_range_normalizedRademacherSum_of_bound id (fun _ => Or.inr rfl) G S hGb0 hGb
  have hbddF : ∀ σ : Signs n,
      BddAbove (Set.range fun h => id (normalizedRademacherSum n F S σ h)) :=
    bddAbove_range_normalizedRademacherSum_of_bound id (fun _ => Or.inr rfl) F S hb hF
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨T, hT, hle⟩ := exists_finset_empiricalRademacherFunctional_le id G S hε hbddG
  haveI : Nonempty T := hT.to_subtype
  have hfin := empiricalRademacherComplexity_without_abs_contraction_finite n (fun t : T => F t)
    ψ S hL hψ
  have hres := empiricalRademacherFunctional_restrict_le id F S T hT hbddF
  simp only [empiricalRademacherFunctional_id] at hle hres
  calc empiricalRademacherComplexity_without_abs n G S
      ≤ empiricalRademacherComplexity_without_abs n (fun t : T => G t) S + ε := hle
    _ ≤ L * empiricalRademacherComplexity_without_abs n (fun t : T => F t) S + ε := by
        gcongr
    _ ≤ L * empiricalRademacherComplexity_without_abs n F S + ε := by
        gcongr

/- @[blueprint "lem:contraction"
  (statement := /-- \textbf{Rademacher contraction (absolute version, general index type).}
    Let $H$ be nonempty, $F = (F_h)_{h\in H}$ with $|F_h(x_k)| \le b$ on the sample, $L \ge 0$, and
    let $\psi : \mathcal X \times \mathbb R \to \mathbb R$ satisfy $\psi(x, 0) = 0$ and
    $|\psi(x,u) - \psi(x,v)| \le L |u - v|$. Then
    $\mathbb E_\sigma \sup_h \bigl|\tfrac1n \sum_k \sigma_k \psi(x_k, F_h(x_k))\bigr|
    \le 2L\, \mathbb E_\sigma \sup_h \bigl|\tfrac1n \sum_k \sigma_k F_h(x_k)\bigr|$.
    This extends FoML's finite-class contraction
    \texttt{empiricalRademacherComplexity\_contraction\_finite} to arbitrary classes. -/)] -/
theorem empiricalRademacherComplexity_contraction [Nonempty H] (n : ℕ)
    (F : H → 𝒳 → ℝ) (ψ : 𝒳 → ℝ → ℝ) (S : Fin n → 𝒳) {L b : ℝ} (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hF : ∀ h k, |F h (S k)| ≤ b) (hψ_zero : ∀ x, ψ x 0 = 0)
    (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ L * |u - v|) :
    empiricalRademacherComplexity n (fun h x => ψ x (F h x)) S ≤
      2 * L * empiricalRademacherComplexity n F S := by
  set G : H → 𝒳 → ℝ := fun h x => ψ x (F h x) with hG
  have hGb : ∀ h k, |G h (S k)| ≤ L * b := by
    intro h k
    have := hψ (S k) (F h (S k)) 0
    rw [hψ_zero, sub_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hF h k) hL)
  have hbddG : ∀ σ : Signs n,
      BddAbove (Set.range fun h => abs (normalizedRademacherSum n G S σ h)) :=
    bddAbove_range_normalizedRademacherSum_of_bound abs (fun u => Or.inl (le_of_eq (abs_abs u)))
      G S (mul_nonneg hL hb) hGb
  have hbddF : ∀ σ : Signs n,
      BddAbove (Set.range fun h => abs (normalizedRademacherSum n F S σ h)) :=
    bddAbove_range_normalizedRademacherSum_of_bound abs (fun u => Or.inl (le_of_eq (abs_abs u)))
      F S hb hF
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨T, hT, hle⟩ := exists_finset_empiricalRademacherFunctional_le abs G S hε hbddG
  haveI : Nonempty T := hT.to_subtype
  have hfin := empiricalRademacherComplexity_contraction_finite n (fun t : T => F t)
    ψ S hL hψ_zero hψ
  have hres := empiricalRademacherFunctional_restrict_le abs F S T hT hbddF
  simp only [empiricalRademacherFunctional_abs] at hle hres
  calc empiricalRademacherComplexity n G S
      ≤ empiricalRademacherComplexity n (fun t : T => G t) S + ε := hle
    _ ≤ 2 * L * empiricalRademacherComplexity n (fun t : T => F t) S + ε := by
        gcongr
    _ ≤ 2 * L * empiricalRademacherComplexity n F S + ε := by
        gcongr

end Contraction

end FoML.ToFoML
