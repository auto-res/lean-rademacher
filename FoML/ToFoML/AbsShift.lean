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
import FoML.ToFoML.Contraction

/-!
# Absolute vs. one-sided empirical Rademacher complexity: shifting by a member

FoML's high-probability uniform-deviation bounds are stated with the *absolute* empirical
Rademacher complexity `empiricalRademacherComplexity` (`𝔼_σ sup_h |n⁻¹ ∑ σ_k G_h(z_k)|`), while
the paper's complexity is the one-sided `empiricalRademacherComplexity_without_abs`
(`𝔼_σ sup_h n⁻¹ ∑ σ_k G_h(z_k)`). For a class which is not closed under negation the absolute
version can be strictly larger (for a singleton `{g}` the one-sided complexity is `0` and the
absolute one is `𝔼_σ |n⁻¹ ∑ σ_k g(z_k)|`).

The general comparison proved here: for any member `g₀ = G i₀` of the class,

`R̂^abs(G) ≤ R̂(G - g₀) + R̂(g₀ - G) + R̂^abs({g₀})`,

and, by Massart's lemma (FoML `massart_lemma_pmf`) applied to the two-element class `{g₀, -g₀}`,
`R̂^abs({g₀}) ≤ b √(2 log 2 / n)` when `|g₀| ≤ b` on the sample. The two one-sided terms are then
amenable to the one-sided contraction inequality (constant `L`, no vanishing condition).
This file depends only on Mathlib and FoML.
-/

open Real
open scoped BigOperators

namespace FoML.ToFoML

variable {ι 𝒳 : Type*} {n : ℕ}

/- @[blueprint "lem:ciSup-abs-le-shift"
  (statement := /-- For a bounded family $(a_i)_{i \in I}$ of reals ($I \ne \emptyset$) and any
    $i_0 \in I$: $\sup_i |a_i| \le \sup_i (a_i - a_{i_0}) + \sup_i (a_{i_0} - a_i) + |a_{i_0}|$.
    (Both suprema on the right are $\ge 0$ since they vanish at $i = i_0$.) -/)] -/
theorem ciSup_abs_le_ciSup_sub_add_ciSup_sub_add [Nonempty ι] (a : ι → ℝ) {C : ℝ}
    (hC : ∀ i, |a i| ≤ C) (i₀ : ι) :
    (⨆ i, |a i|) ≤ (⨆ i, (a i - a i₀)) + (⨆ i, (a i₀ - a i)) + |a i₀| := by
  have hb1 : BddAbove (Set.range fun i => a i - a i₀) :=
    ⟨C + C, by rintro _ ⟨i, rfl⟩; linarith [hC i, hC i₀, le_abs_self (a i), neg_abs_le (a i₀)]⟩
  have hb2 : BddAbove (Set.range fun i => a i₀ - a i) :=
    ⟨C + C, by rintro _ ⟨i, rfl⟩; linarith [hC i, hC i₀, le_abs_self (a i₀), neg_abs_le (a i)]⟩
  have h1 : 0 ≤ ⨆ i, (a i - a i₀) := by
    have := le_ciSup hb1 i₀; simpa using this
  have h2 : 0 ≤ ⨆ i, (a i₀ - a i) := by
    have := le_ciSup hb2 i₀; simpa using this
  refine ciSup_le fun i => ?_
  have hi1 : a i - a i₀ ≤ ⨆ i, (a i - a i₀) := le_ciSup hb1 i
  have hi2 : a i₀ - a i ≤ ⨆ i, (a i₀ - a i) := le_ciSup hb2 i
  have htri : |a i| - |a i₀| ≤ |a i - a i₀| := abs_sub_abs_le_abs_sub _ _
  have h3 : |a i - a i₀| ≤ (⨆ i, (a i - a i₀)) + (⨆ i, (a i₀ - a i)) :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  linarith

/- @[blueprint "lem:rademacher-abs-le-shift"
  (statement := /-- Let $G = (G_i)_{i\in I}$ be a class with $|G_i(z_k)| \le C$ on the sample,
    $I \ne \emptyset$, and fix $i_0 \in I$, $g_0 := G_{i_0}$. Then
    $$\hat{\mathfrak R}^{\mathrm{abs}}_S(G) \le \hat{\mathfrak R}_S(G - g_0)
    + \hat{\mathfrak R}_S(g_0 - G) + \hat{\mathfrak R}^{\mathrm{abs}}_S(\{g_0\}),$$
    where $\hat{\mathfrak R}$ is the one-sided (no absolute value) complexity and
    $G - g_0 = \{G_i - g_0 : i \in I\}$. -/)] -/
theorem empiricalRademacherComplexity_le_shift [Nonempty ι] (n : ℕ) (G : ι → 𝒳 → ℝ)
    (S : Fin n → 𝒳) (i₀ : ι) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i k, |G i (S k)| ≤ C) :
    empiricalRademacherComplexity n G S ≤
      empiricalRademacherComplexity_without_abs n (fun i x => G i x - G i₀ x) S
        + empiricalRademacherComplexity_without_abs n (fun i x => G i₀ x - G i x) S
        + empiricalRademacherComplexity n (fun _ : Unit => G i₀) S := by
  /- Apply \texttt{lem:ciSup-abs-le-shift} for each sign pattern $\sigma$ to
    $a_i = \frac1n\sum_k \sigma_k G_i(z_k)$ and average. -/
  have hstep : ∀ σ : Signs n,
      (⨆ i, |(n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * G i (S k)|) ≤
        (⨆ i, (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * (G i (S k) - G i₀ (S k)))
          + (⨆ i, (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * (G i₀ (S k) - G i (S k)))
          + ⨆ _ : Unit, |(n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * G i₀ (S k)| := by
    intro σ
    have hbd : ∀ i, |(n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * G i (S k)| ≤ C := fun i =>
      abs_normalizedRademacherSum_le_of_bound G S hC0 hC σ i
    have := ciSup_abs_le_ciSup_sub_add_ciSup_sub_add
      (fun i => (n : ℝ)⁻¹ * ∑ k, (σ k : ℝ) * G i (S k)) hbd i₀
    simp only [mul_sub, Finset.sum_sub_distrib, ciSup_const]
    simpa [mul_sub, Finset.sum_sub_distrib] using this
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hstep σ) (by positivity)

/- @[blueprint "lem:rademacher-singleton-abs"
  (statement := /-- \textbf{Absolute Rademacher complexity of a single function.} If $n \ge 1$,
    $b \ge 0$ and $|g(z_k)| \le b$ for all $k$, then
    $\mathbb E_\sigma \bigl|\tfrac1n \sum_k \sigma_k g(z_k)\bigr| \le b \sqrt{2 \log 2 / n}$
    (Massart's lemma for the two-element class $\{g, -g\}$). -/)] -/
theorem empiricalRademacherComplexity_singleton_le (n : ℕ) (hn : 0 < n) (g : 𝒳 → ℝ)
    (S : Fin n → 𝒳) {b : ℝ} (hb : 0 ≤ b) (hg : ∀ k, |g (S k)| ≤ b) :
    empiricalRademacherComplexity n (fun _ : Unit => g) S ≤ b * Real.sqrt (2 * Real.log 2 / n) := by
  classical
  set F : Unit × Bool → 𝒳 → ℝ := signSymmetrization (fun _ : Unit => g) with hF
  have hFb : ∀ i k, |F i (S k)| ≤ b := by
    rintro ⟨u, b'⟩ k
    cases b' <;> simp [F, signSymmetrization, hg k]
  -- absolute complexity of `{g}` = one-sided complexity of `{g, -g}`
  have h1 : empiricalRademacherComplexity n (fun _ : Unit => g) S =
      empiricalRademacherComplexity_without_abs n F S :=
    empiricalRademacherComplexity_eq_without_abs_signSymmetrization n (fun _ : Unit => g) S b hb
      fun _ k => hg k
  -- reindex by the (surjective) inclusion of `Finset.univ`
  have h2 : empiricalRademacherComplexity_without_abs n F S =
      empiricalRademacherComplexity_without_abs n
        (ProbabilityTheory.F_on F Finset.univ) S := by
    rw [← empiricalRademacherComplexity_without_abs_reindex_eq_of_surjective F
      (fun j : {j // j ∈ (Finset.univ : Finset (Unit × Bool))} => j.1)
      (fun i => ⟨⟨i, Finset.mem_univ i⟩, rfl⟩) S]
    rfl
  have hne : (Finset.univ : Finset (Unit × Bool)).Nonempty := Finset.univ_nonempty
  have h3 := ProbabilityTheory.massart_lemma_pmf F S Finset.univ hne hn b fun i _ k => hFb i k
  rw [← empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs]
    at h3
  have hcard : ((Finset.univ : Finset (Unit × Bool)).card : ℝ) = 2 := by
    simp [Finset.card_univ]
  rw [hcard] at h3
  have hsup : (Finset.univ.sup' hne fun j : Unit × Bool =>
      Real.sqrt (∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2)) ≤ b / Real.sqrt n := by
    refine Finset.sup'_le hne _ fun j _ => ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc Real.sqrt (∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2)
        ≤ Real.sqrt (∑ _i : Fin n, ((n : ℝ)⁻¹ * b) ^ 2) := by
          gcongr with i
          exact hFb j i
      _ = Real.sqrt (b ^ 2 / n) := by
          congr 1
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ = b / Real.sqrt n := by
          rw [Real.sqrt_div (sq_nonneg b), Real.sqrt_sq hb]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc empiricalRademacherComplexity n (fun _ : Unit => g) S
      = empiricalRademacherComplexity_without_abs n
          (ProbabilityTheory.F_on F Finset.univ) S := h1.trans h2
    _ ≤ (Finset.univ.sup' hne fun j : Unit × Bool =>
          Real.sqrt (∑ i : Fin n, ((n : ℝ)⁻¹ * |F j (S i)|) ^ 2)) * Real.sqrt (2 * Real.log 2) :=
        h3
    _ ≤ (b / Real.sqrt n) * Real.sqrt (2 * Real.log 2) :=
        mul_le_mul_of_nonneg_right hsup (Real.sqrt_nonneg _)
    _ = b * Real.sqrt (2 * Real.log 2 / n) := by
        rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.log 2)]
        ring

end FoML.ToFoML
