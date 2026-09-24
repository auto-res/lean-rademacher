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
import FoML.ToMathlib.IntervalIntegral
import FoML.ToMathlib.CoveringNumber

/-!
# Dudley's entropy integral for sub-Gaussian processes on a finite probability space

FoML proves Dudley's entropy-integral bound only for Rademacher averages of function classes
(`dudley_entropy_integral'`). The hidden–output decomposition of the paper needs the generic
chaining bound for an *arbitrary* process `(Y_t)_{t ∈ F}` on the finite uniform probability space
`Ω` (in the application `Ω = Signs n`) with sub-Gaussian increments (in the tail sense) with
respect to a pseudometric on the index set, anchored at a point `t₀ ∈ F` with `Y t₀ = 0`:

`𝔼 sup_{t ∈ F} Y_t ≤ 12 σ ∫_0^{diam F} √(log N(F, d, ε)) dε`,

where `N` is Mathlib's internal covering number (closed balls, centres in `F`) and the integral is
Lean's (Bochner) interval integral; since the latter is `0` for non-integrable integrands, the
integrability of `ε ↦ √(log N(F, d, ε))` on `[0, diam F]` is an explicit hypothesis.

The proof is the classical chaining argument (dyadic scales `ε_k = diam F / 2^k`, nested nets,
telescoping, a maximal inequality for finitely many sub-Gaussian variables), with two features
specific to the finite probability space:

* the tail bound forces a *sure* Lipschitz bound `|Y_s − Y_t| ≤ σ d(s,t) √(2 log(2|Ω|))`
  (`lem:sg-tail-lipschitz-finite`), which kills the residual term of the chain as the finest scale
  tends to `0`;
* the maximal inequality is derived from tail bounds by integrating the tail (layer cake for a
  finite sum, `lem:emax-of-tail`): `𝔼 max_{i ≤ M} |ξ_i| ≤ τ (√(2 log(2M)) + 1/√(2 log(2M)))`.

The Mathlib-generic integral facts (layer cake for a finite sum `sum_eq_integral_card_lt`, the
Gaussian tail integral `integral_exp_neg_sq_le`, `mul_le_integral_of_forall_Ico`) live in
`FoML.ToMathlib.IntervalIntegral`, and the finiteness of the covering numbers of a
totally bounded set (`coveringNumber_ne_top_of_totallyBounded`) in
`FoML.ToMathlib.CoveringNumber`. This file depends only on Mathlib, FoML and
`FoML.ToMathlib`.
-/

open scoped NNReal ENNReal BigOperators
open Metric MeasureTheory Real

open FoML.ToMathlib

namespace FoML.ToFoML

section FiniteSpace

variable {Ω : Type*} [Fintype Ω]

/- @[blueprint "def:uniform-expect"
  (statement := /-- For a finite set $\Omega$ and $g : \Omega \to \mathbb R$, the expectation
    under the uniform distribution is $\mathbb E g = |\Omega|^{-1} \sum_{\omega} g(\omega)$. -/)] -/
noncomputable def uniformExpect (g : Ω → ℝ) : ℝ := (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, g ω

/- @[blueprint "def:tail-frac"
  (statement := /-- For $Z : \Omega \to \mathbb R$ and $u \in \mathbb R$, the tail probability
    under the uniform distribution: $\mathbb P(|Z| > u) = |\{\omega : |Z(\omega)| > u\}| /
    |\Omega|$. -/)] -/
noncomputable def tailFrac (Z : Ω → ℝ) (u : ℝ) : ℝ :=
  ((Finset.univ.filter fun ω => u < |Z ω|).card : ℝ) / Fintype.card Ω

/- @[blueprint "lem:tail-frac-nonneg"
  (statement := /-- $\mathbb P(|Z| > u) \ge 0$. -/)] -/
theorem tailFrac_nonneg (Z : Ω → ℝ) (u : ℝ) : 0 ≤ tailFrac Z u := by
  unfold tailFrac; positivity

/- @[blueprint "lem:uniform-expect-mono"
  (statement := /-- If $g \le h$ pointwise then $\mathbb E g \le \mathbb E h$. -/)] -/
theorem uniformExpect_mono {g h : Ω → ℝ} (hgh : ∀ ω, g ω ≤ h ω) :
    uniformExpect g ≤ uniformExpect h := by
  unfold uniformExpect
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => hgh ω) (by positivity)

/- @[blueprint "lem:uniform-expect-const-add-sum"
  (statement := /-- $\mathbb E\bigl[a + \sum_{j \in J} g_j\bigr] = a + \sum_{j \in J}
    \mathbb E g_j$ for a nonempty finite $\Omega$. -/)] -/
theorem uniformExpect_const_add_sum [Nonempty Ω] {J : Type*} (s : Finset J) (a : ℝ)
    (g : J → Ω → ℝ) :
    uniformExpect (fun ω => a + ∑ j ∈ s, g j ω) = a + ∑ j ∈ s, uniformExpect (g j) := by
  unfold uniformExpect
  have hm : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    inv_mul_cancel_left₀ hm, Finset.sum_comm, Finset.mul_sum]

/- @[blueprint "lem:sg-tail-lipschitz-finite"
  (statement := /-- \textbf{Sub-Gaussian tails on a finite space give a sure bound.} Let
    $\Omega$ be finite and nonempty with the uniform distribution, $\tau > 0$, and let
    $Z : \Omega \to \mathbb R$ satisfy $\mathbb P(|Z| > u) \le 2 \exp(-u^2/(2\tau^2))$ for all
    $u > 0$. Then $|Z(\omega)| \le \tau \sqrt{2 \log(2|\Omega|)}$ for \emph{every} $\omega$
    (every atom has probability $1/|\Omega|$, which the tail bound cannot accommodate beyond this
    level). -/)] -/
theorem abs_le_of_tailFrac_le [Nonempty Ω] (Z : Ω → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (htail : ∀ u : ℝ, 0 < u → tailFrac Z u ≤ 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2)))) (ω : Ω) :
    |Z ω| ≤ τ * Real.sqrt (2 * Real.log (2 * Fintype.card Ω)) := by
  set m : ℝ := (Fintype.card Ω : ℝ) with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; exact_mod_cast Fintype.card_pos
  have hlog : 0 < Real.log (2 * m) := Real.log_pos (by linarith)
  set c := τ * Real.sqrt (2 * Real.log (2 * m)) with hc
  have hc0 : 0 < c := by positivity
  by_contra hlt
  push Not at hlt
  set u := (c + |Z ω|) / 2 with hu
  have hu0 : 0 < u := by linarith
  have hcu : c < u := by linarith
  have hulZ : u < |Z ω| := by linarith
  have h1 : (1 : ℝ) / m ≤ tailFrac Z u := by
    unfold tailFrac
    rw [← hm]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have hmem : ω ∈ Finset.univ.filter (fun ω => u < |Z ω|) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hulZ
    exact_mod_cast Finset.card_pos.mpr ⟨ω, hmem⟩
  have hcsq : c ^ 2 = τ ^ 2 * (2 * Real.log (2 * m)) := by
    rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
  have hexp : Real.log (2 * m) < u ^ 2 / (2 * τ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have : c ^ 2 < u ^ 2 := by nlinarith
    nlinarith
  have h2 : 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2))) < 1 / m := by
    calc 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2))) < 2 * Real.exp (-(Real.log (2 * m))) := by
          gcongr
      _ = 1 / m := by
          rw [Real.exp_neg, Real.exp_log (by linarith)]
          field_simp
  linarith [htail u hu0]

end FiniteSpace

section Numeric

/- @[blueprint "lem:psi-le-three-sqrt-log"
  (statement := /-- \textbf{Numerical inequality for the maximal-inequality constant.} For every
    integer $M \ge 1$,
    $$\sqrt{2\log(2M)} + \frac{1}{\sqrt{2\log(2M)}} \le 3 \sqrt{\log \max(M, 2)}.$$
    (At $M = 1$: $2.03 \le 2.50$; for $M \ge 2$ it follows from $7 \log M \ge 7 \log 2 >
    2\log 2 + 2 + 1/(2\log 2)$ after squaring.) -/)] -/
theorem psi_le_three_sqrt_log (M : ℕ) (hM : 1 ≤ M) :
    Real.sqrt (2 * Real.log (2 * M)) + 1 / Real.sqrt (2 * Real.log (2 * M)) ≤
      3 * Real.sqrt (Real.log (max (M : ℝ) 2)) := by
  have hL := Real.log_two_gt_d9
  have hL' := Real.log_two_lt_d9
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set x := Real.log (max (M : ℝ) 2) with hx
  have hx2 : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (le_max_right _ _)
  have hlogM : Real.log M ≤ x := Real.log_le_log (by linarith) (le_max_left _ _)
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlog2M : Real.log (2 * M) = Real.log 2 + Real.log M :=
    Real.log_mul (by norm_num) (by positivity)
  have hy0 : 0 < 2 * Real.log (2 * M) := by rw [hlog2M]; linarith
  set y := Real.sqrt (2 * Real.log (2 * M)) with hy
  have hypos : 0 < y := Real.sqrt_pos.mpr hy0
  have hysq : y ^ 2 = 2 * Real.log (2 * M) := Real.sq_sqrt hy0.le
  have h3 : 3 * Real.sqrt x = Real.sqrt (9 * x) := by
    rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [h3, Real.le_sqrt (by positivity) (by linarith)]
  have hexp : (y + 1 / y) ^ 2 = y ^ 2 + 2 + 1 / y ^ 2 := by
    field_simp
    ring
  rw [hexp, hysq]
  have hinv : 1 / (2 * Real.log (2 * M)) ≤ 1 / (2 * Real.log 2) := by
    apply one_div_le_one_div_of_le (by linarith)
    rw [hlog2M]; linarith
  have hinv' : 1 / (2 * Real.log 2) ≤ 0.7214 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2M : 2 * Real.log (2 * M) ≤ 2 * Real.log 2 + 2 * x := by rw [hlog2M]; linarith
  linarith

end Numeric

section MaximalInequality

variable {Ω : Type*} [Fintype Ω]

/- @[blueprint "lem:emax-of-tail"
  (statement := /-- \textbf{Maximal inequality from tail bounds (finite space).} Let $\Omega$ be
    finite and nonempty with the uniform distribution, $\tau > 0$, $M \ge 1$ an integer, and let
    $(\xi_i)_{i \in s}$ be finitely many real random variables on $\Omega$ with $|s| \le M$ and
    $\mathbb P(|\xi_i| > u) \le 2\exp(-u^2/(2\tau^2))$ for all $i \in s$ and $u > 0$. Then
    $$\mathbb E \max_{i \in s} |\xi_i| \le
      \tau \Bigl(\sqrt{2\log(2M)} + \frac{1}{\sqrt{2\log(2M)}}\Bigr).$$
    Proof: with $a = \tau\sqrt{2\log(2M)}$, by the layer-cake formula and the union bound
    $\mathbb E \max_i |\xi_i| \le a + \int_a^\infty 2M e^{-u^2/(2\tau^2)}\,du
    \le a + 2M \frac{\tau^2}{a} e^{-a^2/(2\tau^2)} = a + \tau^2/a$. -/)] -/
theorem uniformExpect_sup'_abs_le_of_tail [Nonempty Ω] {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (ξ : ι → Ω → ℝ) {τ : ℝ} (hτ : 0 < τ) {M : ℕ} (hM : 1 ≤ M)
    (hsM : s.card ≤ M)
    (htail : ∀ i ∈ s, ∀ u : ℝ, 0 < u →
      tailFrac (ξ i) u ≤ 2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2)))) :
    uniformExpect (fun ω => s.sup' hs fun i => |ξ i ω|) ≤
      τ * (Real.sqrt (2 * Real.log (2 * M)) + 1 / Real.sqrt (2 * Real.log (2 * M))) := by
  classical
  set m : ℝ := (Fintype.card Ω : ℝ) with hm
  have hm0 : 0 < m := by rw [hm]; exact_mod_cast Fintype.card_pos
  set Mx : Ω → ℝ := fun ω => s.sup' hs fun i => |ξ i ω| with hMx
  have hMx0 : ∀ ω, 0 ≤ Mx ω := fun ω => by
    obtain ⟨i, hi⟩ := hs
    exact (abs_nonneg _).trans (Finset.le_sup' (fun i => |ξ i ω|) hi)
  obtain ⟨ω₀, -, hω₀⟩ := Finset.exists_max_image Finset.univ Mx Finset.univ_nonempty
  set R := Mx ω₀ with hR
  have hMxR : ∀ ω, Mx ω ≤ R := fun ω => hω₀ ω (Finset.mem_univ _)
  set g : ℝ → ℝ := fun u => ((Finset.univ.filter fun ω => u < Mx ω).card : ℝ) with hg
  have hsum : ∑ ω, Mx ω = ∫ u in (0 : ℝ)..R, g u := sum_eq_integral_card_lt Mx hMx0 hMxR
  have hg_anti : Antitone g := by
    intro u v huv
    simp only [hg]
    exact_mod_cast Finset.card_le_card (fun ω hω => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      linarith)
  have hg_le_m : ∀ u, g u ≤ m := fun u => by
    simp only [hg, hm]
    exact_mod_cast Finset.card_filter_le _ _
  have hg_tail : ∀ u, 0 < u → g u ≤ m * (2 * M) * Real.exp (-(u ^ 2 / (2 * τ ^ 2))) := by
    intro u hu
    have hsub : (Finset.univ.filter fun ω => u < Mx ω) ⊆
        s.biUnion fun i => Finset.univ.filter fun ω => u < |ξ i ω| := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      obtain ⟨i, hi, hiω⟩ := Finset.exists_mem_eq_sup' hs (fun i => |ξ i ω|)
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hi, by simpa only [hMx, hiω] using hω⟩
    calc g u ≤ ((s.biUnion fun i => Finset.univ.filter fun ω => u < |ξ i ω|).card : ℝ) := by
          simp only [hg]; exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ i ∈ s, ((Finset.univ.filter fun ω => u < |ξ i ω|).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ s, m * (2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2)))) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := htail i hi u hu
          unfold tailFrac at h
          rw [← hm, div_le_iff₀ hm0] at h
          linarith
      _ = s.card * (m * (2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * (m * (2 * Real.exp (-(u ^ 2 / (2 * τ ^ 2))))) := by
          gcongr
      _ = m * (2 * M) * Real.exp (-(u ^ 2 / (2 * τ ^ 2))) := by ring
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 < Real.log (2 * M) := Real.log_pos (by linarith)
  set a := τ * Real.sqrt (2 * Real.log (2 * M)) with ha_def
  have ha : 0 < a := by positivity
  have hasq : a ^ 2 = τ ^ 2 * (2 * Real.log (2 * M)) := by
    rw [ha_def, mul_pow, Real.sq_sqrt (by positivity)]
  have hexpa : Real.exp (-(a ^ 2 / (2 * τ ^ 2))) = 1 / (2 * M) := by
    have : a ^ 2 / (2 * τ ^ 2) = Real.log (2 * M) := by
      rw [hasq]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have key : ∫ u in (0 : ℝ)..R, g u ≤ m * a + m * (τ ^ 2 / a) := by
    have hτa : 0 ≤ m * (τ ^ 2 / a) := by positivity
    by_cases hRa : R ≤ a
    · calc ∫ u in (0 : ℝ)..R, g u ≤ ∫ u in (0 : ℝ)..R, m := by
            apply intervalIntegral.integral_mono_on (hMx0 ω₀) hg_anti.intervalIntegrable
              intervalIntegrable_const
            intro u _; exact hg_le_m u
        _ = m * R := by simp [mul_comm]
        _ ≤ m * a + m * (τ ^ 2 / a) := by nlinarith
    · push Not at hRa
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) hg_anti.intervalIntegrable
        hg_anti.intervalIntegrable]
      have h1 : ∫ u in (0 : ℝ)..a, g u ≤ m * a := by
        calc ∫ u in (0 : ℝ)..a, g u ≤ ∫ u in (0 : ℝ)..a, m :=
              intervalIntegral.integral_mono_on ha.le hg_anti.intervalIntegrable
                intervalIntegrable_const (fun u _ => hg_le_m u)
          _ = m * a := by simp [mul_comm]
      have h2 : ∫ u in a..R, g u ≤ m * (τ ^ 2 / a) := by
        calc ∫ u in a..R, g u ≤ ∫ u in a..R, m * (2 * M) * Real.exp (-(u ^ 2 / (2 * τ ^ 2))) := by
              apply intervalIntegral.integral_mono_on hRa.le hg_anti.intervalIntegrable
                (Continuous.intervalIntegrable (by fun_prop) _ _)
              intro u hu; exact hg_tail u (ha.trans_le hu.1)
          _ = m * (2 * M) * ∫ u in a..R, Real.exp (-(u ^ 2 / (2 * τ ^ 2))) :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ m * (2 * M) * (τ ^ 2 / a * Real.exp (-(a ^ 2 / (2 * τ ^ 2)))) := by
              gcongr
              exact integral_exp_neg_sq_le ha hRa.le hτ
          _ = m * (τ ^ 2 / a) := by
              rw [hexpa]; field_simp
      linarith
  have hsum' : ∑ ω, (s.sup' hs fun i => |ξ i ω|) = ∫ u in (0 : ℝ)..R, g u := hsum
  unfold uniformExpect
  rw [hsum', ← hm]
  calc m⁻¹ * ∫ u in (0 : ℝ)..R, g u ≤ m⁻¹ * (m * a + m * (τ ^ 2 / a)) := by gcongr
    _ = a + τ ^ 2 / a := by field_simp
    _ = τ * (Real.sqrt (2 * Real.log (2 * M)) + 1 / Real.sqrt (2 * Real.log (2 * M))) := by
        rw [ha_def]
        have hs0 : 0 < Real.sqrt (2 * Real.log (2 * M)) := Real.sqrt_pos.mpr (by positivity)
        field_simp

end MaximalInequality

section Covering

variable {T : Type*} [PseudoMetricSpace T]

/- @[blueprint "def:sqrt-log-covering"
  (statement := /-- The Dudley integrand $\varepsilon \mapsto \sqrt{\log N(F, d, \varepsilon)}$,
    with $N$ the internal covering number by closed balls (Mathlib's
    \texttt{Metric.coveringNumber}; $\log \infty := \log 0 := 0$ in Lean, and negative
    $\varepsilon$ are truncated to $0$). -/)] -/
noncomputable def sqrtLogCovering (F : Set T) (ε : ℝ) : ℝ :=
  Real.sqrt (Real.log ((coveringNumber (Real.toNNReal ε) F : ℝ≥0∞).toReal))

/- @[blueprint "lem:sqrt-log-covering-nonneg"
  (statement := /-- The Dudley integrand is nonnegative. -/)] -/
theorem sqrtLogCovering_nonneg (F : Set T) (ε : ℝ) : 0 ≤ sqrtLogCovering F ε :=
  Real.sqrt_nonneg _

/- @[blueprint "lem:exists-finset-net"
  (statement := /-- For $F$ totally bounded and $\varepsilon > 0$ there is a finite
    $\varepsilon$-net $C \subseteq F$ with $|C| = N(F, \varepsilon)$: every $t \in F$ is within
    distance $\varepsilon$ of some $c \in C$. -/)] -/
theorem exists_finset_net {F : Set T} (hF : TotallyBounded F) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ C : Finset T, (↑C : Set T) ⊆ F ∧ (C.card : ℕ∞) = coveringNumber ε F ∧
      ∀ t ∈ F, ∃ c ∈ C, dist t c ≤ ε := by
  obtain ⟨C, hCF, hCfin, hCcov, hCcard⟩ :=
    exists_set_encard_eq_coveringNumber
      (coveringNumber_ne_top_of_totallyBounded hF (pos_iff_ne_zero.mpr hε))
  refine ⟨hCfin.toFinset, by simpa using hCF, ?_, ?_⟩
  · rw [← hCcard, hCfin.encard_eq_coe_toFinset_card]
  · intro t ht
    have := hCcov.subset_iUnion_closedBall ht
    simp only [Set.mem_iUnion, exists_prop] at this
    obtain ⟨c, hc, hct⟩ := this
    exact ⟨c, hCfin.mem_toFinset.mpr hc, Metric.mem_closedBall.mp hct⟩

/- @[blueprint "lem:two-le-covering-of-lt-diam"
  (statement := /-- If $2\varepsilon < \mathrm{diam}(F)$ then $N(F, \varepsilon) \ge 2$ (a
    single closed $\varepsilon$-ball has diameter $\le 2\varepsilon$). -/)] -/
theorem two_le_coveringNumber_of_two_mul_lt_diam {F : Set T} {ε : ℝ≥0}
    (h : 2 * (ε : ℝ) < diam F) : 2 ≤ coveringNumber ε F := by
  by_contra hlt
  push Not at hlt
  have hne : coveringNumber ε F ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  obtain ⟨C, hCF, hCfin, hCcov, hCcard⟩ := exists_set_encard_eq_coveringNumber hne
  rw [← hk] at hlt hCcard
  have hk1 : k ≤ 1 := by
    have : k < 2 := by exact_mod_cast hlt
    omega
  have hC1 : C.encard ≤ 1 := by rw [hCcard]; exact_mod_cast hk1
  rcases Set.encard_le_one_iff_eq.mp hC1 with hC | ⟨c, hc⟩
  · have hFe : F = ∅ := by
      rw [hC] at hCcov
      exact Set.eq_empty_of_forall_notMem fun t ht => by
        obtain ⟨y, hy, _⟩ := hCcov ht
        exact hy
    rw [hFe, diam_empty] at h
    linarith [ε.coe_nonneg]
  · rw [hc] at hCcov
    have hsub : F ⊆ closedBall c ε := by
      intro t ht
      have := hCcov.subset_iUnion_closedBall ht
      simpa using this
    have := (diam_mono hsub isBounded_closedBall).trans (diam_closedBall ε.coe_nonneg)
    linarith

/- @[blueprint "lem:sqrt-log-covering-ge"
  (statement := /-- Let $F$ be totally bounded, $0 < x \le \varepsilon$, $2x < \mathrm{diam}(F)$
    and $N = N(F, \varepsilon)$. Then $\sqrt{\log \max(N, 2)} \le \sqrt{\log N(F, x)}$
    (monotonicity of covering numbers and \texttt{lem:two-le-covering-of-lt-diam}). -/)] -/
theorem sqrt_log_max_le_sqrtLogCovering {F : Set T} (hF : TotallyBounded F) {N : ℕ} {ε x : ℝ}
    (hx : 0 < x) (hxε : x ≤ ε) (h2x : 2 * x < diam F)
    (hN : (N : ℕ∞) = coveringNumber (Real.toNNReal ε) F) :
    Real.sqrt (Real.log (max (N : ℝ) 2)) ≤ sqrtLogCovering F x := by
  unfold sqrtLogCovering
  apply Real.sqrt_le_sqrt
  have hx0 : Real.toNNReal x ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero]; exact not_le.mpr hx
  have hnetop := coveringNumber_ne_top_of_totallyBounded hF (pos_iff_ne_zero.mpr hx0)
  have hnetop' : (coveringNumber (Real.toNNReal x) F : ℝ≥0∞) ≠ ⊤ := by simpa using hnetop
  apply Real.log_le_log (by positivity)
  rw [max_le_iff]
  constructor
  · have h1 : (N : ℕ∞) ≤ coveringNumber (Real.toNNReal x) F :=
      hN ▸ coveringNumber_anti (Real.toNNReal_le_toNNReal hxε)
    have h2 : ((N : ℕ∞) : ℝ≥0∞) ≤ (coveringNumber (Real.toNNReal x) F : ℝ≥0∞) := by
      exact_mod_cast h1
    have h3 := ENNReal.toReal_mono hnetop' h2
    simpa using h3
  · have h1 : (2 : ℕ∞) ≤ coveringNumber (Real.toNNReal x) F :=
      two_le_coveringNumber_of_two_mul_lt_diam (by rw [Real.coe_toNNReal _ hx.le]; exact h2x)
    have h2 : ((2 : ℕ∞) : ℝ≥0∞) ≤ (coveringNumber (Real.toNNReal x) F : ℝ≥0∞) := by
      exact_mod_cast h1
    have h3 := ENNReal.toReal_mono hnetop' h2
    simpa using h3

end Covering

section Chain

/- @[blueprint "def:chain-points"
  (statement := /-- Given projections $\pi_k$ (one for each scale $k$) and a top scale $K$, the
    chain of a point $t$ is $c_0 = \pi_K(t)$, $c_{j+1} = \pi_{K-(j+1)}(c_j)$, so that $c_j$ lives
    at scale $K - j$ and $c_K = \pi_0(\cdot)$. -/)] -/
def chainPt {α : Type*} (proj : ℕ → α → α) (K : ℕ) (t : α) : ℕ → α
  | 0 => proj K t
  | j + 1 => proj (K - (j + 1)) (chainPt proj K t j)

/- @[blueprint "lem:chain-telescoping"
  (statement := /-- Telescoping along the chain: for any $g$,
    $g(t) = (g(t) - g(c_0)) + \sum_{j < K} (g(c_j) - g(c_{j+1})) + g(c_K)$. -/)] -/
theorem chain_telescope {α : Type*} (proj : ℕ → α → α) (K : ℕ) (t : α) (g : α → ℝ) :
    g t = (g t - g (chainPt proj K t 0)) +
      ∑ j ∈ Finset.range K, (g (chainPt proj K t j) - g (chainPt proj K t (j + 1))) +
      g (chainPt proj K t K) := by
  rw [Finset.sum_range_sub']; ring

end Chain

section Dudley

variable {Ω : Type*} [Fintype Ω] {T : Type*} [PseudoMetricSpace T]

/- @[blueprint "def:sg-increments-finite"
  (statement := /-- \textbf{Sub-Gaussian increments (finite uniform space).} A process
    $Y : T \to (\Omega \to \mathbb R)$ on the finite uniform probability space $\Omega$ has
    $\sigma$-sub-Gaussian increments on $F \subseteq T$ with respect to the pseudometric $d$ if
    for all $s, t \in F$: $d(s,t) = 0 \Rightarrow Y_s = Y_t$, and for all $u > 0$
    $$\mathbb P(|Y_s - Y_t| > u) \le 2 \exp\Bigl(-\frac{u^2}{2 \sigma^2 d(s,t)^2}\Bigr).$$ -/)] -/
def SubGaussianIncrementsOn (F : Set T) (Y : T → Ω → ℝ) (σ : ℝ) : Prop :=
  (∀ s ∈ F, ∀ t ∈ F, dist s t = 0 → ∀ ω, Y s ω = Y t ω) ∧
  ∀ s ∈ F, ∀ t ∈ F, ∀ u : ℝ, 0 < u →
    tailFrac (fun ω => Y s ω - Y t ω) u ≤
      2 * Real.exp (-(u ^ 2 / (2 * σ ^ 2 * dist s t ^ 2)))

/- @[blueprint "lem:sg-tail-uniform"
  (statement := /-- If $Y$ has $\sigma$-sub-Gaussian increments on $F$, $s, t \in F$ and
    $d(s,t) \le \rho$ with $\rho > 0$, then
    $\mathbb P(|Y_s - Y_t| > u) \le 2\exp(-u^2/(2(\sigma\rho)^2))$ for all $u > 0$. -/)] -/
theorem tailFrac_sub_le_of_dist_le {F : Set T} {Y : T → Ω → ℝ} {σ : ℝ}
    (hY : SubGaussianIncrementsOn F Y σ) (hσ : 0 < σ) {s t : T} (hs : s ∈ F) (ht : t ∈ F)
    {ρ : ℝ} (hst : dist s t ≤ ρ) {u : ℝ} (hu : 0 < u) :
    tailFrac (fun ω => Y s ω - Y t ω) u ≤ 2 * Real.exp (-(u ^ 2 / (2 * (σ * ρ) ^ 2))) := by
  classical
  by_cases hd : dist s t = 0
  · have hYst : ∀ ω, Y s ω - Y t ω = 0 := fun ω => by rw [hY.1 s hs t ht hd ω, sub_self]
    have h0 : tailFrac (fun ω => Y s ω - Y t ω) u = 0 := by
      unfold tailFrac
      rw [Finset.filter_eq_empty_iff.mpr (fun ω _ => by
        simp only [hYst ω, abs_zero, not_lt]; exact hu.le)]
      simp
    rw [h0]; positivity
  · refine (hY.2 s hs t ht u hu).trans ?_
    have hden : 2 * σ ^ 2 * dist s t ^ 2 ≤ 2 * (σ * ρ) ^ 2 := by
      rw [mul_pow]
      have := pow_le_pow_left₀ dist_nonneg hst 2
      nlinarith [sq_nonneg σ]
    have hd0 : 0 < dist s t := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    have h1 : u ^ 2 / (2 * (σ * ρ) ^ 2) ≤ u ^ 2 / (2 * σ ^ 2 * dist s t ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have h2 := Real.exp_le_exp.mpr (neg_le_neg h1)
    linarith

/- @[blueprint "lem:sg-lipschitz-finite"
  (statement := /-- \textbf{Sure Lipschitz bound on a finite space.} If $Y$ has
    $\sigma$-sub-Gaussian increments on $F$ (finite nonempty uniform $\Omega$), $s, t \in F$ and
    $d(s,t) \le \rho$, $\rho > 0$, then for every $\omega$
    $|Y_s(\omega) - Y_t(\omega)| \le \sigma \rho \sqrt{2\log(2|\Omega|)}$. -/)] -/
theorem abs_sub_le_of_dist_le [Nonempty Ω] {F : Set T} {Y : T → Ω → ℝ} {σ : ℝ}
    (hY : SubGaussianIncrementsOn F Y σ) (hσ : 0 < σ) {s t : T} (hs : s ∈ F) (ht : t ∈ F)
    {ρ : ℝ} (hρ : 0 < ρ) (hst : dist s t ≤ ρ) (ω : Ω) :
    |Y s ω - Y t ω| ≤ σ * ρ * Real.sqrt (2 * Real.log (2 * Fintype.card Ω)) :=
  abs_le_of_tailFrac_le (fun ω => Y s ω - Y t ω) (by positivity)
    (fun u hu => tailFrac_sub_le_of_dist_le hY hσ hs ht hst hu) ω

/- @[blueprint "thm:dudley-subgaussian"
  (statement := /-- \textbf{Dudley's entropy integral for sub-Gaussian processes on a finite
    probability space.} Let $\Omega$ be a finite nonempty set with the uniform distribution,
    $(T, d)$ a pseudometric space, $F \subseteq T$ totally bounded, $t_0 \in F$, and
    $Y : T \to (\Omega \to \mathbb R)$ a process with $Y_{t_0} = 0$ and $\sigma$-sub-Gaussian
    increments on $F$ ($\sigma > 0$), i.e. $d(s,t) = 0 \Rightarrow Y_s = Y_t$ and
    $\mathbb P(|Y_s - Y_t| > u) \le 2\exp(-u^2/(2\sigma^2 d(s,t)^2))$ for $s, t \in F$, $u > 0$.
    Assume that $\varepsilon \mapsto \sqrt{\log N(F, d, \varepsilon)}$ is integrable on
    $[0, \mathrm{diam}(F)]$ ($N$ = internal covering number by closed balls). Then
    $$\mathbb E \sup_{t \in F} Y_t \le 12\,\sigma \int_0^{\mathrm{diam}(F)}
      \sqrt{\log N(F, d, \varepsilon)}\, d\varepsilon.$$
    (Proof: chaining at the dyadic scales $\varepsilon_k = \mathrm{diam}(F)/2^k$ with nested
    nets; the level-$k$ increments are indexed by the net of size $N_k = N(F, \varepsilon_k)$
    and have distances $\le 2\varepsilon_k$, so by \texttt{lem:emax-of-tail} and
    \texttt{lem:psi-le-three-sqrt-log} they contribute at most
    $6\sigma\varepsilon_k\sqrt{\log\max(N_k,2)} \le 12\sigma
    \int_{\varepsilon_{k+1}}^{\varepsilon_k} \sqrt{\log N(F,\varepsilon)}\,d\varepsilon$;
    the residual at the finest scale is at most
    $\sigma \varepsilon_K \sqrt{2\log(2|\Omega|)} \to 0$ by
    \texttt{lem:sg-lipschitz-finite}.) -/)] -/
theorem dudley_subgaussian_finite_space [Nonempty Ω] {F : Set T} (hF : TotallyBounded F)
    {t₀ : T} (ht₀ : t₀ ∈ F) (Y : T → Ω → ℝ) (hY₀ : ∀ ω, Y t₀ ω = 0) {σ : ℝ} (hσ : 0 < σ)
    (hY : SubGaussianIncrementsOn F Y σ)
    (hint : IntervalIntegrable (sqrtLogCovering F) volume 0 (diam F)) :
    uniformExpect (fun ω => ⨆ t : F, Y t ω) ≤
      12 * σ * ∫ ε in (0 : ℝ)..(diam F), sqrtLogCovering F ε := by
  classical
  haveI : Nonempty F := ⟨⟨t₀, ht₀⟩⟩
  set D := diam F with hD
  have hbdd : Bornology.IsBounded F := hF.isBounded
  have hD0 : 0 ≤ D := diam_nonneg
  set m : ℝ := (Fintype.card Ω : ℝ) with hm
  set Lm := Real.sqrt (2 * Real.log (2 * m)) with hLm
  have hLm0 : 0 ≤ Lm := Real.sqrt_nonneg _
  have hI0 : 0 ≤ ∫ ε in (0 : ℝ)..D, sqrtLogCovering F ε :=
    intervalIntegral.integral_nonneg hD0 (fun x _ => sqrtLogCovering_nonneg F x)
  rcases hD0.lt_or_eq with hDpos | hDzero
  swap
  · -- `diam F = 0`: the process vanishes identically on `F`.
    have hY0 : ∀ t : F, ∀ ω, Y t ω = 0 := by
      intro t ω
      have hd : dist (t : T) t₀ = 0 :=
        le_antisymm ((dist_le_diam_of_mem hbdd t.2 ht₀).trans (by rw [← hD, ← hDzero]))
          dist_nonneg
      rw [hY.1 t t.2 t₀ ht₀ hd ω, hY₀]
    have h1 : uniformExpect (fun ω => ⨆ t : F, Y t ω) = 0 := by
      simp only [hY0, ciSup_const]
      unfold uniformExpect; simp
    rw [h1]
    exact mul_nonneg (by positivity) hI0
  -- Dyadic scales.
  set ε : ℕ → ℝ := fun k => D / 2 ^ k with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hε]; positivity
  have hεle : ∀ k, ε k ≤ D := fun k => by
    simp only [hε]; exact div_le_self hD0 (one_le_pow₀ (by norm_num))
  have hεsucc : ∀ k, ε (k + 1) = ε k / 2 := fun k => by
    simp only [hε]; rw [pow_succ]; ring
  have hε0 : ε 0 = D := by simp [hε]
  have hεanti : ∀ a b, a ≤ b → ε b ≤ ε a := fun a b h => by
    simp only [hε]
    exact div_le_div_of_nonneg_left hD0 (by positivity) (pow_le_pow_right₀ (by norm_num) h)
  have hεne : ∀ k, Real.toNNReal (ε k) ≠ 0 := fun k => by
    rw [ne_eq, Real.toNNReal_eq_zero]; exact not_le.mpr (hεpos k)
  have hintε : ∀ a b, IntervalIntegrable (sqrtLogCovering F) volume (ε a) (ε b) := fun a b =>
    hint.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hD0]; exact ⟨(hεpos a).le, hεle a⟩)
      (by rw [Set.uIcc_of_le hD0]; exact ⟨(hεpos b).le, hεle b⟩))
  -- Nets (as finsets of the subtype `F`).
  have hnet : ∀ k : ℕ, ∃ C : Finset F, (C.card : ℕ∞) = coveringNumber (Real.toNNReal (ε k)) F ∧
      ∀ t : F, ∃ c ∈ C, dist (t : T) c ≤ ε k := by
    intro k
    obtain ⟨C, hCF, hCcard, hCcov⟩ := exists_finset_net hF (hεne k)
    refine ⟨C.subtype (· ∈ F), ?_, ?_⟩
    · rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hCF (Finset.mem_coe.mpr hx)),
        hCcard]
    · intro t
      obtain ⟨c, hc, hct⟩ := hCcov t t.2
      exact ⟨⟨c, hCF (Finset.mem_coe.mpr hc)⟩, Finset.mem_subtype.mpr hc,
        by rwa [Real.coe_toNNReal _ (hεpos k).le] at hct⟩
  choose net hnetcard hnetcov using hnet
  have hne : ∀ k, (net k).Nonempty := fun k => by
    obtain ⟨c, hc, _⟩ := hnetcov k ⟨t₀, ht₀⟩
    exact ⟨c, hc⟩
  -- Projections: `proj 0 = t₀`, `proj k t ∈ net k` within `ε k` of `t`.
  have hproj : ∀ k : ℕ, ∀ t : F, ∃ c : F, (k = 0 → c = ⟨t₀, ht₀⟩) ∧ (k ≠ 0 → c ∈ net k) ∧
      dist (t : T) c ≤ ε k := by
    intro k t
    rcases Nat.eq_zero_or_pos k with hk | hk
    · refine ⟨⟨t₀, ht₀⟩, fun _ => rfl, fun h => absurd hk h, ?_⟩
      rw [hk, hε0]; exact dist_le_diam_of_mem hbdd t.2 ht₀
    · obtain ⟨c, hc, hct⟩ := hnetcov k t
      exact ⟨c, fun h => absurd h hk.ne', fun _ => hc, hct⟩
  choose proj hproj0 hprojnet hprojdist using hproj
  -- Chain facts.
  have hchain_mem : ∀ K (t : F) j, j < K → chainPt proj K t j ∈ net (K - j) := by
    intro K t j hj
    cases j with
    | zero => simp only [chainPt, Nat.sub_zero]; exact hprojnet K t (by omega)
    | succ j => simp only [chainPt]; exact hprojnet (K - (j + 1)) _ (by omega)
  have hchain_dist : ∀ K (t : F) j,
      dist ((chainPt proj K t j : F) : T) ((chainPt proj K t (j + 1) : F) : T) ≤
        ε (K - (j + 1)) := by
    intro K t j
    simp only [chainPt]
    exact hprojdist (K - (j + 1)) (chainPt proj K t j)
  have hchain_top : ∀ K (t : F), chainPt proj K t K = ⟨t₀, ht₀⟩ := by
    intro K t
    cases K with
    | zero => exact hproj0 0 t rfl
    | succ K => simp only [chainPt]; exact hproj0 _ _ (by omega)
  have hchain_start : ∀ K (t : F), dist (t : T) ((chainPt proj K t 0 : F) : T) ≤ ε K :=
    fun K t =>
    hprojdist K t
  -- Level-`k` increment maxima.
  set B : ℕ → Ω → ℝ := fun k ω =>
    (net k).sup' (hne k) fun c => |Y c ω - Y (proj (k - 1) c) ω| with hB
  -- Pointwise chain bound.
  have hpoint : ∀ K (t : F) ω, Y t ω ≤ σ * ε K * Lm + ∑ j ∈ Finset.range K, B (j + 1) ω := by
    intro K t ω
    have htel := chain_telescope proj K t (fun x : F => Y x ω)
    rw [hchain_top K t, hY₀, add_zero] at htel
    have h1 : Y t ω - Y ((chainPt proj K t 0 : F) : T) ω ≤ σ * ε K * Lm :=
      (le_abs_self _).trans (abs_sub_le_of_dist_le hY hσ t.2 (chainPt proj K t 0).2 (hεpos K)
        (hchain_start K t) ω)
    have h2 : ∑ j ∈ Finset.range K, (Y ((chainPt proj K t j : F) : T) ω -
        Y ((chainPt proj K t (j + 1) : F) : T) ω) ≤ ∑ j ∈ Finset.range K, B (K - j) ω := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      refine (le_abs_self _).trans ?_
      have hmem := hchain_mem K t j hj
      have := Finset.le_sup' (fun c : F => |Y c ω - Y (proj (K - j - 1) c) ω|) hmem
      simp only [hB]
      convert this using 3
      simp only [chainPt, Nat.sub_sub]
    have h3 : ∑ j ∈ Finset.range K, B (K - j) ω = ∑ j ∈ Finset.range K, B (j + 1) ω := by
      rw [← Finset.sum_range_reflect (fun j => B (j + 1) ω) K]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      congr 2; omega
    linarith
  -- Per-scale bound via the maximal inequality.
  have hscale : ∀ k, 1 ≤ k →
      uniformExpect (B k) ≤ 12 * σ * ∫ x in ε (k + 1)..ε k, sqrtLogCovering F x := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp
      (coveringNumber_ne_top_of_totallyBounded hF (pos_iff_ne_zero.mpr (hεne (k' + 1))))
    have hcard : (net (k' + 1)).card ≤ N := by
      have : ((net (k' + 1)).card : ℕ∞) = N := by rw [hnetcard (k' + 1), hN]
      exact_mod_cast this.le
    have hN1 : 1 ≤ N := by
      have : 1 ≤ (net (k' + 1)).card := Finset.card_pos.mpr (hne (k' + 1))
      omega
    have hτ : 0 < σ * ε k' := by positivity
    have htail' : ∀ c ∈ net (k' + 1), ∀ u : ℝ, 0 < u →
        tailFrac (fun ω => Y c ω - Y (proj k' c) ω) u ≤
          2 * Real.exp (-(u ^ 2 / (2 * (σ * ε k') ^ 2))) := fun c _ u hu =>
      tailFrac_sub_le_of_dist_le hY hσ c.2 (proj k' c).2 (hprojdist k' c) hu
    have hmax : uniformExpect (B (k' + 1)) ≤ σ * ε k' *
        (Real.sqrt (2 * Real.log (2 * N)) + 1 / Real.sqrt (2 * Real.log (2 * N))) :=
      uniformExpect_sup'_abs_le_of_tail (net (k' + 1)) (hne (k' + 1))
        (fun c ω => Y c ω - Y (proj k' c) ω) hτ hN1 hcard htail'
    have hpsi := psi_le_three_sqrt_log N hN1
    have hεk : ε k' = 2 * ε (k' + 1) := by rw [hεsucc]; ring
    have hlow : Real.sqrt (Real.log (max (N : ℝ) 2)) * (ε (k' + 1) - ε (k' + 2)) ≤
        ∫ x in ε (k' + 2)..ε (k' + 1), sqrtLogCovering F x := by
      apply mul_le_integral_of_forall_Ico (hεanti _ _ (by omega)) (hintε _ _)
      intro x hx
      apply sqrt_log_max_le_sqrtLogCovering hF ((hεpos (k' + 2)).trans_le hx.1) hx.2.le _ hN
      have h1 : ε (k' + 1) ≤ ε 1 := hεanti 1 (k' + 1) (by omega)
      have h2 : ε 1 = D / 2 := by simp [hε]
      linarith [hx.2]
    calc uniformExpect (B (k' + 1)) ≤ σ * ε k' *
          (Real.sqrt (2 * Real.log (2 * N)) + 1 / Real.sqrt (2 * Real.log (2 * N))) := hmax
      _ ≤ σ * ε k' * (3 * Real.sqrt (Real.log (max (N : ℝ) 2))) := by gcongr
      _ = 12 * σ * (Real.sqrt (Real.log (max (N : ℝ) 2)) * (ε (k' + 1) - ε (k' + 2))) := by
          rw [hεk, hεsucc (k' + 1)]; ring
      _ ≤ 12 * σ * ∫ x in ε (k' + 2)..ε (k' + 1), sqrtLogCovering F x := by gcongr
  -- Summing the scales.
  have hsumInt : ∀ K, ∑ j ∈ Finset.range K, ∫ x in ε (j + 2)..ε (j + 1), sqrtLogCovering F x =
      ∫ x in ε (K + 1)..ε 1, sqrtLogCovering F x := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, add_comm,
        intervalIntegral.integral_add_adjacent_intervals (hintε _ _) (hintε _ _)]
  -- Bound for every `K`.
  have hK : ∀ K, uniformExpect (fun ω => ⨆ t : F, Y t ω) ≤
      σ * ε K * Lm + 12 * σ * ∫ x in (0 : ℝ)..D, sqrtLogCovering F x := by
    intro K
    calc uniformExpect (fun ω => ⨆ t : F, Y t ω) ≤
          uniformExpect (fun ω => σ * ε K * Lm + ∑ j ∈ Finset.range K, B (j + 1) ω) :=
          uniformExpect_mono fun ω => ciSup_le fun t => hpoint K t ω
      _ = σ * ε K * Lm + ∑ j ∈ Finset.range K, uniformExpect (B (j + 1)) :=
          uniformExpect_const_add_sum _ _ _
      _ ≤ σ * ε K * Lm + ∑ j ∈ Finset.range K,
            12 * σ * ∫ x in ε (j + 2)..ε (j + 1), sqrtLogCovering F x := by
          gcongr with j hj
          exact hscale (j + 1) (by omega)
      _ = σ * ε K * Lm + 12 * σ * ∫ x in ε (K + 1)..ε 1, sqrtLogCovering F x := by
          rw [← Finset.mul_sum, hsumInt]
      _ ≤ σ * ε K * Lm + 12 * σ * ∫ x in (0 : ℝ)..D, sqrtLogCovering F x := by
          gcongr
          apply intervalIntegral.integral_mono_interval (hεpos (K + 1)).le
            (hεanti 1 (K + 1) (by omega)) (hεle 1)
            (Filter.Eventually.of_forall fun x => sqrtLogCovering_nonneg F x) hint
  -- Let `K → ∞`.
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨K, hKlt⟩ := exists_pow_lt_of_lt_one (x := η / (σ * Lm * D + 1)) (by positivity)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hεK : ε K = D * (1 / 2) ^ K := by simp only [hε]; rw [one_div_pow]; ring
  have hsmall : σ * ε K * Lm < η := by
    rw [hεK]
    rw [lt_div_iff₀ (by positivity)] at hKlt
    have h0 : 0 ≤ σ * Lm * D := by positivity
    have h1 : 0 < (1 / 2 : ℝ) ^ K := by positivity
    nlinarith
  linarith [hK K]

end Dudley

end FoML.ToFoML
