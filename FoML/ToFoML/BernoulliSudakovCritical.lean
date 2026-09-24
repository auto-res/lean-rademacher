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
import FoML.ToMathlib.GaussianSudakov
import FoML.ToFoML.BernoulliSudakovTools
import FoML.ToFoML.BernoulliSudakovTruncation

/-!
# Bernoulli–Sudakov minoration: the critical case and subset selection

Rows B7 and B9 of the Bernoulli–Sudakov blueprint (lean-deepgen's `00note/sudakov-math.md`, §2 steps S9–S10,
§4 item 5).

For `u : Fin M → Fin n → ℝ` write `b(u) := bernoulliSup u` for the one-sided Rademacher average
`2^{-n} ∑_σ max_j ∑_i σ_i u_{j,i}` and `g(u) := ∫ max_j ∑_i u_{j,i} g_i dγ_n` for the
Gaussian analogue.

**B7 (critical case, ULB Prop. 6.4.7).** If `M ≥ 2`, `‖u_j‖₂² ≤ 4a²`, `‖u_j‖_∞ ≤ b`, the family is
`a`-separated in `ℓ₂` and `√(log M) ≤ a/b`, then `b(u) ≥ a √(log M) / L₃`.
Proof: split each Gaussian coordinate `g_i = ξ_c(g_i) + ξ'_c(g_i)` at level `c = 2B + 1`; then
`a√(log M)/(6√2) ≤ g(u) ≤ ∫ max_j ∑ ξ_c u + ∫ max_j ∑ ξ'_c u ≤ 16 a√(log M)/B + c b(u)`
(`thm:gaussian-sudakov`, `lem:tail-part-max-bound`, `lem:bounded-part-max-bound`). With
`B := 192√2` the tail term is `a√(log M)/(12√2)`, half of the Gaussian lower bound, so
`a√(log M)/(12√2) ≤ (2B+1) b(u)`, i.e. `L₃ = 12√2 (384√2 + 1) = 9216 + 12√2`.

**B9 (subset selection, ULB Prop. 6.4.8).** Dropping the critical-regime assumption,
`b(u) ≥ (1/L₂) min(a√(log M), a²/b)` with `L₂ := √2 L₃`. If `√(log M) ≤ a/b` this is B7. If
`a/b < √(log 2)` any two points give `b(u) ≥ a/(2√3)` (Khintchine) and `a²/b ≤ a√(log 2) ≤ a`.
Otherwise let `N := ⌊exp((a/b)²)⌋`; then `2 ≤ N < M`, `√(log N) ≤ a/b`, and
`log N ≥ ½ log(N+1) ≥ ½ (a/b)²` (`lem:log-two-le`), so B7 applied to the first `N` vectors
(`lem:bernoulli-sup-comp-injective`) gives `b(u) ≥ a√(log N)/L₃ ≥ a²/(√2 L₃ b)`.
-/

open Real MeasureTheory ProbabilityTheory
open scoped BigOperators

open FoML.ToMathlib

namespace FoML.ToFoML

variable {n : ℕ}

/-! ### The constants -/

/- @[blueprint "def:bernoulli-critical-B"
  (statement := /-- The truncation parameter of the critical case: $B := 192\sqrt2 = 32 \cdot
    6\sqrt2$, chosen so that the tail bound $16 a\sqrt{\log M}/B$ of
    \texttt{lem:tail-part-max-bound} equals half of the Gaussian lower bound
    $a\sqrt{\log M}/(6\sqrt2)$ of \texttt{thm:gaussian-sudakov}. The truncation level is
    $c = 2B + 1 = 384\sqrt2 + 1$. -/)] -/
noncomputable def criticalB : ℝ := 192 * √2

/- @[blueprint "lem:bernoulli-critical-B-ge-one"
  (statement := /-- $B = 192\sqrt2 \ge 1$. -/)] -/
theorem one_le_criticalB : 1 ≤ criticalB := by
  unfold criticalB
  have h : (1 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith

/- @[blueprint "def:L3"
  (statement := /-- The constant of the critical case:
    $L_3 := 12\sqrt2\,(2B + 1) = 12\sqrt2\,(384\sqrt2 + 1) = 9216 + 12\sqrt2 \approx 9233$. -/)] -/
noncomputable def L₃ : ℝ := 9216 + 12 * √2

/- @[blueprint "lem:L3-eq"
  (statement := /-- $L_3 = 12\sqrt2\,(2B + 1)$ with $B = 192\sqrt2$. -/)] -/
theorem L₃_eq : L₃ = 12 * √2 * (2 * criticalB + 1) := by
  unfold L₃ criticalB
  have h : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h]

/- @[blueprint "lem:L3-pos"
  (statement := /-- $L_3 > 0$. -/)] -/
theorem L₃_pos : 0 < L₃ := by
  unfold L₃; positivity

/- @[blueprint "def:L2"
  (statement := /-- The constant of the subset-selection step:
    $L_2 := \sqrt2\,L_3 = 9216\sqrt2 + 24 \approx 13058$. -/)] -/
noncomputable def L₂ : ℝ := √2 * L₃

/- @[blueprint "lem:L2-pos"
  (statement := /-- $L_2 > 0$. -/)] -/
theorem L₂_pos : 0 < L₂ := by
  unfold L₂; have := L₃_pos; positivity

/- @[blueprint "lem:L3-le-L2"
  (statement := /-- $L_3 \le L_2$ (since $\sqrt2 \ge 1$). -/)] -/
theorem L₃_le_L₂ : L₃ ≤ L₂ := by
  unfold L₂
  have h : (1 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  nlinarith [L₃_pos]

/- @[blueprint "lem:two-sqrt-three-le-L2"
  (statement := /-- $2\sqrt3 \le L_2$. -/)] -/
theorem two_mul_sqrt_three_le_L₂ : 2 * √3 ≤ L₂ := by
  have h3 : √3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h := L₃_le_L₂
  unfold L₃ at h
  have h2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  linarith

/-! ### An $\ell_2$ bound from an $\ell_\infty$ bound -/

/- @[blueprint "lem:sum-sq-le-of-bounded"
  (statement := /-- If $|x_i| \le b$ for all $i < n$ then $\sum_i x_i^2 \le n b^2$. -/)] -/
theorem sum_sq_le_of_abs_le {x : Fin n → ℝ} {b : ℝ} (hx : ∀ i, |x i| ≤ b) :
    ∑ i, x i ^ 2 ≤ n * b ^ 2 := by
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, b ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = n * b ^ 2 := by simp

/-! ### Integrability of the truncated maxima -/

/- @[blueprint "lem:truncation-bounded-abs-le-abs"
  (statement := /-- $|\xi'_c(y)| \le |y|$. -/)] -/
theorem abs_gaussTruncBdd_le_abs (c y : ℝ) : |gaussTruncBdd c y| ≤ |y| := by
  unfold gaussTruncBdd gaussTrunc
  split_ifs <;> simp

/- @[blueprint "lem:integrable-iSup-sum-comp-mul"
  (statement := /-- Let $f : \mathbb R \to \mathbb R$ be measurable with $|f(y)| \le |y|$ and
    $M \ge 1$. Then $x \mapsto \max_j \sum_i f(x_i)\,u_{j,i}$ is $\gamma_n$-integrable (it is
    measurable and dominated by $\sum_j \sum_i |x_i|\,|u_{j,i}|$). -/)] -/
theorem integrable_iSup_sum_comp_mul {M : ℕ} (hM : 0 < M) (u : Fin M → Fin n → ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hfle : ∀ y, |f y| ≤ |y|) :
    Integrable (fun x : Fin n → ℝ => ⨆ j, ∑ i, f (x i) * u j i) (stdGaussianPi n) := by
  have hmeas : ∀ j, Measurable fun x : Fin n → ℝ => ∑ i, f (x i) * u j i := fun j =>
    Finset.measurable_sum _ fun i _ => (hf.comp (measurable_pi_apply i)).mul_const _
  refine Integrable.mono' (g := fun x => ∑ j, ∑ i, |x i| * |u j i|) ?_ ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
      (integrable_eval_stdGaussianPi i).abs.mul_const _
  · exact (Measurable.iSup hmeas).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    refine (abs_iSup_eval_le hM fun j => ∑ i, f (x i) * u j i).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hfle _) (abs_nonneg _)

/- @[blueprint "lem:integrable-iSup-gaussTrunc"
  (statement := /-- For $M \ge 1$, $x \mapsto \max_j \sum_i \xi_c(x_i)\,u_{j,i}$ is
    $\gamma_n$-integrable. -/)] -/
theorem integrable_iSup_gaussTrunc {M : ℕ} (hM : 0 < M) (u : Fin M → Fin n → ℝ) (c : ℝ) :
    Integrable (fun x : Fin n → ℝ => ⨆ j, ∑ i, gaussTrunc c (x i) * u j i) (stdGaussianPi n) :=
  integrable_iSup_sum_comp_mul hM u (measurable_gaussTrunc c) (abs_gaussTrunc_le c)

/- @[blueprint "lem:integrable-iSup-gaussTruncBdd"
  (statement := /-- For $M \ge 1$, $x \mapsto \max_j \sum_i \xi'_c(x_i)\,u_{j,i}$ is
    $\gamma_n$-integrable. -/)] -/
theorem integrable_iSup_gaussTruncBdd {M : ℕ} (hM : 0 < M) (u : Fin M → Fin n → ℝ) (c : ℝ) :
    Integrable (fun x : Fin n → ℝ => ⨆ j, ∑ i, gaussTruncBdd c (x i) * u j i)
      (stdGaussianPi n) :=
  integrable_iSup_sum_comp_mul hM u (measurable_gaussTruncBdd c) (abs_gaussTruncBdd_le_abs c)

/-! ### Splitting the Gaussian maximum into tail and bounded parts -/

/- @[blueprint "lem:gaussian-max-truncation-split"
  (statement := /-- For $M \ge 1$ and any level $c$,
    $$\int \max_j \sum_i u_{j,i}\,g_i\,d\gamma_n \le
      \int \max_j \sum_i \xi_c(g_i)\,u_{j,i}\,d\gamma_n +
      \int \max_j \sum_i \xi'_c(g_i)\,u_{j,i}\,d\gamma_n ,$$
    since $g_i = \xi_c(g_i) + \xi'_c(g_i)$ and $\max_j(A_j + B_j) \le \max_j A_j + \max_j B_j$
    pointwise (\texttt{lem:gaussian-max-split}). -/)] -/
theorem integral_iSup_linear_le_trunc_add_truncBdd {M : ℕ} (hM : 0 < M)
    (u : Fin M → Fin n → ℝ) (c : ℝ) :
    ∫ g, ⨆ j, ∑ i, u j i * g i ∂stdGaussianPi n ≤
      (∫ x, ⨆ j, ∑ i, gaussTrunc c (x i) * u j i ∂stdGaussianPi n) +
        ∫ x, ⨆ j, ∑ i, gaussTruncBdd c (x i) * u j i ∂stdGaussianPi n := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hA := integrable_iSup_gaussTrunc hM u c
  have hB := integrable_iSup_gaussTruncBdd hM u c
  have hpt : ∀ g : Fin n → ℝ, (⨆ j, ∑ i, u j i * g i) =
      ⨆ j, (∑ i, gaussTrunc c (g i) * u j i + ∑ i, gaussTruncBdd c (g i) * u j i) := by
    intro g
    refine iSup_congr fun j => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_mul, gaussTrunc_add_gaussTruncBdd]
    ring
  rw [← integral_add hA hB]
  refine integral_mono (integrable_iSup_linear u) (hA.add hB) fun g => ?_
  simp only
  rw [hpt g]
  exact iSup_add_le_iSup_add_iSup _ _

/-! ### B7: the critical case -/

/- @[blueprint "lem:bernoulli-critical"
  (statement := /-- \textbf{Critical case} (ULB Prop.~6.4.7; blueprint S9). Let $M \ge 2$,
    $u_1, \dots, u_M \in \mathbb R^n$, $a, b > 0$ with $\|u_j\|_2^2 \le 4a^2$,
    $\|u_j\|_\infty \le b$, $\|u_j - u_k\|_2^2 \ge a^2$ for $j \ne k$, and
    $\sqrt{\log M} \le a/b$. Then
    $$ b(u) \ \ge\ \frac{a\sqrt{\log M}}{L_3}, \qquad L_3 = 9216 + 12\sqrt2 .$$
    Proof: with $B = 192\sqrt2$, $c = 2B+1$,
    $\frac{a\sqrt{\log M}}{6\sqrt2} \le g(u) \le \frac{16 a\sqrt{\log M}}{B} + c\,b(u)
    = \frac{a\sqrt{\log M}}{12\sqrt2} + c\,b(u)$ by \texttt{thm:gaussian-sudakov},
    \texttt{lem:gaussian-max-truncation-split}, \texttt{lem:tail-part-max-bound} and
    \texttt{lem:bounded-part-max-bound}; rearrange. -/)] -/
theorem bernoulli_critical {M : ℕ} (hM : 2 ≤ M) (u : Fin M → Fin n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hu2 : ∀ j, ∑ i, u j i ^ 2 ≤ 4 * a ^ 2) (hub : ∀ j i, |u j i| ≤ b)
    (hsep : ∀ j k, j ≠ k → a ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2)
    (hlog : √(Real.log M) ≤ a / b) :
    a * √(Real.log M) / L₃ ≤ bernoulliSup u := by
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  set L := √(Real.log M) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hB := one_le_criticalB
  have hBpos : 0 < criticalB := by linarith
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hc : (0 : ℝ) ≤ 2 * criticalB + 1 := by positivity
  have hG := gaussian_sudakov hM u ha.le hsep
  have hsplit := integral_iSup_linear_le_trunc_add_truncBdd (by omega) u (2 * criticalB + 1)
  have h5 := integral_iSup_gaussTrunc_le hM u ha hb hB hu2 hub hlog
  have h6 := integral_iSup_gaussTruncBdd_le u hc
  have hbu := bernoulliSup_nonneg u
  -- `16 / B = 1 / (12 √2)`
  have h16 : 16 * a * L / criticalB = a * L / (12 * √2) := by
    unfold criticalB
    field_simp
    ring
  have hkey : a * L / (12 * √2) ≤ (2 * criticalB + 1) * bernoulliSup u := by
    have h1 : a / (6 * √2) * L - a * L / (12 * √2) = a * L / (12 * √2) := by
      field_simp
      ring
    linarith
  calc a * L / L₃ = a * L / (12 * √2) / (2 * criticalB + 1) := by
        rw [L₃_eq, div_div]
    _ ≤ (2 * criticalB + 1) * bernoulliSup u / (2 * criticalB + 1) := by gcongr
    _ = bernoulliSup u := by field_simp

/-! ### Two separated points: the Khintchine lower bound -/

/- @[blueprint "lem:bernoulli-sup-two"
  (statement := /-- For two vectors $u_0, u_1 \in \mathbb R^n$,
    $b(u) \ge \frac{1}{2\sqrt3}\,\|u_0 - u_1\|_2$. Proof:
    $\max\{Z_0, Z_1\} = \frac{Z_0 + Z_1}{2} + \frac{|Z_0 - Z_1|}{2}$ with
    $Z_j = \sum_i \sigma_i u_{j,i}$; the first term averages to $0$ and the second is bounded
    below by the Khintchine lower bound \texttt{lem:khintchine-lower}. -/)] -/
theorem bernoulliSup_two_ge (u : Fin 2 → Fin n → ℝ) :
    √(∑ i, (u 0 i - u 1 i) ^ 2) / (2 * √3) ≤ bernoulliSup u := by
  set d : Fin n → ℝ := fun i => u 0 i - u 1 i with hd
  have hσ : ∀ σ : Signs n, (⨆ j, ∑ i, (σ i : ℝ) * u j i) =
      (∑ i, (σ i : ℝ) * u 0 i + ∑ i, (σ i : ℝ) * u 1 i + |∑ i, (σ i : ℝ) * d i|) / 2 := by
    intro σ
    rw [iSup_fin_two, max_eq_half_add_add_abs_sub]
    congr 2
    simp only [hd, mul_sub, Finset.sum_sub_distrib]
  have hK := khintchine_lower d
  unfold bernoulliSup
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_signs_rademacher_sum, sum_signs_rademacher_sum, zero_add,
    zero_add]
  calc √(∑ i, (u 0 i - u 1 i) ^ 2) / (2 * √3) = (√(∑ i, d i ^ 2) / √3) / 2 := by
        simp only [hd]; ring
    _ ≤ ((Fintype.card (Signs n) : ℝ)⁻¹ * ∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * d i|) / 2 := by
        gcongr
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ * ((∑ σ : Signs n, |∑ i : Fin n, (σ i : ℝ) * d i|) / 2) := by
        ring

/- @[blueprint "lem:bernoulli-sup-ge-of-separated"
  (statement := /-- If $M \ge 2$, $a \ge 0$ and $\|u_j - u_k\|_2^2 \ge a^2$ for all $j \ne k$,
    then $b(u) \ge a/(2\sqrt3)$: restrict to the first two vectors
    (\texttt{lem:bernoulli-sup-comp-injective}) and apply \texttt{lem:bernoulli-sup-two}. -/)] -/
theorem bernoulliSup_ge_of_separated {M : ℕ} (hM : 2 ≤ M) (u : Fin M → Fin n → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hsep : ∀ j k, j ≠ k → a ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2) :
    a / (2 * √3) ≤ bernoulliSup u := by
  set ι : Fin 2 → Fin M := Fin.castLE hM with hι
  have h01 : ι 0 ≠ ι 1 := (Fin.castLE_injective hM).ne (by decide)
  have hs := hsep (ι 0) (ι 1) h01
  have hsq : a ≤ √(∑ i, (u (ι 0) i - u (ι 1) i) ^ 2) :=
    (Real.le_sqrt ha (Finset.sum_nonneg fun i _ => sq_nonneg _)).mpr hs
  have h := bernoulliSup_two_ge (u ∘ ι)
  simp only [Function.comp_apply] at h
  calc a / (2 * √3) ≤ √(∑ i, (u (ι 0) i - u (ι 1) i) ^ 2) / (2 * √3) := by gcongr
    _ ≤ bernoulliSup (u ∘ ι) := h
    _ ≤ bernoulliSup u := bernoulliSup_comp_le u ι

/-! ### B9: subset selection -/

/- @[blueprint "lem:bernoulli-subset-selection"
  (statement := /-- \textbf{Subset selection} (ULB Prop.~6.4.8; blueprint S10). Let $M \ge 2$,
    $u_1, \dots, u_M \in \mathbb R^n$, $a, b > 0$ with $\|u_j\|_2^2 \le 4a^2$,
    $\|u_j\|_\infty \le b$ and $\|u_j - u_k\|_2^2 \ge a^2$ for $j \ne k$. Then
    $$ b(u) \ \ge\ \frac{1}{L_2}\,\min\Bigl(a\sqrt{\log M},\ \frac{a^2}{b}\Bigr), \qquad
       L_2 = \sqrt2\,L_3 = 9216\sqrt2 + 24 .$$
    Proof. If $\sqrt{\log M} \le a/b$, this is \texttt{lem:bernoulli-critical} (and
    $L_3 \le L_2$). If $a/b < \sqrt{\log 2}$, then $a^2/b < a\sqrt{\log2} \le a$ and
    $b(u) \ge a/(2\sqrt3) \ge a/L_2$ by \texttt{lem:bernoulli-sup-ge-of-separated}. Otherwise
    $\sqrt{\log2} \le a/b < \sqrt{\log M}$; let $N := \lfloor e^{(a/b)^2} \rfloor$, so
    $2 \le N < M$, $\log N \le (a/b)^2$ and $(a/b)^2 < \log(N+1) \le 2\log N$
    (\texttt{lem:log-two-le}). \texttt{lem:bernoulli-critical} for the first $N$ vectors and
    \texttt{lem:bernoulli-sup-comp-injective} give
    $b(u) \ge a\sqrt{\log N}/L_3 \ge a\,(a/b)/(\sqrt2 L_3) = a^2/(L_2 b)$. -/)] -/
theorem bernoulli_subset_selection {M : ℕ} (hM : 2 ≤ M) (u : Fin M → Fin n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hu2 : ∀ j, ∑ i, u j i ^ 2 ≤ 4 * a ^ 2) (hub : ∀ j i, |u j i| ≤ b)
    (hsep : ∀ j k, j ≠ k → a ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2) :
    min (a * √(Real.log M)) (a ^ 2 / b) / L₂ ≤ bernoulliSup u := by
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have hL3 := L₃_pos
  have hL2 := L₂_pos
  have hL32 := L₃_le_L₂
  have hmin_nonneg : 0 ≤ min (a * √(Real.log M)) (a ^ 2 / b) :=
    le_min (by positivity) (by positivity)
  by_cases hcrit : √(Real.log M) ≤ a / b
  · -- the critical regime: B7 directly
    have h := bernoulli_critical hM u ha hb hu2 hub hsep hcrit
    calc min (a * √(Real.log M)) (a ^ 2 / b) / L₂ ≤ a * √(Real.log M) / L₂ := by
          gcongr; exact min_le_left _ _
      _ ≤ a * √(Real.log M) / L₃ := div_le_div_of_nonneg_left (by positivity) hL3 hL32
      _ ≤ bernoulliSup u := h
  push Not at hcrit
  by_cases hsmall : a / b < √(Real.log 2)
  · -- tiny ratio: two points suffice
    have h := bernoulliSup_ge_of_separated hM u ha.le hsep
    have hlog2 : √(Real.log 2) ≤ 1 := Real.sqrt_le_one.mpr
      (by linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)])
    have h2 : a ^ 2 / b ≤ a := by
      calc a ^ 2 / b = a * (a / b) := by ring
        _ ≤ a * 1 := by gcongr; linarith
        _ = a := mul_one a
    calc min (a * √(Real.log M)) (a ^ 2 / b) / L₂ ≤ a / L₂ := by
          gcongr; exact (min_le_right _ _).trans h2
      _ ≤ a / (2 * √3) :=
          div_le_div_of_nonneg_left ha.le (by positivity) two_mul_sqrt_three_le_L₂
      _ ≤ bernoulliSup u := h
  push Not at hsmall
  -- subset selection: `N := ⌊exp((a/b)²)⌋`
  set t := a / b with ht
  have ht0 : 0 < t := by positivity
  have hlog2t : Real.log 2 ≤ t ^ 2 := (Real.sqrt_le_left ht0.le).mp hsmall
  have htM : t ^ 2 < Real.log M := (Real.lt_sqrt ht0.le).mp hcrit
  set N : ℕ := ⌊Real.exp (t ^ 2)⌋₊ with hN
  have hexp0 : 0 ≤ Real.exp (t ^ 2) := (Real.exp_pos _).le
  have h2exp : (2 : ℝ) ≤ Real.exp (t ^ 2) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp (t ^ 2) := Real.exp_le_exp.mpr hlog2t
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast h2exp)
  have hNM : N ≤ M := by
    refine ((Nat.floor_lt hexp0).mpr ?_).le
    calc Real.exp (t ^ 2) < Real.exp (Real.log M) := Real.exp_lt_exp.mpr htM
      _ = M := Real.exp_log (by positivity)
  have hNr : (N : ℝ) ≤ Real.exp (t ^ 2) := Nat.floor_le hexp0
  have hNr' : Real.exp (t ^ 2) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : Real.log N ≤ t ^ 2 := (Real.log_le_iff_le_exp hN0).mpr hNr
  have hlogN1 : t ^ 2 < Real.log ((N : ℝ) + 1) :=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hNr'
  have hlogN2 : t ^ 2 / 2 ≤ Real.log N := by
    have := log_add_one_le_two_mul_log hN2
    linarith
  have hsqrtN : √(Real.log N) ≤ t := (Real.sqrt_le_left ht0.le).mpr hlogN
  have hsqrtN' : t / √2 ≤ √(Real.log N) := by
    rw [Real.le_sqrt (by positivity) (Real.log_nonneg hN1), div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hlogN2
  -- B7 on the first `N` vectors
  set ι : Fin N → Fin M := Fin.castLE hNM with hι
  have hB7 := bernoulli_critical hN2 (u ∘ ι) ha hb (fun j => hu2 (ι j))
    (fun j i => hub (ι j) i)
    (fun j k hjk => hsep (ι j) (ι k) ((Fin.castLE_injective hNM).ne hjk)) hsqrtN
  calc min (a * √(Real.log M)) (a ^ 2 / b) / L₂ ≤ a ^ 2 / b / L₂ := by
        gcongr; exact min_le_right _ _
    _ = a * (t / √2) / L₃ := by
        rw [ht]
        unfold L₂
        field_simp
    _ ≤ a * √(Real.log N) / L₃ := by gcongr
    _ ≤ bernoulliSup (u ∘ ι) := hB7
    _ ≤ bernoulliSup u := bernoulliSup_comp_le u ι

end FoML.ToFoML
