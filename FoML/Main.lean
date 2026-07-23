import FoML.Generalization.LinearPredictorL2
import FoML.Generalization.LinearPredictorL1
import FoML.Generalization.Dudley
import FoML.Generalization.FiniteClass
import FoML.Generalization.LipschitzParameter
import FoML.Generalization.Learning
import FoML.Rademacher.Reindex

/-!
# End-to-end examples

This is the main user-facing entry point of `lean-rademacher`. The proofs
below deliberately repeat the principal applications as short `example`s:
the reusable implementation lives in the imported generalization modules,
while this file shows which hypotheses a user needs to provide.

## The generic bridge

Suppose a separable hypothesis class `F` satisfies the fixed-sample estimate

$$
\widehat{\mathfrak R}_n(F;S)\le C
\qquad\text{for every sample }S.
$$

If every function is bounded by `b`, then the bridge gives

$$
\Pr\!\left\{
  \operatorname{UD}_n(F;S)
  \ge 2C+b\sqrt{\frac{2\log(1/\delta)}{n}}
\right\}\le\delta.
$$

The first example is the Lean form of this reusable step.
-/

section

universe u v w

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒳 : Type w}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
Generic end-to-end use: substitute a deterministic empirical Rademacher
upper bound into the separable-class confidence theorem.
-/
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b C δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hn : 0 < n)
    (hC : ∀ S : Fin n → 𝒳, empiricalRademacherComplexity n F S ≤ C)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * C + b * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  exact uniform_deviation_tail_bound_separable_of_empirical_le_delta
    (μ := μ) hn F hF_meas X hX hb hF_bound hF_cont hC hδ hδ_one

/-!
## The observed empirical complexity

The basic sample-dependent theorem keeps the empirical Rademacher complexity
of the observed sample in the threshold:

$$
\Pr\!\left\{
  \operatorname{UD}_n(F;S)
  \ge 2\widehat{\mathfrak R}_n(F;S)+3\varepsilon
\right\}
\le
2\exp\!\left(-\frac{n\varepsilon^2}{2b^2}\right).
$$

Thus this single statement exhibits the three commonly used variants
requested at once: a separable hypothesis class, a high-probability estimate,
and empirical rather than expected Rademacher complexity.
-/

/-- Basic separable high-probability bound using observed empirical complexity. -/
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      2 * empiricalRademacherComplexity n F (X ∘ S) + 3 * ε ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  exact uniform_deviation_tail_bound_separable_of_empirical_complexity
    (μ := μ) F hF_meas X hX hb hF_bound hF_cont hε

/-!
## `ℓ₂` linear predictors

For weights with $\lVert w\rVert_2\le W$ and inputs with
$\lVert x\rVert_2\le X$, the deterministic end-to-end estimate is

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge \frac{2XW}{\sqrt n}
    +XW\sqrt{\frac{2\log(1/\delta)}{n}}
\right\}\le\delta.
$$

`linear_predictor_l2_uniform_deviation_tail_bound_delta` obtains this result
by composing the fixed-sample linear estimate with the generic bridge.
-/

/-- Main deterministic-threshold example for the `ℓ₂` linear class. -/
example
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * (X * W / Real.sqrt (n : ℝ)) +
          (X * W) * Real.sqrt (2 * Real.log (1 / δ) / n) ≤
        uniformDeviation n
          (linearPredictorL2 :
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
          μ Z (Z ∘ S)}).toReal ≤ δ := by
  exact linear_predictor_l2_uniform_deviation_tail_bound_delta
    d W X hn hX hW Z hZ hδ hδ_one

/-!
The sample-dependent variant retains the observed quadratic radius:

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge \frac{2W}{n}\sqrt{\sum_k\lVert Z_k\rVert_2^2}
    +3XW\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}\le\delta.
$$
-/

/-- Main sample-dependent example for the `ℓ₂` linear class. -/
example
    [IsProbabilityMeasure μ]
    (d : ℕ) (W X : ℝ) (hn : 0 < n) (hX : 0 < X) (hW : 0 < W)
    (Z : Ω → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X)
    (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (W * (n : ℝ)⁻¹ *
            Real.sqrt
              (∑ k : Fin n,
                ‖(Z (S k) : EuclideanSpace ℝ (Fin d))‖ ^ 2)) +
        3 * ((X * W) * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n
            (linearPredictorL2 :
              Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W →
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  exact linear_predictor_l2_uniform_deviation_tail_bound_of_sample_delta
    d W X hn hX hW Z hZ hδ hδ_one

/-!
## `ℓ₁/ℓ∞` linear predictors

For $\lVert w\rVert_1\le W$ and $\lVert x\rVert_\infty\le X_\infty$, let

$$
Q_\infty(S)
=\frac1n\sup_{j<d}\sqrt{\sum_k |S_{k,j}|^2}.
$$

The sample-dependent estimate is

$$
\Pr\!\left\{
  \operatorname{UD}_n
  \ge 2WQ_\infty(S)\sqrt{2\log(2d)}
    +3X_\infty W\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}\le\delta.
$$
-/

/-- Main sample-dependent example for the `ℓ₁/ℓ∞` linear class. -/
example
    [IsProbabilityMeasure μ]
    (d : ℕ) (Xinf W : ℝ) (hX : 0 < Xinf) (hW : 0 < W)
    (hd : 0 < d) (hn : 0 < n)
    (Z : Ω → LinftyBall (d := d) Xinf) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (W * linearPredictorL1SampleRadius (Z ∘ S) *
            Real.sqrt (2 * Real.log (2 * d))) +
        3 * ((Xinf * W) * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n
            (linearPredictorL1 :
              L1Ball (d := d) W → LinftyBall (d := d) Xinf → ℝ)
            μ Z (Z ∘ S)}).toReal ≤ δ := by
  exact linear_predictor_l1_uniform_deviation_tail_bound_of_sample_delta
    d Xinf W hX hW hd hn Z hZ hδ hδ_one

/-!
## Dudley entropy integral

For

$$
D_\alpha(F,S)
=4\alpha+\frac{12}{\sqrt n}
  \int_\alpha^{c/2}\sqrt{\log N(F\cup(-F),x)}\,dx,
$$

the entropy route ends in the directly usable statement

$$
\Pr\!\left\{
  \operatorname{UD}_n(F;S)
  \ge 2D_\alpha(F,S)
    +3b\sqrt{\frac{2\log(2/\delta)}{n}}
\right\}\le\delta.
$$

No sample-uniform deterministic upper bound on the entropy integral is
required in this form.
-/

/-- Main sample-dependent Dudley entropy-integral example. -/
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hF_cont : ∀ x : 𝒳, Continuous fun h ↦ F h x)
    (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (h : H), empiricalNorm S (F h) ≤ c)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * dudleyEntropyEstimate F (X ∘ S) (htb (X ∘ S)) α c +
        3 * (b * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  exact uniform_deviation_tail_bound_separable_of_dudley_delta
    F hF_meas X hX hb hF_bound hF_cont hn hα hαc
    htb hnorm hδ hδ_one

/-!
For a finite hypothesis class, taking every hypothesis as a cover center gives
$N(F^\pm,\varepsilon)\leq2|H|$.  Choosing $\alpha=c/4$ in Dudley's estimate
removes the covering number completely:

$$
\widehat{\mathfrak R}_n(F;S)
\leq
c+\frac{3c}{\sqrt n}\sqrt{\log(2|H|)}.
$$

The following high-probability example has no unevaluated entropy term.
-/

/-- Explicit finite-class Dudley generalization bound. -/
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Fintype H] [Nonempty H] [IsProbabilityMeasure μ]
    (F : H → 𝒳 → ℝ) (hF_meas : ∀ h, Measurable (F h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c δ : ℝ} (hb : 0 < b) (hF_bound : ∀ h x, |F h x| ≤ b)
    (hn : 0 < n) (hc : 0 < c)
    (hNorm : ∀ (S : Fin n → 𝒳) h, empiricalNorm S (F h) ≤ c)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 *
          (c + (3 * c / Real.sqrt n) *
            Real.sqrt (Real.log (2 * Fintype.card H))) +
          3 * sampleConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  exact uniform_deviation_tail_bound_finite_of_dudley_quarter_delta
    F hF_meas X hX hb hF_bound hn hc hNorm hδ hδ_one

/-!
For a continuously parameterized family $F_t$, $t\in[-W,W]$, satisfying

$$
|F_t(x)-F_s(x)|\leq L|t-s|,
$$

an equally spaced grid gives

$$
N(F,\varepsilon)
\leq
\left\lceil\frac{2WL}{\varepsilon}\right\rceil+1.
$$

Freezing this estimate at the Dudley truncation scale $\alpha$ yields the
following confidence bound, again with no unevaluated covering number.
-/

/-- Explicit Dudley generalization bound for a Lipschitz parameter family. -/
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [IsProbabilityMeasure μ]
    (hn : 0 < n)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (F : Set.Icc (-W) W → 𝒳 → ℝ)
    (hF_meas : ∀ t, Measurable (F t))
    (hF_lip : ∀ t s x, |F t x - F s x| ≤ L * |t.1 - s.1|)
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α δ : ℝ} (hb : 0 < b) (hF_bound : ∀ t x, |F t x| ≤ b)
    (hα : 0 < α) (hαc : α < c / 2)
    (hNorm : ∀ (S : Fin n → 𝒳) t, empiricalNorm S (F t) ≤ c)
    (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * lipschitzParameterDudleyEstimate n W L α c +
          3 * sampleConfidenceRadius b δ n ≤
        uniformDeviation n F μ X (X ∘ S)}).toReal ≤ δ := by
  exact uniform_deviation_tail_bound_lipschitzParameter_dudley_delta
    hn hW hL F hF_meas hF_lip X hX hb hF_bound
    hα hαc hNorm hδ hδ_one

/-!
## Approximate ERM and excess risk

Let `A(S)` be an $\eta$-approximate empirical risk minimizer for a bounded
loss class $\ell$.  The deterministic oracle inequality

$$
R(A(S))-R(h^\star)
\leq
2\operatorname{UD}_n(\ell;S)+\eta
$$

composes with the observed empirical Rademacher estimate to give

$$
\Pr\!\left\{
R(A(S))-R(h^\star)
\geq
4C(S)+6b\sqrt{\frac{2\log(2/\delta)}{n}}+\eta
\right\}
\leq\delta,
$$

whenever
$\widehat{\mathfrak R}_n(\ell;S)\leq C(S)$.
The learning rule itself need not be measurable: the conclusion uses outer
probability through `Measure.real`.
-/

/-- Main sample-dependent excess-risk example for an approximate ERM. -/
example
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty H]
    [TopologicalSpace H] [SeparableSpace H] [FirstCountableTopology H]
    [IsProbabilityMeasure μ]
    (ℓ : H → 𝒳 → ℝ) (hℓ_meas : ∀ h, Measurable (ℓ h))
    (X : Ω → 𝒳) (hX : Measurable X)
    (C : (Fin n → 𝒳) → ℝ)
    {b η δ : ℝ} (hb : 0 < b) (hℓ_bound : ∀ h x, |ℓ h x| ≤ b)
    (hℓ_cont : ∀ x : 𝒳, Continuous fun h ↦ ℓ h x)
    (A : (Fin n → 𝒳) → H)
    (hA : ∀ S, IsApproxERM η n ℓ S (A S))
    (hC : ∀ S, empiricalRademacherComplexity n ℓ S ≤ C S)
    (hstar : H) (hn : 0 < n) (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      4 * C (X ∘ S) + 6 * sampleConfidenceRadius b δ n + η ≤
        excessRisk ℓ μ X (A (X ∘ S)) hstar}).toReal ≤ δ := by
  exact approxERM_excessRisk_tail_bound_separable_of_sample_empirical_le_delta
    (μ := μ) hn ℓ hℓ_meas X hX C hb hℓ_bound hℓ_cont
    A hA hC hstar hδ hδ_one

/-!
For a finite hypothesis type, a centered $L$-Lipschitz loss satisfies the
absolute-complexity contraction estimate

$$
\widehat{\mathfrak R}_n((\ell-\ell(0,\cdot))\circ F;S)
\leq
2L\,\widehat{\mathfrak R}_n(F;S).
$$

The factor `2` is specific to this repository's absolute-value definition.
The corresponding one-sided theorem has factor `L`.
-/

/-- Main contraction example for a centered supervised loss. -/
example
    {𝒴 : Type*} [Fintype H] [Nonempty H]
    (F : H → 𝒳 → ℝ) (loss : ℝ → 𝒴 → ℝ)
    (S : Fin n → 𝒳 × 𝒴) {L : ℝ} (hL : 0 ≤ L)
    (hloss : ∀ y u v, |loss u y - loss v y| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (supervisedLossClass F (centeredLoss loss)) S ≤
      2 * L *
        empiricalRademacherComplexity n
          (fun (h : H) (z : 𝒳 × 𝒴) ↦ F h z.1) S := by
  exact empiricalRademacherComplexity_centered_supervisedLossClass_le
    n F loss S hL hloss

end
