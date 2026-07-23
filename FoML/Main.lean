import FoML.LinearPredictorL2Generalization
import FoML.LinearPredictorL1Generalization
import FoML.DudleyGeneralization

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

end
