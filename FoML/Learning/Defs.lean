import FoML.Defs

/-!
# Risks, empirical risk minimization, and loss classes

This file defines the basic learning-theoretic objects used by the excess-risk
bounds.  An empirical risk minimizer is represented by a predicate rather than
by a chosen `argmin`; consequently, downstream oracle inequalities do not need
existence or measurability assumptions that are irrelevant to their proofs.
-/

noncomputable section

universe u v w

open MeasureTheory

variable {Ω : Type u} {H : Type v} {𝒵 : Type w}

/--
The population risk of `h`:

`populationRisk ℓ μ Z h = ∫ ω, ℓ h (Z ω) ∂μ`.
-/
def populationRisk
    [MeasurableSpace Ω]
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵) (h : H) : ℝ :=
  ∫ ω, ℓ h (Z ω) ∂μ

/--
The empirical risk of `h` on a sample `S` of size `n`:

`empiricalRisk n ℓ S h = n⁻¹ * ∑ k, ℓ h (S k)`.
-/
def empiricalRisk
    (n : ℕ) (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (h : H) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k : Fin n, ℓ h (S k)

/--
The excess risk of `h` relative to a comparator `hstar`:

`excessRisk ℓ μ Z h hstar = R(h) - R(hstar)`.

The comparator need not minimize population risk.  This makes deterministic
oracle inequalities reusable even when existence of a minimizer is handled
separately.
-/
def excessRisk
    [MeasurableSpace Ω]
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵)
    (h hstar : H) : ℝ :=
  populationRisk ℓ μ Z h - populationRisk ℓ μ Z hstar

/--
`hhat` is an empirical risk minimizer for `ℓ` on `S`.
-/
def IsERM
    (n : ℕ) (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (hhat : H) : Prop :=
  ∀ h, empiricalRisk n ℓ S hhat ≤ empiricalRisk n ℓ S h

/--
`hhat` is an `η`-approximate empirical risk minimizer for `ℓ` on `S`.
-/
def IsApproxERM
    (η : ℝ) (n : ℕ) (ℓ : H → 𝒵 → ℝ)
    (S : Fin n → 𝒵) (hhat : H) : Prop :=
  ∀ h, empiricalRisk n ℓ S hhat ≤ empiricalRisk n ℓ S h + η

/--
`hstar` minimizes population risk over the represented hypothesis class.
-/
def IsPopulationRiskMinimizer
    [MeasurableSpace Ω]
    (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵) (hstar : H) : Prop :=
  ∀ h, populationRisk ℓ μ Z hstar ≤ populationRisk ℓ μ Z h

/--
The pointwise discrepancy between empirical and population risk.
-/
def riskDeviation
    [MeasurableSpace Ω]
    (n : ℕ) (ℓ : H → 𝒵 → ℝ) (μ : Measure Ω) (Z : Ω → 𝒵)
    (S : Fin n → 𝒵) (h : H) : ℝ :=
  |empiricalRisk n ℓ S h - populationRisk ℓ μ Z h|

/--
The supervised loss class induced by predictors `F` and a loss function
`loss`: `(x, y) ↦ loss (F h x) y`.
-/
def supervisedLossClass
    {𝒳 𝒴 : Type*}
    (F : H → 𝒳 → ℝ) (loss : ℝ → 𝒴 → ℝ) : H → (𝒳 × 𝒴) → ℝ :=
  fun h z ↦ loss (F h z.1) z.2

/--
Center a loss in its prediction argument.  The centered loss vanishes at
prediction zero and has the same Lipschitz constant as the original loss.
-/
def centeredLoss {𝒴 : Type*} (loss : ℝ → 𝒴 → ℝ) : ℝ → 𝒴 → ℝ :=
  fun u y ↦ loss u y - loss 0 y

@[simp]
lemma centeredLoss_zero {𝒴 : Type*} (loss : ℝ → 𝒴 → ℝ) (y : 𝒴) :
    centeredLoss loss 0 y = 0 := by
  simp [centeredLoss]

lemma centeredLoss_add_base
    {𝒴 : Type*} (loss : ℝ → 𝒴 → ℝ) (u : ℝ) (y : 𝒴) :
    centeredLoss loss u y + loss 0 y = loss u y := by
  simp [centeredLoss]

lemma supervisedLossClass_eq_centered_add_base
    {𝒳 𝒴 : Type*}
    (F : H → 𝒳 → ℝ) (loss : ℝ → 𝒴 → ℝ) (h : H) (z : 𝒳 × 𝒴) :
    supervisedLossClass F loss h z =
      supervisedLossClass F (centeredLoss loss) h z + loss 0 z.2 := by
  simp [supervisedLossClass, centeredLoss]

end
