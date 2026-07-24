import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Confidence radii

The lemmas in this file package the elementary real calculation used to turn
sub-Gaussian tail estimates into bounds parametrized by a failure probability.
-/

open Real

/--
The sub-Gaussian confidence radius with tail prefactor `κ`:

`confidenceRadius κ b δ n = b * √(2 * log (κ / δ) / n)`.
-/
noncomputable def confidenceRadius (κ b δ : ℝ) (n : ℕ) : ℝ :=
  b * Real.sqrt (2 * Real.log (κ / δ) / n)

/--
Substituting `confidenceRadius κ b δ n` into a sub-Gaussian tail with
prefactor `κ` gives exactly `δ`.
-/
theorem mul_exp_neg_confidenceRadius_sq
    {n : ℕ} (hn : 0 < n) {κ b δ : ℝ}
    (hκ : 0 < κ) (hb : 0 < b) (hδ : 0 < δ) (hδκ : δ ≤ κ) :
    κ * (-confidenceRadius κ b δ n ^ 2 * n / (2 * b ^ 2)).exp = δ := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hone : 1 ≤ κ / δ := by
    apply (le_div_iff₀ hδ).2
    simpa [one_mul] using hδκ
  have hquot : 0 < κ / δ := div_pos hκ hδ
  have hlog : 0 ≤ Real.log (κ / δ) := Real.log_nonneg hone
  have harg : 0 ≤ 2 * Real.log (κ / δ) / (n : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hlog) hnR.le
  have hsqrt :
      Real.sqrt (2 * Real.log (κ / δ) / (n : ℝ)) ^ 2 =
        2 * Real.log (κ / δ) / (n : ℝ) :=
    Real.sq_sqrt harg
  have hexponent :
      -confidenceRadius κ b δ n ^ 2 * (n : ℝ) / (2 * b ^ 2) =
        -Real.log (κ / δ) := by
    rw [confidenceRadius, mul_pow, hsqrt]
    field_simp [hb.ne', hnR.ne']
  rw [hexponent, Real.exp_neg, Real.exp_log hquot]
  field_simp [hκ.ne', hδ.ne']

