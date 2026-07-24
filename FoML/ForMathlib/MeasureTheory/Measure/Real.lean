import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Auxiliary lemmas for real-valued measures

This file contains order-theoretic facts about `Measure.real` that are useful
for concentration inequalities but do not depend on Rademacher complexity.
-/

open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/--
Increasing the threshold function decreases a superlevel event.

If `A ω ≤ B ω` for every `ω`, then
`{ω | B ω ≤ G ω} ⊆ {ω | A ω ≤ G ω}`.
-/
theorem measureReal_superlevel_mono [IsFiniteMeasure μ]
    {A B G : Ω → ℝ} (hAB : ∀ ω, A ω ≤ B ω) :
    μ.real {ω | B ω ≤ G ω} ≤ μ.real {ω | A ω ≤ G ω} := by
  apply measureReal_mono (h₂ := measure_ne_top μ _)
  intro ω hω
  exact (hAB ω).trans hω

/--
Turn a centered upper-tail estimate into an upper-tail estimate around any
upper bound `C` on the mean.

The conclusion is the elementary implication

`C + ε ≤ Y ω → ε ≤ Y ω - ∫ ω, Y ω ∂μ`.
-/
theorem measureReal_superlevel_le_of_centered [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {C ε p : ℝ}
    (hmean : ∫ ω, Y ω ∂μ ≤ C)
    (htail : μ.real {ω | ε ≤ Y ω - ∫ ω, Y ω ∂μ} ≤ p) :
    μ.real {ω | C + ε ≤ Y ω} ≤ p := by
  calc
    μ.real {ω | C + ε ≤ Y ω} ≤
        μ.real {ω | ε ≤ Y ω - ∫ ω, Y ω ∂μ} := by
      apply measureReal_mono (h₂ := measure_ne_top μ _)
      intro ω hω
      dsimp only [Set.mem_setOf_eq] at hω ⊢
      linarith
    _ ≤ p := htail

end MeasureTheory
