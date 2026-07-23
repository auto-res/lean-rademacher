import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Distance between indexed suprema

This file contains an order-theoretic Lipschitz estimate for real-valued
indexed suprema.  It is independent of the statistical-learning definitions.
-/

open Set

/--
Reindexing an indexed supremum along a surjection does not change it.

Unlike `Function.Surjective.iSup_comp` for complete lattices, this version is
available for conditionally complete lattices because it compares the two
ranges directly.
-/
theorem ciSup_comp_of_surjective
    {ι κ E : Type*} [ConditionallyCompleteLattice E]
    (e : κ → ι) (he : Function.Surjective e) (f : ι → E) :
    (⨆ k, f (e k)) = ⨆ i, f i := by
  simp only [iSup]
  congr
  exact he.range_comp f

/--
If two bounded-above real families are pointwise at distance at most `c`,
then their indexed suprema are at distance at most `c`.
-/
theorem abs_ciSup_sub_ciSup_le
    {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {c : ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (hfg : ∀ i, |f i - g i| ≤ c) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  apply abs_sub_le_iff.mpr
  constructor
  · rw [ciSup_sub hf]
    apply ciSup_le
    intro i
    calc
      f i - ⨆ j, g j ≤ f i - g i := by
        gcongr
        exact le_ciSup hg i
      _ ≤ |f i - g i| := le_abs_self _
      _ ≤ c := hfg i
  · rw [ciSup_sub hg]
    apply ciSup_le
    intro i
    calc
      g i - ⨆ j, f j ≤ g i - f i := by
        gcongr
        exact le_ciSup hf i
      _ ≤ |g i - f i| := le_abs_self _
      _ = |f i - g i| := abs_sub_comm _ _
      _ ≤ c := hfg i
