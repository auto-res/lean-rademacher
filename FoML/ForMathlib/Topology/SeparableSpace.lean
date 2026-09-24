import Mathlib.Topology.Bases
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Suprema over separable spaces

This file records reusable facts for replacing a supremum over a separable
space by a supremum over Mathlib's chosen countable dense sequence.
-/

universe u v w

open TopologicalSpace

lemma closure_mem_le_sSup
    {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E]
    [OrderClosedTopology E]
    {s : Set E} (hs : BddAbove s) {b : E} (hb : b ∈ closure s) :
    b ≤ sSup s := by
  have hsubset : s ⊆ Set.Iic (sSup s) := by
    intro x hx
    exact le_csSup hs hx
  have hclosure : closure s ⊆ Set.Iic (sSup s) :=
    closure_minimal hsubset isClosed_Iic
  exact hclosure hb

lemma sSup_eq_closure_sSup
    {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E]
    [OrderClosedTopology E]
    {s : Set E} (hs : s.Nonempty) (hs' : BddAbove s) :
    sSup s = sSup (closure s) := by
  have hclosure : BddAbove (closure s) := by
    use sSup s
    intro b hb
    exact closure_mem_le_sSup hs' hb
  apply le_antisymm
  · apply csSup_le_csSup hclosure hs
    exact subset_closure
  · apply csSup_le (by aesop)
    exact fun b hb ↦ closure_mem_le_sSup hs' hb

lemma closure_range_eq_closure_denseSeq
    {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
    {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E]
    [OrderClosedTopology E]
    {f : X → E} (hf : Continuous f) :
    closure (Set.range f) = closure (Set.range (f ∘ denseSeq X)) := by
  rw [Set.range_comp f (denseSeq X)]
  apply Set.Subset.antisymm
  · have hdense : Dense (Set.range (denseSeq X)) := denseRange_denseSeq X
    have himage := hf.range_subset_closure_image_dense hdense
    exact closure_minimal himage isClosed_closure
  · apply closure_mono
    exact Set.image_subset_range f (Set.range (denseSeq X))

theorem separableSpaceSup_eq
    {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
    {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E]
    [OrderClosedTopology E]
    {f : X → E} (hf : Continuous f) (hf' : BddAbove (Set.range f)) :
    ⨆ x : X, f x = ⨆ i : Nat, f (denseSeq X i) := by
  calc
    _ = sSup (closure (Set.range f)) :=
      sSup_eq_closure_sSup (Set.range_nonempty f) hf'
    _ = sSup (closure (Set.range (f ∘ denseSeq X))) := by
      rw [closure_range_eq_closure_denseSeq hf]
    _ = sSup (Set.range (f ∘ denseSeq X)) := by
      have hbounded : BddAbove (Set.range (f ∘ denseSeq X)) := by
        rw [Set.range_comp f (denseSeq X)]
        exact BddAbove.mono
          (Set.image_subset_range f (Set.range (denseSeq X))) hf'
      exact (sSup_eq_closure_sSup
        (Set.range_nonempty (f ∘ denseSeq X)) hbounded).symm

theorem separableSpaceSup_eq_real
    {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
    {f : X → ℝ} (hf : Continuous f) :
    ⨆ x : X, f x = ⨆ i : Nat, f (denseSeq X i) := by
  if hbounded : BddAbove (Set.range f) then
    exact separableSpaceSup_eq hf hbounded
  else
    have hdense_unbounded : ¬ BddAbove (Set.range (f ∘ denseSeq X)) := by
      intro h
      have hclosure :
          BddAbove (closure (Set.range (f ∘ denseSeq X))) :=
        bddAbove_closure.mpr h
      rw [← closure_range_eq_closure_denseSeq hf] at hclosure
      exact hbounded (bddAbove_closure.mp hclosure)
    calc
      _ = 0 := Real.iSup_of_not_bddAbove hbounded
      _ = _ := (Real.iSup_of_not_bddAbove hdense_unbounded).symm

/--
Restriction of a family to Mathlib's chosen countable dense sequence.

The definition includes its value, rather than merely introducing a type:

`denseRestriction F = F ∘ denseSeq H`.
-/
noncomputable abbrev denseRestriction
    {H : Type u} {α : Type w}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    (F : H → α) : ℕ → α :=
  F ∘ denseSeq H

@[simp]
lemma denseRestriction_apply
    {H : Type u} {α : Type w}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    (F : H → α) (i : ℕ) :
    denseRestriction F i = F (denseSeq H i) :=
  rfl

lemma measurable_denseRestriction_apply
    {H : Type u} {α : Type w} {β : Type*}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    [MeasurableSpace α] [MeasurableSpace β]
    {F : H → α → β} (hF : ∀ h, Measurable (F h)) (i : ℕ) :
    Measurable (denseRestriction F i) :=
  hF (denseSeq H i)

lemma abs_denseRestriction_le
    {H : Type u} {α : Type w}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    {F : H → α → ℝ} {b : ℝ}
    (hF : ∀ h x, |F h x| ≤ b) :
    ∀ i x, |denseRestriction F i x| ≤ b :=
  fun i x ↦ hF (denseSeq H i) x
