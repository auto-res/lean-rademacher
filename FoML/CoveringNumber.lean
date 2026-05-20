import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Classical

/-- Open ball defined by an arbitrary two-variable radius function. -/
def coverBall {X : Type*} (d : X → X → ℝ) (x : X) (ε : ℝ) : Set X :=
  {y : X | d y x < ε}

/-- A set admits finite `ε`-covers with respect to `d` for every positive radius. -/
def HasFiniteCovers {X : Type*} (d : X → X → ℝ) (A : Set X) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ t : Finset X, ↑t ⊆ A ∧ A ⊆ ⋃ y ∈ t, coverBall d y ε

lemma coveringNumber_exists {X : Type*} {A : Set X} (d : X → X → ℝ)
    (ha : HasFiniteCovers d A) {ε : ℝ} (εpos : ε > 0) :
    ∃ n : Nat, ∃ t : Finset X, t.card = n ∧ ↑t ⊆ A ∧ A ⊆ ⋃ y ∈ t, coverBall d y ε := by
  rcases ha εpos with ⟨t, htA, hcover⟩
  exact ⟨t.card, t, rfl, htA, hcover⟩

noncomputable def coveringNumber {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) (ε : ℝ) : ℕ :=
  if h : ε > 0 then
    Nat.find (coveringNumber_exists d ha h)
  else 0

theorem coveringNumber_eq {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) {ε : ℝ} (hε : ε > 0) :
    coveringNumber d ha ε = Nat.find (coveringNumber_exists d ha hε) :=
  dif_pos hε

theorem converingNumber_antitone {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) :
    AntitoneOn (coveringNumber d ha) (Set.Ioi 0) := by
  intro ε₁ hε₁ ε₂ hε₂ hε₁ε₂
  rw [coveringNumber_eq d ha hε₁, coveringNumber_eq d ha hε₂]
  apply Nat.find_mono
  intro n hn
  rcases hn with ⟨t, ht₁, htA, ht₂⟩
  exact ⟨t, ht₁, htA, ht₂.trans <| by
    apply Set.iUnion_mono
    intro y
    apply Set.iUnion_mono
    intro hy
    intro x hx
    exact lt_of_lt_of_le hx hε₁ε₂⟩

theorem coveringNumber_nonzero {X : Type*} (d : X → X → ℝ) {A : Set X} (hs : A.Nonempty)
    (ha : HasFiniteCovers d A) {ε : ℝ} (hε : ε > 0) :
    0 < coveringNumber d ha ε := by
  dsimp [coveringNumber]
  simp [hε]
  exact Set.nonempty_iff_ne_empty.mp hs

theorem converingNumber_aemeasurable {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) :
    AEMeasurable (coveringNumber d ha) MeasureTheory.volume := by
  have h₀ : AEMeasurable (coveringNumber d ha) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (converingNumber_antitone d ha)
  convert (aemeasurable_indicator_iff measurableSet_Ioi).mpr h₀
  ext ε
  if h : ε ∈ Set.Ioi 0 then
    rw [Set.indicator_of_mem h]
  else
    rw [Set.indicator_of_notMem h]
    rw [coveringNumber, dif_neg (by exact h)]

noncomputable def coveringFinset {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) {ε : ℝ} (hε : ε > 0) : Finset X :=
  Classical.choose (Nat.find_spec (coveringNumber_exists d ha hε))

lemma coveringFinset_cover {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) {ε : ℝ} (hε : ε > 0) :
    A ⊆ ⋃ y ∈ coveringFinset d ha hε, coverBall d y ε := by
  simpa [coveringFinset, coveringNumber_exists] using
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists d ha hε))).2.2

lemma coveringFinset_subset {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) {ε : ℝ} (hε : ε > 0) :
    ↑(coveringFinset d ha hε) ⊆ A := by
  simpa [coveringFinset, coveringNumber_exists] using
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists d ha hε))).2.1

lemma coveringFinset_card {X : Type*} (d : X → X → ℝ) {A : Set X}
    (ha : HasFiniteCovers d A) {ε : ℝ} (hε : ε > 0) :
    (coveringFinset d ha hε).card = coveringNumber d ha ε := by
  have h :=
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists d ha hε))).1
  simpa [coveringFinset, coveringNumber_eq d ha hε, coveringNumber_exists] using h
