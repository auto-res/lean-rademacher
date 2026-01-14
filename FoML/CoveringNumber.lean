import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Classical

lemma coveringNumber_exists {X : Type*} {A : Set X} [PseudoMetricSpace X] (ha : TotallyBounded A) {ε : ℝ} (εpos: ε > 0):
  ∃ n : Nat, ∃ t : Finset X, t.card = n ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  have hh : ∀ d ∈ uniformity X, ∃ (t : Set X), t.Finite ∧ A ⊆ ⋃ y ∈ t, {x : X | (x, y) ∈ d} := ha
  have hball := Metric.finite_approx_of_totallyBounded ha ε εpos
  have ⟨t, ⟨ht, tfin, tball⟩⟩  := hball
  have : Fintype t := tfin.fintype
  let n : Nat := this.card
  exists n
  exists t.toFinset
  constructor
  · exact Set.toFinset_card t
  · convert tball
    ext _
    simp only [Set.mem_toFinset]

noncomputable def coveringNumber {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) (ε : ℝ): ℕ :=
  if h : ε > 0 then
    Nat.find (coveringNumber_exists ha h)
  else 0

theorem coveringNumber_eq {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
  coveringNumber ha ε = Nat.find (coveringNumber_exists ha hε) := dif_pos hε

theorem converingNumber_antitone {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) :
  AntitoneOn (coveringNumber ha) (Set.Ioi 0) := by
  intro ε₁ hε₁ ε₂ hε₂ hε₁ε₂
  rw [coveringNumber_eq ha hε₁, coveringNumber_eq ha hε₂]
  apply Nat.find_mono
  intro n ⟨t, ht₁, ht₂⟩
  exists t, ht₁
  apply ht₂.trans
  apply Set.iUnion_mono
  intro _
  apply Set.iUnion_mono
  intro _
  exact Metric.ball_subset_ball hε₁ε₂

theorem coveringNumber_nonzero {X : Type*} [PseudoMetricSpace X] {A : Set X} (hs : A.Nonempty) (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    0 < coveringNumber ha ε := by
  dsimp [coveringNumber]
  simp [hε]
  exact Set.nonempty_iff_ne_empty.mp hs

theorem converingNumber_aemeasurable {X : Type*} [PseudoMetricSpace X] {A : Set X} (ha : TotallyBounded A) :
  AEMeasurable (coveringNumber ha) MeasureTheory.volume := by
  have h₀ : AEMeasurable (coveringNumber ha) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (converingNumber_antitone ha)
  convert (aemeasurable_indicator_iff measurableSet_Ioi).mpr h₀
  ext ε
  if h : ε ∈ Set.Ioi 0 then
    rw [Set.indicator_of_mem h]
  else
    rw [Set.indicator_of_notMem h]
    rw [coveringNumber, dif_neg (by exact h)]

noncomputable def coveringFinset
  {X : Type*} [PseudoMetricSpace X] {A : Set X}
  (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) : Finset X :=
  Classical.choose (Nat.find_spec (coveringNumber_exists (X:=X) (A:=A) ha hε))

lemma coveringFinset_cover
  {X : Type*} [PseudoMetricSpace X] {A : Set X}
  (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
  A ⊆ ⋃ y ∈ coveringFinset ha hε, Metric.ball y ε := by
  simpa [coveringFinset, coveringNumber_exists] using
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists (X:=X) (A:=A) ha hε))).2

lemma coveringFinset_card
  {X : Type*} [PseudoMetricSpace X] {A : Set X}
  (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
  (coveringFinset ha hε).card = coveringNumber ha ε := by
  have h :=
    (Classical.choose_spec (Nat.find_spec (coveringNumber_exists (X:=X) (A:=A) ha hε))).1
  simpa [coveringFinset, coveringNumber_eq (X:=X) (A:=A) ha hε, coveringNumber_exists] using h
