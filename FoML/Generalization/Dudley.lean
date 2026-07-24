import FoML.Generalization.Confidence
import FoML.Entropy.Dudley

/-!
# Dudley entropy estimates and generalization bounds

This file connects the fixed-sample Dudley entropy integral to expected and
high-probability Rademacher generalization bounds.
-/

section

universe u v

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type*}
variable {μ : Measure Ω}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/--
The Dudley entropy estimate for absolute empirical Rademacher complexity:

`Dα(F,S) = 4α + (12 / √n) ∫_[α,c/2] √(log N(F ∪ -F, x)) dx`.

The proof `hTotallyBounded` supplies the finite covering-number construction.
-/
noncomputable def dudleyEntropyEstimate
    {n : ℕ} {ι : Type v} {𝒳 : Type*}
    (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (hTotallyBounded :
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (α c : ℝ) : ℝ :=
  4 * α + (12 / Real.sqrt n) *
    (∫ x : ℝ in α..(c / 2),
      Real.sqrt (Real.log (coveringNumber
        (signSymmetrization_totallyBounded
          (F := F) (S := S) hTotallyBounded) x)))

/-- Fixed-sample one-sided Dudley entropy-integral estimate. -/
theorem dudley_entropy_integral_bound
    {n : ℕ} {ι : Type u} [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
    (hε : 0 < ε)
    (hTotallyBounded :
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (hn : 0 < n) (hNorm : ∀ h : ι, empiricalNorm S (F h) ≤ c)
    (hεc : ε < c / 2) :
    empiricalRademacherComplexity_without_abs n F S ≤
      4 * ε + (12 / Real.sqrt n) *
        (∫ x : ℝ in ε..(c / 2),
          Real.sqrt (Real.log (coveringNumber hTotallyBounded x))) := by
  exact dudley_entropy_integral'
    hε hTotallyBounded hn hNorm hεc

/--
Fixed-sample Dudley estimate for absolute empirical Rademacher complexity:

`R̂ₙ(F;S) ≤ Dα(F,S)`.
-/
theorem dudley_entropy_integral_bound_abs
    {n : ℕ} {ι : Type u} [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
    (hε : 0 < ε)
    (hTotallyBounded :
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (hn : 0 < n) (hNorm : ∀ h : ι, empiricalNorm S (F h) ≤ c)
    (hεc : ε < c / 2) :
    empiricalRademacherComplexity n F S ≤
      dudleyEntropyEstimate F S hTotallyBounded ε c := by
  exact dudley_entropy_integral_abs
    hε hTotallyBounded hn hNorm hεc

/--
For a class closed under pointwise negation, the entropy of the original
class suffices for the absolute empirical Rademacher estimate.
-/
theorem dudley_entropy_integral_bound_abs_of_neg_closed
    {n : ℕ} {ι : Type u} [Nonempty ι]
    {F : ι → 𝒳 → ℝ} {S : Fin n → 𝒳} {c ε : ℝ}
    (hε : 0 < ε)
    (hTotallyBounded :
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)))
    (hn : 0 < n) (hNorm : ∀ h : ι, empiricalNorm S (F h) ≤ c)
    (hεc : ε < c / 2) (hneg : IsNegClosed F) :
    empiricalRademacherComplexity n F S ≤
      4 * ε + (12 / Real.sqrt n) *
        (∫ x : ℝ in ε..(c / 2),
          Real.sqrt (Real.log (coveringNumber hTotallyBounded x))) := by
  exact dudley_entropy_integral_abs_of_neg_closed
    hε hTotallyBounded hn hNorm hεc hneg

/--
A sample-uniform Dudley estimate bounds expected Rademacher complexity:

`(∀ S, Dα(F,S) ≤ C) → Rₙ(F;μ) ≤ C`.
-/
theorem rademacher_complexity_le_dudley_of_uniform_entropy
    [Nonempty ι] [TopologicalSpace ι] [SeparableSpace ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (X : Ω → 𝒳)
    (hf : ∀ h, Measurable (f h ∘ X))
    {b c α C : ℝ} (hb : 0 ≤ b) (hf_bound : ∀ h x, |f h x| ≤ b)
    (hf_cont : ∀ x : 𝒳, Continuous fun h ↦ f h x)
    (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace f S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (h : ι), empiricalNorm S (f h) ≤ c)
    (hentropy : ∀ S : Fin n → 𝒳,
      dudleyEntropyEstimate f S (htb S) α c ≤ C) :
    rademacherComplexity n f μ X ≤ C := by
  apply rademacherComplexity_le_of_empirical_le_separable
    f X hf hb hf_bound hf_cont
  intro S
  exact (dudley_entropy_integral_bound_abs
    hα (htb S) hn (hnorm S) hαc).trans (hentropy S)

/--
A sample-uniform Dudley estimate yields

`Pr{UDₙ ≥ 2 C + ε} ≤ exp (-n ε² / (2b²))`.
-/
theorem uniform_deviation_tail_bound_separable_of_uniform_dudley
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ h, Measurable (f h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α C : ℝ} (hb : 0 < b) (hf_bound : ∀ h x, |f h x| ≤ b)
    (hf_cont : ∀ x : 𝒳, Continuous fun h ↦ f h x)
    (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace f S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (h : ι), empiricalNorm S (f h) ≤ c)
    (hentropy : ∀ S : Fin n → 𝒳,
      dudleyEntropyEstimate f S (htb S) α c ≤ C)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S |
      2 * C + ε ≤ uniformDeviation n f μ X (X ∘ S)}).toReal ≤
      (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  apply uniform_deviation_tail_bound_separable_of_empirical_le
    (F := f) hf X hX hb hf_bound hf_cont
  · intro S
    exact (dudley_entropy_integral_bound_abs
      hα (htb S) hn (hnorm S) hαc).trans (hentropy S)
  · exact hε

/--
Sample-dependent Dudley generalization estimate:

`Pr{UDₙ ≥ 2 Dα(F,S) + 3ε} ≤ 2 exp (-n ε² / (2b²))`.
-/
theorem uniform_deviation_tail_bound_separable_of_dudley
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ h, Measurable (f h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α : ℝ} (hb : 0 < b) (hf_bound : ∀ h x, |f h x| ≤ b)
    (hf_cont : ∀ x : 𝒳, Continuous fun h ↦ f h x)
    (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace f S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (h : ι), empiricalNorm S (f h) ≤ c)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (μⁿ {S : Fin n → Ω |
      2 * dudleyEntropyEstimate f (X ∘ S) (htb (X ∘ S)) α c +
        3 * ε ≤ uniformDeviation n f μ X (X ∘ S)}).toReal ≤
      2 * (-ε ^ 2 * n / (2 * b ^ 2)).exp := by
  exact
    uniform_deviation_tail_bound_separable_of_sample_empirical_le
      (μ := μ) f hf X hX
      (fun S ↦ dudleyEntropyEstimate f S (htb S) α c)
      hb hf_bound hf_cont
      (fun S ↦ dudley_entropy_integral_bound_abs
        hα (htb S) hn (hnorm S) hαc)
      hε

/--
Confidence form of the sample-dependent Dudley estimate:

`Pr{UDₙ ≥ 2 Dα(F,S) + 3b √(2 log(2/δ)/n)} ≤ δ`.
-/
theorem uniform_deviation_tail_bound_separable_of_dudley_delta
    [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ]
    (f : ι → 𝒳 → ℝ) (hf : ∀ h, Measurable (f h))
    (X : Ω → 𝒳) (hX : Measurable X)
    {b c α : ℝ} (hb : 0 < b) (hf_bound : ∀ h x, |f h x| ≤ b)
    (hf_cont : ∀ x : 𝒳, Continuous fun h ↦ f h x)
    (hn : 0 < n) (hα : 0 < α) (hαc : α < c / 2)
    (htb : ∀ S : Fin n → 𝒳,
      TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace f S)))
    (hnorm : ∀ (S : Fin n → 𝒳) (h : ι), empiricalNorm S (f h) ≤ c)
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) :
    (μⁿ {S : Fin n → Ω |
      2 * dudleyEntropyEstimate f (X ∘ S) (htb (X ∘ S)) α c +
        3 * (b * Real.sqrt (2 * Real.log (2 / δ) / n)) ≤
          uniformDeviation n f μ X (X ∘ S)}).toReal ≤ δ := by
  exact
    uniform_deviation_tail_bound_separable_of_sample_empirical_le_delta
      (μ := μ) hn f hf X hX
      (fun S ↦ dudleyEntropyEstimate f S (htb S) α c)
      hb hf_bound hf_cont
      (fun S ↦ dudley_entropy_integral_bound_abs
        hα (htb S) hn (hnorm S) hαc)
      hδ hδ_one

end
