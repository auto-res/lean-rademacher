import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Notation

noncomputable
section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}

def Signs (n : ℕ) : Type := Fin n → ({-1, 1} : Finset ℤ)

instance : Fintype (Signs n) := inferInstanceAs (Fintype (Fin n → { x // x ∈ {-1, 1} }))

instance : Neg { x // x ∈ ({-1, 1} : Finset ℤ) } where
  neg x := ⟨-x.val, by
    cases x with
    | mk val h =>
      simp at h
      cases h
      · simp [*]
      · simp [*]
  ⟩

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}

set_option hygiene false

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

def empiricalRademacherComplexity (n : ℕ) (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)|

def rademacherComplexity (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳) : ℝ :=
  μⁿ[fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω)]

def empiricalRademacherComplexity_without_abs (n : ℕ) (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)

def uniformDeviation (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳) (S : Fin n → 𝒳) : ℝ :=
  ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, f i (S k) - μ[fun ω' ↦ f i (X ω')]|

end
