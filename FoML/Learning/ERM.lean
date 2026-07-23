import FoML.Learning.Defs
import FoML.ForMathlib.Analysis.FiniteSample

/-!
# Deterministic oracle inequalities for empirical risk minimization

The central result is the deterministic implication

`R(hhat) - R(hstar) ≤ 2 D + η`

whenever `hhat` is an `η`-approximate ERM and every empirical/population risk
discrepancy is at most `D`.  The uniform-deviation version is then a small
order-theoretic bridge.
-/

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Real

variable {n : ℕ}
variable {Ω : Type u} [MeasurableSpace Ω] {H : Type v} {𝒵 : Type w}
variable {μ : Measure Ω}

@[simp]
lemma isApproxERM_zero_iff_isERM
    (ℓ : H → 𝒵 → ℝ) (S : Fin n → 𝒵) (hhat : H) :
    IsApproxERM 0 n ℓ S hhat ↔ IsERM n ℓ S hhat := by
  simp [IsApproxERM, IsERM]

lemma IsERM.isApproxERM
    {ℓ : H → 𝒵 → ℝ} {S : Fin n → 𝒵} {hhat : H}
    (hERM : IsERM n ℓ S hhat) :
    IsApproxERM 0 n ℓ S hhat :=
  (isApproxERM_zero_iff_isERM ℓ S hhat).2 hERM

/--
Deterministic oracle inequality from a pointwise deviation estimate:

`R(hhat) - R(hstar) ≤ 2 D + η`.
-/
theorem IsApproxERM.excessRisk_le
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵} {S : Fin n → 𝒵}
    {hhat hstar : H} {η D : ℝ}
    (hERM : IsApproxERM η n ℓ S hhat)
    (hdev : ∀ h, riskDeviation n ℓ μ Z S h ≤ D) :
    excessRisk ℓ μ Z hhat hstar ≤ 2 * D + η := by
  have hhatDev := abs_le.mp (hdev hhat)
  have hstarDev := abs_le.mp (hdev hstar)
  have hopt := hERM hstar
  dsimp only [excessRisk]
  linarith

/--
Exact-ERM specialization of `IsApproxERM.excessRisk_le`.
-/
theorem IsERM.excessRisk_le
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵} {S : Fin n → 𝒵}
    {hhat hstar : H} {D : ℝ}
    (hERM : IsERM n ℓ S hhat)
    (hdev : ∀ h, riskDeviation n ℓ μ Z S h ≤ D) :
    excessRisk ℓ μ Z hhat hstar ≤ 2 * D := by
  simpa using hERM.isApproxERM.excessRisk_le (μ := μ) hdev

/--
Uniform deviation is definitionally the supremum of `riskDeviation`.
-/
lemma uniformDeviation_eq_iSup_riskDeviation
    (ℓ : H → 𝒵 → ℝ) (Z : Ω → 𝒵) (S : Fin n → 𝒵) :
    uniformDeviation n ℓ μ Z S =
      ⨆ h, riskDeviation n ℓ μ Z S h :=
  rfl

/--
Every pointwise risk discrepancy is at most uniform deviation, provided the
family of discrepancies is bounded above.
-/
lemma riskDeviation_le_uniformDeviation
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵} {S : Fin n → 𝒵}
    (hbounded :
      BddAbove (Set.range fun h ↦ riskDeviation n ℓ μ Z S h))
    (h : H) :
    riskDeviation n ℓ μ Z S h ≤ uniformDeviation n ℓ μ Z S := by
  rw [uniformDeviation_eq_iSup_riskDeviation]
  exact le_ciSup hbounded h

/--
The deterministic approximate-ERM oracle inequality in terms of uniform
deviation.
-/
theorem IsApproxERM.excessRisk_le_two_mul_uniformDeviation
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵} {S : Fin n → 𝒵}
    {hhat hstar : H} {η : ℝ}
    (hERM : IsApproxERM η n ℓ S hhat)
    (hbounded :
      BddAbove (Set.range fun h ↦ riskDeviation n ℓ μ Z S h)) :
    excessRisk ℓ μ Z hhat hstar ≤
      2 * uniformDeviation n ℓ μ Z S + η :=
  hERM.excessRisk_le (fun h ↦ riskDeviation_le_uniformDeviation hbounded h)

/--
The deterministic exact-ERM oracle inequality in terms of uniform deviation.
-/
theorem IsERM.excessRisk_le_two_mul_uniformDeviation
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵} {S : Fin n → 𝒵}
    {hhat hstar : H}
    (hERM : IsERM n ℓ S hhat)
    (hbounded :
      BddAbove (Set.range fun h ↦ riskDeviation n ℓ μ Z S h)) :
    excessRisk ℓ μ Z hhat hstar ≤
      2 * uniformDeviation n ℓ μ Z S := by
  simpa using
    hERM.isApproxERM.excessRisk_le_two_mul_uniformDeviation
      (μ := μ) (hstar := hstar) hbounded

/--
For a probability distribution and a loss bounded in absolute value by `b`,
each risk discrepancy is at most `2 * b`.
-/
lemma riskDeviation_le_two_mul
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵}
    (hℓ_meas : ∀ h, Measurable (ℓ h ∘ Z))
    {b : ℝ} (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (S : Fin n → 𝒵) (h : H) :
    riskDeviation n ℓ μ Z S h ≤ 2 * b := by
  have hmean : |populationRisk ℓ μ Z h| ≤ b := by
    dsimp only [populationRisk]
    calc
      |∫ x : Ω, ℓ h (Z x) ∂μ| ≤ ∫ x : Ω, |ℓ h (Z x)| ∂μ :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x : Ω, b ∂μ := by
        apply integral_mono
        · constructor
          · exact (hℓ_meas h).norm.aestronglyMeasurable
          · apply HasFiniteIntegral.of_mem_Icc
            filter_upwards
            intro x
            exact ⟨abs_nonneg _, hℓ_bound h (Z x)⟩
        · exact integrable_const b
        · exact fun x ↦ hℓ_bound h (Z x)
      _ = b := by simp
  have hsample : |empiricalRisk n ℓ S h| ≤ b := by
    exact abs_normalized_fin_sum_le hn (fun _ z ↦ ℓ h z) S
      (fun _ z ↦ hℓ_bound h z)
  dsimp only [riskDeviation]
  calc
    |empiricalRisk n ℓ S h - populationRisk ℓ μ Z h| ≤
        |empiricalRisk n ℓ S h| + |populationRisk ℓ μ Z h| :=
      abs_sub _ _
    _ ≤ b + b := add_le_add hsample hmean
    _ = 2 * b := by ring

/--
Bounded losses make the range of pointwise risk discrepancies bounded above.
-/
lemma bddAbove_range_riskDeviation
    [IsProbabilityMeasure μ]
    (hn : 0 < n)
    {ℓ : H → 𝒵 → ℝ} {Z : Ω → 𝒵}
    (hℓ_meas : ∀ h, Measurable (ℓ h ∘ Z))
    {b : ℝ} (hℓ_bound : ∀ h z, |ℓ h z| ≤ b)
    (S : Fin n → 𝒵) :
    BddAbove (Set.range fun h ↦ riskDeviation n ℓ μ Z S h) := by
  refine ⟨2 * b, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact riskDeviation_le_two_mul hn hℓ_meas hℓ_bound S h

end
