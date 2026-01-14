import FoML.CoveringNumber

universe v
open scoped BigOperators
variable {Z : Type v}
variable {n : ℕ}

noncomputable def empiricalNorm (S : Fin n → Z) (f : Z → ℝ) : ℝ :=
  Real.sqrt ((1 / n) * ∑ i : Fin n, (f (S i)^2))

lemma empiricalNorm_def (S : Fin n → Z) (f : Z → ℝ) :
    empiricalNorm S f = Real.sqrt ((1 / n) * ∑ i : Fin n, (f (S i))^2) :=
  rfl

noncomputable def empiricalDist (S : Fin n → Z) (f g : Z → ℝ) : ℝ :=
  empiricalNorm S (f - g)

@[simp]
lemma empiricalDist_def (S : Fin n → Z) (f g : Z → ℝ) :
    empiricalDist S f g = empiricalNorm S (f - g) :=
  rfl

noncomputable def empiricalPMet (S : Fin n → Z) :
    PseudoMetricSpace (Z → ℝ) where
  dist := fun f g => empiricalDist S f g
  dist_self := by
    intro x; dsimp[empiricalDist]
    simp only [sub_self]; dsimp [empiricalNorm]; simp
  dist_comm := by
    intro x y
    dsimp[empiricalDist, empiricalNorm]
    grind
  dist_triangle := by
    intro x y z
    dsimp[empiricalDist,empiricalNorm]
    suffices Real.sqrt (∑ i, (x (S i) - z (S i)) ^ 2) ≤ Real.sqrt (∑ i, (x (S i) - y (S i)) ^ 2) + Real.sqrt (∑ i, (y (S i) - z (S i)) ^ 2) from by
      calc
      _ = √(1 / ↑n) * √(∑ i, (x (S i) - z (S i)) ^ 2) := by simp
      _ ≤ √(1 / ↑n) * (√(∑ i, (x (S i) - y (S i)) ^ 2) + √(∑ i, (y (S i) - z (S i)) ^ 2)) := by
        apply mul_le_mul
        · simp
        · exact this
        · apply Real.sqrt_nonneg
        simp
      _ = √(1 / ↑n) * √(∑ i, (x (S i) - y (S i)) ^ 2) + √(1 / ↑n) * √(∑ i, (y (S i) - z (S i)) ^ 2) := by apply LeftDistribClass.left_distrib
      _ = _ := by simp
    let xS : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ x (S i))
    let yS : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ y (S i))
    let zS : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ z (S i))
    calc
    _ = √(∑ i, (xS i - zS i) ^ 2) := by rfl
    _ = √(∑ i, ‖xS i - zS i‖ ^ 2) := by simp
    _ = ‖xS - zS‖ := Eq.symm (EuclideanSpace.norm_eq (xS - zS))
    _ ≤ ‖xS - yS‖ + ‖yS - zS‖ := norm_sub_le_norm_sub_add_norm_sub xS yS zS
    _ = _ := by
      apply Mathlib.Tactic.LinearCombination.add_eq_eq
      · calc
        _ = √(∑ i, ‖xS i - yS i‖ ^ 2) := EuclideanSpace.norm_eq (xS - yS)
        _ = √(∑ i, (xS i - yS i) ^ 2) := by simp
      · calc
        _ = √(∑ i, ‖yS i - zS i‖ ^ 2) := EuclideanSpace.norm_eq (yS - zS)
        _ = √(∑ i, (yS i - zS i) ^ 2) := by simp

@[simp]
lemma empiricalDist_app (S : Fin n → Z) (f g : Z → ℝ) :
    empiricalDist S f g = empiricalNorm S (f - g) :=
  rfl

@[simp] lemma empiricalDist_comm (S : Fin n → Z) (f g : Z → ℝ) :
    empiricalDist S f g = empiricalDist S g f := by
  letI := empiricalPMet S
  simpa [empiricalDist] using (dist_comm (x := f) (y := g))

lemma empiricalDist_proj (S : Fin n → Z) (f : Z → ℝ) (i : Fin n):
    |f (S i)|/√n ≤ empiricalNorm S f := by
  calc
  _ = √(f (S i)^2)/√n := by
    have : √(f (S i)^2) = |f (S i)| := by exact Real.sqrt_sq_eq_abs (f (S i))
    rw [this]
  _ = √((f (S i)^2)/n) := by
    simp
  _ ≤ _ := by
    dsimp [empiricalNorm]
    apply Real.sqrt_le_sqrt
    rw [one_div_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ ?_
    · have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ (f (S j))^2 := by
        intro j hj; exact sq_nonneg _
      have hi : i ∈ Finset.univ := by simp
      simpa using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun j => (f (S j))^2)
          hnonneg hi)
    · simp

section

universe u
variable {ι : Type u} {F : ι → Z → ℝ}
variable {S : Fin n → Z}

structure EmpiricalFunctionSpace (F : ι → Z → ℝ) (S : Fin n → Z) where
  index : ι

instance : CoeFun (EmpiricalFunctionSpace F S) (fun _ ↦ Z → ℝ) where
  coe f := F f.index

@[simp] lemma EmpiricalFunctionSpace.coe_apply
    (q : EmpiricalFunctionSpace F S) :
    (q : Z → ℝ) = F q.index := rfl

@[simps!]
noncomputable instance : Dist (EmpiricalFunctionSpace F S) where
  dist f g := empiricalDist S f g

noncomputable instance : PseudoMetricSpace (EmpiricalFunctionSpace F S) :=
  PseudoMetricSpace.induced (fun f ↦ F f.index) (empiricalPMet S)

end
