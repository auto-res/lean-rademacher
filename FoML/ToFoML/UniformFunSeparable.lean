import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository
-- `import FoML` (root module) would be cyclic here; the root imports at the time of porting:
import FoML.Generalization.LinearPredictorL2
import FoML.Generalization.LinearPredictorL1
import FoML.Generalization.RKHS
import FoML.Generalization.Dudley
import FoML.Generalization.FiniteClass
import FoML.Generalization.LipschitzParameter
import FoML.Generalization.Learning
import FoML.Generalization.RKHSLearning
import FoML.Learning.Contraction
import FoML.Rademacher.Reindex
import FoML.ToMathlib.UniformFunSeparable

/-!
# Sup-norm separable function classes as FoML separable hypothesis classes

FoML's separable-class generalization bounds
(`uniform_deviation_tail_bound_separable_*`) are stated for an index type `H` carrying a
topology which is separable and first countable, together with pointwise continuity of the
evaluations `h ↦ F h x`. For a class `𝓗 ⊆ 𝒳 → ℝ` which is separable for the *uniform* norm we
realize these hypotheses by indexing the class by the subtype
`UniformFun.toFun ⁻¹' 𝓗 ⊆ (𝒳 →ᵤ ℝ)` of Mathlib's type `𝒳 →ᵤ ℝ` of functions with the topology
of uniform convergence. The required facts are Mathlib-generic and live in
`FoML.ToMathlib.UniformFunSeparable` (re-exported here through the import):

* the uniformity of `𝒳 →ᵤ ℝ` is countably generated (`instIsCountablyGeneratedUniformFun`),
  hence `𝒳 →ᵤ ℝ` is first countable and pseudo-metrizable, and so is every subtype;
* a countable subset which is dense for the uniform norm is topologically dense
  (`isSeparable_preimage_toFun_of_sup_dense`), so the subtype is a `SeparableSpace`
  (`separableSpace_preimage_toFun_of_sup_dense`);
* evaluation at a point is (uniformly) continuous (`continuous_toFun_apply`).

This file depends only on Mathlib, FoML and `FoML.ToMathlib`.
-/

open scoped UniformConvergence

open FoML.ToMathlib

namespace FoML.ToFoML

variable {α : Type*}

/- Sanity check: the FoML index type `UniformFun.toFun ⁻¹' 𝓗 ⊆ α →ᵤ ℝ` is first countable and,
under sup-norm density of a countable subclass, separable. -/
example {𝓗 Dn : Set (α → ℝ)} (hc : Dn.Countable)
    (hdense : ∀ f ∈ 𝓗, ∀ ε > (0 : ℝ), ∃ g ∈ Dn, ∀ x, |f x - g x| ≤ ε) :
    FirstCountableTopology (UniformFun.toFun ⁻¹' 𝓗 : Set (α →ᵤ ℝ)) ∧
      TopologicalSpace.SeparableSpace (UniformFun.toFun ⁻¹' 𝓗 : Set (α →ᵤ ℝ)) :=
  ⟨inferInstance, separableSpace_preimage_toFun_of_sup_dense hc hdense⟩

end FoML.ToFoML
