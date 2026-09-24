import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Separability and first countability of `α →ᵤ β`

Facts about Mathlib's type `α →ᵤ β` of functions with the topology of uniform convergence
(`UniformFun`), missing from Mathlib:

* for a pseudo-metric space `β` the uniformity of `α →ᵤ β` is countably generated
  (`instIsCountablyGeneratedUniformFun`), hence `α →ᵤ β` is first countable and pseudo-metrizable,
  and so is every subtype;
* evaluation at a point is (uniformly) continuous (`continuous_toFun_apply`);
* a subset `𝓗 ⊆ α → ℝ` admitting a countable subset which is dense for the uniform norm is
  topologically separable in `α →ᵤ ℝ` (`isSeparable_preimage_toFun_of_sup_dense`), and the
  corresponding subtype is a `SeparableSpace` (`separableSpace_preimage_toFun_of_sup_dense`).

This file depends only on Mathlib (`Architect` annotations are commented out). The
declarations live in the namespace `FoML.ToMathlib` (they were extracted from
`FoML.ToFoML.UniformFunSeparable`, where they serve FoML's separable-class bounds).
-/

open Topology Filter TopologicalSpace
open scoped UniformConvergence Uniformity

namespace FoML.ToMathlib

variable {α β : Type*}

/- @[blueprint "lem:uniformfun-countably-generated"
  (statement := /-- For a pseudo-metric space $\beta$, the uniformity of uniform convergence on
    $\beta^\alpha$ is countably generated (it has the countable basis
    $\{(f,g) : \sup_x d(f(x),g(x)) < 1/(n+1)\}$, $n \in \mathbb N$); consequently
    $\alpha \to_u \beta$ is first countable and pseudo-metrizable. -/)] -/
instance instIsCountablyGeneratedUniformFun [PseudoMetricSpace β] :
    IsCountablyGenerated (𝓤 (α →ᵤ β)) :=
  (UniformFun.hasBasis_uniformity_of_basis α β
    Metric.uniformity_basis_dist_inv_nat_succ).isCountablyGenerated

/- @[blueprint "lem:uniformfun-eval-continuous"
  (statement := /-- Evaluation at a point $x$ is continuous on $\alpha \to_u \beta$ (it is even
    uniformly continuous). -/)] -/
theorem continuous_toFun_apply [UniformSpace β] (x : α) :
    Continuous fun f : α →ᵤ β => UniformFun.toFun f x :=
  (UniformFun.uniformContinuous_eval β x).continuous

/- @[blueprint "lem:sup-dense-isSeparable"
  (statement := /-- Let $\mathcal H \subseteq \mathbb R^{\alpha}$ and let
    $\mathcal D \subseteq \mathbb R^\alpha$ be countable and dense in $\mathcal H$ for the
    uniform norm: for every $f \in \mathcal H$ and $\varepsilon > 0$ there is
    $g \in \mathcal D$ with
    $\sup_x |f(x) - g(x)| \le \varepsilon$. Then $\mathcal H$, viewed as a subset of
    $\alpha \to_u \mathbb R$ (uniform convergence topology), is topologically separable:
    $\mathcal H \subseteq \overline{\mathcal D}$. -/)] -/
theorem isSeparable_preimage_toFun_of_sup_dense {𝓗 Dn : Set (α → ℝ)} (hc : Dn.Countable)
    (hdense : ∀ f ∈ 𝓗, ∀ ε > (0 : ℝ), ∃ g ∈ Dn, ∀ x, |f x - g x| ≤ ε) :
    IsSeparable (UniformFun.toFun ⁻¹' 𝓗 : Set (α →ᵤ ℝ)) := by
  /- The image of $\mathcal D$ under the identification $\alpha \to \alpha \to_u \mathbb R$ is
    countable; a basic neighbourhood of $f$ is $\{g : \forall x, |f(x) - g(x)| < \varepsilon\}$
    and contains the $\varepsilon/2$-approximant of $f$ in $\mathcal D$. -/
  refine ⟨UniformFun.ofFun '' Dn, hc.image _, fun f hf => ?_⟩
  rw [mem_closure_iff_nhds_basis
    (UniformFun.hasBasis_nhds_of_basis α ℝ f Metric.uniformity_basis_dist)]
  intro ε hε
  obtain ⟨g, hgD, hg⟩ := hdense (UniformFun.toFun f) hf (ε / 2) (by positivity)
  refine ⟨UniformFun.ofFun g, ⟨g, hgD, rfl⟩, ?_⟩
  simp only [Set.mem_setOf_eq, UniformFun.mem_gen, UniformFun.toFun_ofFun, Real.dist_eq]
  intro x
  exact (hg x).trans_lt (by linarith)

/- @[blueprint "lem:sup-dense-separableSpace"
  (statement := /-- Under the hypotheses of \texttt{lem:sup-dense-isSeparable}, the subtype
    $\mathcal H \subseteq \alpha \to_u \mathbb R$ with the topology of uniform convergence is a
    separable (and first countable) topological space. -/)] -/
theorem separableSpace_preimage_toFun_of_sup_dense {𝓗 Dn : Set (α → ℝ)} (hc : Dn.Countable)
    (hdense : ∀ f ∈ 𝓗, ∀ ε > (0 : ℝ), ∃ g ∈ Dn, ∀ x, |f x - g x| ≤ ε) :
    SeparableSpace (UniformFun.toFun ⁻¹' 𝓗 : Set (α →ᵤ ℝ)) :=
  (isSeparable_preimage_toFun_of_sup_dense hc hdense).separableSpace

/- Sanity check: every subtype of `α →ᵤ ℝ` is first countable. -/
example (𝓗 : Set (α → ℝ)) :
    FirstCountableTopology (UniformFun.toFun ⁻¹' 𝓗 : Set (α →ᵤ ℝ)) := inferInstance

end FoML.ToMathlib
