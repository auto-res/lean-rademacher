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
import FoML.ToMathlib.CoveringNumber

/-!
# Bridge between Mathlib's and FoML's covering numbers

Mathlib (`Mathlib.Topology.MetricSpace.CoveringNumbers`) defines
`Metric.externalCoveringNumber ε A : ℕ∞` (`ε : ℝ≥0`, covers by *closed* balls, centres anywhere),
while FoML (`FoML.Entropy.CoveringNumber`) defines, for a totally bounded set `A` in a
pseudometric space, `coveringNumber (ha : TotallyBounded A) (ε : ℝ) : ℕ` as the minimal
cardinality of a finite external cover by *open* balls (and `0` for `ε ≤ 0`).

This file proves the two comparison inequalities (closed `ε'`-balls with `ε' < ε` are contained in
open `ε`-balls, and open `ε`-balls in closed `ε`-balls) and that finiteness of all external
covering numbers implies total boundedness. It depends only on Mathlib, FoML and
`FoML.ToMathlib.CoveringNumber` (for `exists_isCover_encard_eq_externalCoveringNumber`).
-/

open scoped NNReal ENNReal
open Metric

open FoML.ToMathlib

namespace FoML.ToFoML

variable {X : Type*} [PseudoMetricSpace X] {A : Set X}

/- @[blueprint "lem:foml-covering-le-external"
  (statement := /-- Let $A$ be totally bounded and $0 \le \varepsilon' < \varepsilon$. Then FoML's
    open-ball covering number is dominated by Mathlib's closed-ball external covering number:
    $N^{\mathrm{open}}(A, \varepsilon) \le N^{\mathrm{ext}}(A, \varepsilon')$
    (a closed $\varepsilon'$-ball is contained in the open $\varepsilon$-ball with the same
    centre). -/)] -/
theorem coveringNumber_le_externalCoveringNumber (ha : TotallyBounded A) (ε ε' : ℝ≥0)
    (hε : ε' < ε) :
    (coveringNumber ha ε : ℕ∞) ≤ externalCoveringNumber ε' A := by
  /- If the external covering number is infinite there is nothing to prove. Otherwise take a
    minimal closed $\varepsilon'$-cover $C$; it is finite, and every closed $\varepsilon'$-ball is
    contained in the open $\varepsilon$-ball with the same centre, so $C$ is a finite open
    $\varepsilon$-cover, and FoML's covering number is at most $|C|$. -/
  by_cases htop : externalCoveringNumber ε' A = ⊤
  · rw [htop]; exact le_top
  obtain ⟨C, hC, hCe⟩ := exists_isCover_encard_eq_externalCoveringNumber ε' A
  have hfin : C.Finite := Set.encard_ne_top_iff.mp (hCe ▸ htop)
  have hεpos : (0 : ℝ) < ε := lt_of_le_of_lt ε'.coe_nonneg (by exact_mod_cast hε)
  have hcover : A ⊆ ⋃ y ∈ hfin.toFinset, Metric.ball y ε := by
    intro x hx
    have := (isCover_iff_subset_iUnion_closedBall.mp hC) hx
    simp only [Set.mem_iUnion, exists_prop] at this ⊢
    obtain ⟨y, hy, hxy⟩ := this
    refine ⟨y, hfin.mem_toFinset.mpr hy, ?_⟩
    exact Metric.closedBall_subset_ball (by exact_mod_cast hε) hxy
  have h1 := coveringNumber_le_card_of_cover ha hεpos hfin.toFinset hcover
  calc (coveringNumber ha ε : ℕ∞) ≤ (hfin.toFinset.card : ℕ∞) := by exact_mod_cast h1
    _ = C.encard := (hfin.encard_eq_coe_toFinset_card).symm
    _ = externalCoveringNumber ε' A := hCe

/- @[blueprint "lem:external-le-foml-covering"
  (statement := /-- Let $A$ be totally bounded and $\varepsilon > 0$. Then Mathlib's closed-ball
    external covering number is dominated by FoML's open-ball covering number:
    $N^{\mathrm{ext}}(A, \varepsilon) \le N^{\mathrm{open}}(A, \varepsilon)$
    (an open ball is contained in the closed ball of the same radius). -/)] -/
theorem externalCoveringNumber_le_coveringNumber (ha : TotallyBounded A) (ε : ℝ≥0)
    (hε : 0 < ε) :
    externalCoveringNumber ε A ≤ coveringNumber ha ε := by
  /- FoML's minimal open $\varepsilon$-cover `coveringFinset` is a closed $\varepsilon$-cover. -/
  have hεpos : (0 : ℝ) < ε := by exact_mod_cast hε
  have hcov : IsCover ε A (↑(coveringFinset ha hεpos) : Set X) := by
    rw [isCover_iff_subset_iUnion_closedBall]
    intro x hx
    have := coveringFinset_cover ha hεpos hx
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_coe] at this ⊢
    obtain ⟨y, hy, hxy⟩ := this
    exact ⟨y, hy, Metric.ball_subset_closedBall hxy⟩
  calc externalCoveringNumber ε A ≤ (↑(coveringFinset ha hεpos) : Set X).encard :=
        hcov.externalCoveringNumber_le_encard
    _ = ((coveringFinset ha hεpos).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ = (coveringNumber ha ε : ℕ∞) := by rw [coveringFinset_card]

/- @[blueprint "lem:totallyBounded-of-covering-finite"
  (statement := /-- If $N^{\mathrm{ext}}(A, \varepsilon) < \infty$ for every $\varepsilon > 0$
    then $A$ is totally bounded. -/)] -/
theorem totallyBounded_of_externalCoveringNumber_ne_top
    (h : ∀ ε : ℝ≥0, 0 < ε → externalCoveringNumber ε A ≠ ⊤) : TotallyBounded A := by
  /- For $\varepsilon > 0$ a finite closed $\varepsilon/2$-cover is a finite open
    $\varepsilon$-cover. -/
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set ε' : ℝ≥0 := Real.toNNReal (ε / 2) with hε'
  have hε'pos : 0 < ε' := Real.toNNReal_pos.mpr (by linarith)
  have hcoe : (ε' : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
  obtain ⟨C, hC, hCe⟩ := exists_isCover_encard_eq_externalCoveringNumber ε' A
  refine ⟨C, Set.encard_ne_top_iff.mp (hCe ▸ h ε' hε'pos), ?_⟩
  intro x hx
  have := (isCover_iff_subset_iUnion_closedBall.mp hC) hx
  simp only [Set.mem_iUnion, exists_prop] at this ⊢
  obtain ⟨y, hy, hxy⟩ := this
  refine ⟨y, hy, Metric.closedBall_subset_ball ?_ hxy⟩
  rw [hcoe]
  linarith

end FoML.ToFoML
