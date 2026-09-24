import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Covering and packing numbers: elementary facts missing from Mathlib

Complements to `Mathlib.Topology.MetricSpace.CoveringNumbers` (`Metric.coveringNumber`,
`Metric.externalCoveringNumber`, `Metric.packingNumber`: radius `ε : ℝ≥0`, closed balls, values
in `ℕ∞`), stated for arbitrary pseudo-emetric spaces:

* the packing/covering comparison `M(A, 2ε) ≤ N^ext(A, ε)`, `N(A, ε) ≤ M(A, ε)` and
  `N(A, 2ε) ≤ N^ext(A, ε)` (repackaging of Mathlib lemmas);
* the external covering number is attained by some cover;
* subadditivity `N^ext(A ∪ B, ε) ≤ N^ext(A, ε) + N^ext(B, ε)`;
* Lipschitz embeddings: a `K`-Lipschitz map sends `ε`-covers (resp. packings) to `Kε`-covers
  (resp. packings), so `N(φ(A), Kε) ≤ N(A, ε)` for the external / internal covering numbers and
  the packing number;
* a totally bounded set has finite covering numbers at every positive radius.

This file depends only on Mathlib (`Architect` annotations are commented out).
-/

open scoped NNReal ENNReal
open Metric

namespace FoML.ToMathlib

section Basic

variable {X : Type*} [PseudoEMetricSpace X]

/- @[blueprint "lem:packing-covering"
  (statement := /-- Packing and covering numbers are comparable:
    $M(A, 2\varepsilon) \le N^{\mathrm{ext}}(A, \varepsilon)$ and
    $N(A, \varepsilon) \le M(A, \varepsilon)$. -/)] -/
theorem packing_covering (ε : ℝ≥0) (A : Set X) :
    packingNumber (2 * ε) A ≤ externalCoveringNumber ε A ∧
      coveringNumber ε A ≤ packingNumber ε A :=
  ⟨packingNumber_two_mul_le_externalCoveringNumber ε A, coveringNumber_le_packingNumber ε A⟩

/- @[blueprint "lem:covering-le-external-two-mul"
  (statement := /-- $N(A, 2\varepsilon) \le N^{\mathrm{ext}}(A, \varepsilon)$. -/)] -/
theorem covering_two_mul_le_external (ε : ℝ≥0) (A : Set X) :
    coveringNumber (2 * ε) A ≤ externalCoveringNumber ε A :=
  coveringNumber_two_mul_le_externalCoveringNumber ε A

/- @[blueprint "lem:exists-external-cover"
  (statement := /-- The external covering number is attained: there is an $\varepsilon$-cover $C$
    of $A$ with $|C| = N^{\mathrm{ext}}(A, \varepsilon)$. -/)] -/
theorem exists_isCover_encard_eq_externalCoveringNumber (ε : ℝ≥0) (A : Set X) :
    ∃ C : Set X, IsCover ε A C ∧ C.encard = externalCoveringNumber ε A := by
  /- $\mathbb N \cup \{\infty\}$ is well-ordered, so the infimum over the nonempty family of
    covers is attained. -/
  have : Nonempty {C : Set X // IsCover ε A C} := ⟨⟨A, IsCover.rfl⟩⟩
  obtain ⟨C, hC⟩ :=
    ENat.exists_eq_iInf (fun C : {C : Set X // IsCover ε A C} => (C : Set X).encard)
  refine ⟨C, C.2, ?_⟩
  rw [hC, externalCoveringNumber, iInf_subtype]

/- @[blueprint "lem:subadditivity"
  (statement := /-- Subadditivity of the (external) covering number:
    $N^{\mathrm{ext}}(A \cup B, \varepsilon) \le N^{\mathrm{ext}}(A, \varepsilon)
    + N^{\mathrm{ext}}(B, \varepsilon)$. -/)] -/
theorem externalCoveringNumber_union_le (ε : ℝ≥0) (A B : Set X) :
    externalCoveringNumber ε (A ∪ B) ≤ externalCoveringNumber ε A + externalCoveringNumber ε B := by
  /- The union of an $\varepsilon$-cover of $A$ and an $\varepsilon$-cover of $B$ is an
    $\varepsilon$-cover of $A \cup B$; take the infimum over both covers. -/
  obtain ⟨C₁, hC₁, hC₁e⟩ := exists_isCover_encard_eq_externalCoveringNumber ε A
  obtain ⟨C₂, hC₂, hC₂e⟩ := exists_isCover_encard_eq_externalCoveringNumber ε B
  have hC : IsCover ε (A ∪ B) (C₁ ∪ C₂) := SetRel.IsCover.union hC₁ hC₂
  rw [← hC₁e, ← hC₂e]
  exact hC.externalCoveringNumber_le_encard.trans (Set.encard_union_le _ _)

end Basic

section LipschitzEmbedding

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/- @[blueprint "lem:lipschitz-embedding"
  (statement := /-- Let $\varphi : X \to Y$ be $K$-Lipschitz between pseudo-emetric spaces and
    $A \subseteq X$. Then for every $\varepsilon \ge 0$,
    $N^{\mathrm{ext}}(\varphi(A), K\varepsilon) \le N^{\mathrm{ext}}(A, \varepsilon)$. -/)] -/
theorem externalCoveringNumber_image_le {K : ℝ≥0} {φ : X → Y} (hφ : LipschitzWith K φ)
    (ε : ℝ≥0) (A : Set X) :
    externalCoveringNumber (K * ε) (φ '' A) ≤ externalCoveringNumber ε A := by
  /- The image of an $\varepsilon$-cover of $A$ is a $K\varepsilon$-cover of $\varphi(A)$ of no
    larger cardinality. -/
  simp only [externalCoveringNumber, le_iInf_iff]
  intro C hC
  exact (iInf₂_le (φ '' C) (hC.image_lipschitz hφ)).trans (Set.encard_image_le _ _)

/- @[blueprint "lem:lipschitz-embedding-internal"
  (statement := /-- With $\varphi$, $A$ as in the previous lemma, also
    $N(\varphi(A), K\varepsilon) \le N(A, \varepsilon)$ for the internal covering number. -/)] -/
theorem coveringNumber_image_le {K : ℝ≥0} {φ : X → Y} (hφ : LipschitzWith K φ)
    (ε : ℝ≥0) (A : Set X) :
    coveringNumber (K * ε) (φ '' A) ≤ coveringNumber ε A := by
  /- The image of an internal $\varepsilon$-cover of $A$ is an internal $K\varepsilon$-cover of
    $\varphi(A)$. -/
  simp only [coveringNumber, le_iInf_iff]
  intro C hCA hC
  refine (iInf_le _ (φ '' C)).trans ?_
  refine (iInf_le _ (Set.image_mono hCA)).trans ?_
  exact (iInf_le _ (hC.image_lipschitz hφ)).trans (Set.encard_image_le _ _)

/- @[blueprint "lem:lipschitz-embedding-packing"
  (statement := /-- With $\varphi$, $A$ as above, also
    $M(\varphi(A), K\varepsilon) \le M(A, \varepsilon)$ for the packing number
    (no assumption $K \ne 0$ is needed: if $K = 0$ every $K\varepsilon$-separated subset of
    $\varphi(A)$ is a singleton). -/)] -/
theorem packingNumber_image_le {K : ℝ≥0} {φ : X → Y} (hφ : LipschitzWith K φ)
    (ε : ℝ≥0) (A : Set X) :
    packingNumber (K * ε) (φ '' A) ≤ packingNumber ε A := by
  /- Given a $K\varepsilon$-separated $D \subseteq \varphi(A)$, choose a preimage $x_y \in A$ of
    each $y \in D$. For $y \ne z$, $K\varepsilon < d(y,z) \le K\, d(x_y, x_z)$ forces
    $\varepsilon < d(x_y, x_z)$, so $\{x_y\}$ is $\varepsilon$-separated, and $D$ is its image. -/
  simp only [packingNumber, iSup_le_iff]
  intro D hDA hD
  have hpre : ∀ y : D, ∃ x ∈ A, φ x = y := fun y => hDA y.2
  choose x hxA hxy using hpre
  have hD' : IsSeparated (ε : ℝ≥0∞) (Set.range x) := by
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ hne
    have hyz : (y : Y) ≠ z := fun h => hne (by rw [show y = z from Subtype.ext h])
    have h1 : ((K * ε : ℝ≥0) : ℝ≥0∞) < edist (y : Y) z := hD y.2 z.2 hyz
    have h2 : edist (y : Y) z ≤ K * edist (x y) (x z) := by
      rw [← hxy y, ← hxy z]; exact hφ.edist_le_mul _ _
    refine lt_of_not_ge fun hle => ?_
    have : (K : ℝ≥0∞) * edist (x y) (x z) ≤ K * ε := by gcongr
    rw [ENNReal.coe_mul] at h1
    exact absurd (h1.trans_le h2) (not_lt.mpr this)
  have hDimg : D = φ '' Set.range x := by
    ext y
    constructor
    · intro hy
      exact ⟨x ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hxy ⟨y, hy⟩⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      rw [hxy z]; exact z.2
  calc D.encard = (φ '' Set.range x).encard := congrArg Set.encard hDimg
    _ ≤ (Set.range x).encard := Set.encard_image_le _ _
    _ ≤ packingNumber ε A := hD'.encard_le_packingNumber (Set.range_subset_iff.mpr hxA)

end LipschitzEmbedding

section TotallyBounded

variable {X : Type*} [PseudoEMetricSpace X]

/- @[blueprint "lem:aa-external-covering-ne-top"
  (statement := /-- A totally bounded set has finite external covering numbers:
    if $A$ is totally bounded and $\varepsilon > 0$ then
    $N^{\mathrm{ext}}(A, \varepsilon) < \infty$. -/)] -/
theorem externalCoveringNumber_ne_top_of_totallyBounded {A : Set X} (hA : TotallyBounded A)
    {ε : ℝ≥0} (hε : 0 < ε) : externalCoveringNumber ε A ≠ ⊤ := by
  /- Total boundedness gives a finite set $t$ with $A \subseteq \bigcup_{y \in t} B(y,\varepsilon)$
    (open balls), hence $t$ is a finite $\varepsilon$-cover by closed balls. -/
  obtain ⟨t, ht, hAt⟩ := EMetric.totallyBounded_iff.1 hA ε (ENNReal.coe_pos.2 hε)
  have hcover : IsCover ε A t := by
    rw [isCover_iff_subset_iUnion_closedEBall]
    exact hAt.trans (Set.iUnion₂_mono fun _ _ => eball_subset_closedEBall)
  exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 ht) hcover.externalCoveringNumber_le_encard

/- @[blueprint "lem:aa-covering-ne-top"
  (statement := /-- A totally bounded set has finite (internal) covering numbers:
    if $A$ is totally bounded and $\varepsilon > 0$ then $N(A, \varepsilon) < \infty$. -/)] -/
theorem coveringNumber_ne_top_of_totallyBounded {A : Set X} (hA : TotallyBounded A)
    {ε : ℝ≥0} (hε : 0 < ε) : coveringNumber ε A ≠ ⊤ := by
  /- $N(A,\varepsilon) \le M(A,\varepsilon) = M(A, 2 \cdot \varepsilon/2)
    \le N^{\mathrm{ext}}(A, \varepsilon/2) < \infty$. -/
  refine ne_top_of_le_ne_top (externalCoveringNumber_ne_top_of_totallyBounded hA
    (ε := ε / 2) (by positivity)) ?_
  calc coveringNumber ε A ≤ packingNumber ε A := coveringNumber_le_packingNumber ε A
    _ = packingNumber (2 * (ε / 2)) A := by ring_nf
    _ ≤ externalCoveringNumber (ε / 2) A :=
      packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A

end TotallyBounded

end FoML.ToMathlib
