import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Hyperbolic-cosine inequalities in inner product spaces

Elementary facts missing from Mathlib, used for vector-valued Hoeffding / Pinelis inequalities:

* `u ↦ cosh √u` is convex on `[0, ∞)` (a power series with nonnegative coefficients);
* two-point majorization for convex functions on `[0, ∞)`;
* the Hilbert-space inequality
  `cosh(λ‖x+v‖) + cosh(λ‖x−v‖) ≤ 2 cosh(λ‖x‖) cosh(λ‖v‖)`
  (from the parallelogram identity, Cauchy–Schwarz and convexity of `u ↦ cosh √u`).

This file depends only on Mathlib (`Architect` annotations are commented out). The
declarations live in the namespace `FoML.ToMathlib` (they were extracted from
`FoML.ToFoML.VectorHoeffding`).
-/

open Real

namespace FoML.ToMathlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- @[blueprint "lem:convexOn-cosh-sqrt"
  (statement := /-- The function $u \mapsto \cosh\sqrt u$ is convex on $[0,\infty)$: indeed
    $\cosh\sqrt u = \sum_{k\ge0} u^k/(2k)!$ is a series of convex functions with nonnegative
    coefficients. -/)] -/
theorem convexOn_cosh_sqrt : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun u => Real.cosh (Real.sqrt u) := by
  have key : ∀ u : ℝ, 0 ≤ u →
      HasSum (fun k : ℕ => u ^ k / (Nat.factorial (2 * k) : ℝ)) (Real.cosh (Real.sqrt u)) := by
    intro u hu
    have := Real.hasSum_cosh (Real.sqrt u)
    simp only [pow_mul, Real.sq_sqrt hu] at this
    exact this
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : 0 ≤ x := hx
  have hy' : 0 ≤ y := hy
  simp only [smul_eq_mul]
  have hxy : 0 ≤ a * x + b * y := by positivity
  refine hasSum_le (fun k => ?_) (key _ hxy) (((key x hx').mul_left a).add ((key y hy').mul_left b))
  have hc := (convexOn_pow (𝕜 := ℝ) k).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hc
  calc (a * x + b * y) ^ k / (Nat.factorial (2 * k) : ℝ)
      ≤ (a * x ^ k + b * y ^ k) / (Nat.factorial (2 * k) : ℝ) := by gcongr
    _ = a * (x ^ k / (Nat.factorial (2 * k) : ℝ)) + b * (y ^ k / (Nat.factorial (2 * k) : ℝ)) := by
        ring

/- @[blueprint "lem:convex-two-point-majorize"
  (statement := /-- \textbf{Two-point majorization.} If $h$ is convex on $[0,\infty)$ and
    $0 \le y_2 \le x_2 \le x_1 \le y_1$ with $x_1 + x_2 = y_1 + y_2$, then
    $h(x_1) + h(x_2) \le h(y_1) + h(y_2)$. -/)] -/
theorem convexOn_two_point_majorize {h : ℝ → ℝ} (hh : ConvexOn ℝ (Set.Ici (0 : ℝ)) h)
    {x₁ x₂ y₁ y₂ : ℝ} (hy₂ : 0 ≤ y₂) (h21 : y₂ ≤ x₂) (h12 : x₂ ≤ x₁) (h1 : x₁ ≤ y₁)
    (hsum : x₁ + x₂ = y₁ + y₂) : h x₁ + h x₂ ≤ h y₁ + h y₂ := by
  rcases (sub_nonneg.mpr (h21.trans (h12.trans h1))).lt_or_eq with hd | hd
  · set θ : ℝ := (x₁ - y₂) / (y₁ - y₂) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
    have hθ1 : 0 ≤ 1 - θ := by
      rw [hθ, sub_nonneg, div_le_one hd]; linarith
    have hy₁ : y₁ ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]; linarith
    have hy₂' : y₂ ∈ Set.Ici (0 : ℝ) := hy₂
    have e1 : x₁ = θ * y₁ + (1 - θ) * y₂ := by
      rw [hθ]; field_simp; ring
    have e2 : x₂ = (1 - θ) * y₁ + θ * y₂ := by
      rw [hθ]; field_simp; linear_combination (y₁ - y₂) * hsum
    have c1 := hh.2 hy₁ hy₂' hθ0 hθ1 (by ring)
    have c2 := hh.2 hy₁ hy₂' hθ1 hθ0 (by ring)
    simp only [smul_eq_mul] at c1 c2
    rw [← e1] at c1
    rw [← e2] at c2
    linarith
  · have hy : y₁ = y₂ := by linarith
    have hx1 : x₁ = y₁ := by linarith
    have hx2 : x₂ = y₁ := by linarith
    rw [hx1, hx2, hy]

/- @[blueprint "lem:cosh-norm-add-sub-le"
  (statement := /-- \textbf{Key Hilbert-space inequality.} For $x, v$ in a real inner product
    space and $\lambda \in \mathbb R$,
    $$\cosh(\lambda\|x+v\|) + \cosh(\lambda\|x-v\|) \le 2\cosh(\lambda\|x\|)\cosh(\lambda\|v\|).$$
    Proof: with $a = \lambda\|x+v\|$, $b = \lambda\|x-v\|$, $p = \lambda\|x\|$,
    $q = \lambda\|v\|$ one has $a^2 + b^2 = (p+q)^2 + (p-q)^2$ and
    $|a^2 - b^2| = 4\lambda^2|\langle x, v\rangle| \le 4pq$ (Cauchy--Schwarz), so $(a^2, b^2)$ is
    majorized by $((p+q)^2, (p-q)^2)$; by convexity of $u \mapsto \cosh\sqrt u$,
    $\cosh a + \cosh b \le \cosh(p+q) + \cosh(p-q) = 2\cosh p\cosh q$. -/)] -/
theorem cosh_norm_add_add_cosh_norm_sub_le (x v : E) (l : ℝ) :
    Real.cosh (l * ‖x + v‖) + Real.cosh (l * ‖x - v‖) ≤
      2 * Real.cosh (l * ‖x‖) * Real.cosh (l * ‖v‖) := by
  wlog hl : 0 ≤ l generalizing l
  · simpa only [neg_mul, Real.cosh_neg] using this (-l) (by linarith)
  set h : ℝ → ℝ := fun u => Real.cosh (Real.sqrt u) with hh
  have hcosh : ∀ r : ℝ, 0 ≤ r → Real.cosh r = h (r ^ 2) := by
    intro r hr; simp only [hh]; rw [Real.sqrt_sq hr]
  have ha : 0 ≤ l * ‖x + v‖ := by positivity
  have hb : 0 ≤ l * ‖x - v‖ := by positivity
  have hrhs : 2 * Real.cosh (l * ‖x‖) * Real.cosh (l * ‖v‖) =
      h ((l * ‖x‖ + l * ‖v‖) ^ 2) + h ((l * ‖x‖ - l * ‖v‖) ^ 2) := by
    simp only [hh]
    rw [Real.sqrt_sq (by positivity), Real.sqrt_sq_eq_abs, Real.cosh_abs, Real.cosh_add,
      Real.cosh_sub]
    ring
  rw [hcosh _ ha, hcosh _ hb, hrhs]
  have hA := norm_add_sq_real x v
  have hB := norm_sub_sq_real x v
  have hip := abs_real_inner_le_norm x v
  rw [abs_le] at hip
  have hl2 : 0 ≤ l ^ 2 := sq_nonneg l
  have hsum : (l * ‖x + v‖) ^ 2 + (l * ‖x - v‖) ^ 2 =
      (l * ‖x‖ + l * ‖v‖) ^ 2 + (l * ‖x‖ - l * ‖v‖) ^ 2 := by
    rw [mul_pow, mul_pow, hA, hB]; ring
  have hy2 : 0 ≤ (l * ‖x‖ - l * ‖v‖) ^ 2 := sq_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hip.2 hl2
  have e2 := mul_le_mul_of_nonneg_left hip.1 hl2
  rcases le_total 0 (inner ℝ x v) with hip0 | hip0
  · have e3 := mul_le_mul_of_nonneg_left hip0 hl2
    refine convexOn_two_point_majorize convexOn_cosh_sqrt hy2 ?_ ?_ ?_ hsum
    · rw [mul_pow, hB]; nlinarith
    · rw [mul_pow, mul_pow, hA, hB]; nlinarith
    · rw [mul_pow, hA]; nlinarith
  · have e3 := mul_le_mul_of_nonneg_left hip0 hl2
    rw [add_comm (h ((l * ‖x + v‖) ^ 2))]
    refine convexOn_two_point_majorize convexOn_cosh_sqrt hy2 ?_ ?_ ?_
      (by rw [add_comm]; exact hsum)
    · rw [mul_pow, hA]; nlinarith
    · rw [mul_pow, mul_pow, hA, hB]; nlinarith
    · rw [mul_pow, hB]; nlinarith

end FoML.ToMathlib
