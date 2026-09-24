import Mathlib
-- import Architect  -- LeanArchitect (blueprint) not used in this repository

/-!
# Miscellaneous elementary lemmas missing from Mathlib

Monotonicity and sign of `log` on `ℕ` and on `ℕ∞` (through `ℝ≥0∞`, with the junk values
`log 0 = log ∞ = 0`): `log_natCast_le_log_natCast`, `log_toReal_toENNReal_nonneg`,
`log_toReal_toENNReal_mono`. All declarations live in the namespace `FoML.ToMathlib`.

This file depends only on Mathlib (`Architect` annotations are commented out).
-/

open scoped ENNReal

namespace FoML.ToMathlib

/-! ### Elementary facts about `log` of extended naturals -/

/- @[blueprint "lem:log-natCast-mono"
  (statement := /-- For natural numbers $m \le n$, $\log m \le \log n$ (with $\log 0 = 0$). -/)] -/
theorem log_natCast_le_log_natCast {m n : ℕ} (h : m ≤ n) : Real.log m ≤ Real.log n := by
  /- If $m = 0$ the left side is $0 \le \log n$; otherwise $\log$ is monotone on $(0,\infty)$. -/
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/- @[blueprint "lem:log-toReal-nonneg"
  (statement := /-- For $n \in \mathbb N \cup \{\infty\}$, $\log n \ge 0$ (with the conventions
    $\log 0 = \log \infty = 0$). -/)] -/
theorem log_toReal_toENNReal_nonneg (n : ℕ∞) : 0 ≤ Real.log (n : ℝ≥0∞).toReal := by
  /- Case split on $n = \infty$ (value $0$) and $n \in \mathbb N$ ($\log n \ge 0$). -/
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n => rw [ENat.toENNReal_coe, ENNReal.toReal_natCast]; exact Real.log_natCast_nonneg n

/- @[blueprint "lem:log-toReal-mono"
  (statement := /-- For $m \le n$ in $\mathbb N \cup \{\infty\}$ with $n < \infty$,
    $\log m \le \log n$. -/)] -/
theorem log_toReal_toENNReal_mono {m n : ℕ∞} (hn : n ≠ ⊤) (h : m ≤ n) :
    Real.log (m : ℝ≥0∞).toReal ≤ Real.log (n : ℝ≥0∞).toReal := by
  /- Both are natural numbers; apply monotonicity of $\log$ on $\mathbb N$. -/
  induction n using ENat.recTopCoe with
  | top => exact absurd rfl hn
  | coe n =>
    induction m using ENat.recTopCoe with
    | top => exact absurd (top_le_iff.1 h) (ENat.coe_ne_top n)
    | coe m =>
      rw [ENat.toENNReal_coe, ENat.toENNReal_coe, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
      exact log_natCast_le_log_natCast (by exact_mod_cast h)

end FoML.ToMathlib
