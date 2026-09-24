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
import FoML.ToFoML.BernoulliSudakovTools
import FoML.ToFoML.BernoulliSudakovCritical

/-!
# Bernoulli–Sudakov minoration: the multiscale iteration (B11)

Row B11 of the Bernoulli–Sudakov blueprint (lean-deepgen's `00note/sudakov-math.md`, §2 step S11, §4 item 6;
ULB pp. 186–187). We remove the diameter hypothesis `‖u_j‖₂ ≤ 2a` from the subset-selection
lemma `lem:bernoulli-subset-selection` (B9) and prove the unnormalised minoration

`b(u) ≥ (1/L₀) min(a √(log M), a²/b)`,   `L₀ := 8 L₂`,

for any `M ≥ 2`, `a, b > 0`, `‖u_j‖_∞ ≤ b` and `‖u_j − u_k‖₂ ≥ a` (`j ≠ k`).

**Proof.** Write `B := b(u) ≥ 0`. If `B ≥ a²/(8 L₂ b)` we are done, so assume
`B < a²/(8 L₂ b)`. View the `u_j` as points of `ℓ²(Fin n)` (`lem:euclidean-dist-eq`), let
`r₀ := a/2` and, for `k ∈ ℕ`, `a' := 2^k r₀ ≥ a/2`. Fix `t` and a `2^k r₀`-separated subfamily `J`
inside the closed `2^(k+1) r₀`-ball around `u_t`. Translating by `u_t` (shift invariance
`lem:bernoulli-sup-sub-const`, monotonicity `lem:bernoulli-sup-comp-injective`) the family
`(u_j − u_t)_{j ∈ J}` satisfies the hypotheses of B9 with `a'` and `b' := 2b`, hence
`min(a' √(log |J|), a'²/(2b)) / L₂ ≤ B` (`lem:bernoulli-pack-bound`). Since
`a'²/(2b L₂) ≥ a²/(8 L₂ b) > B` the minimum is the first term, and
`log |J| ≤ (L₂ B/a')² = 4 · 4^{-k} (L₂ B/a)²` (`lem:bernoulli-pack-log-bound`). Feeding
`κ_k := exp(4 · 4^{-k} C)`, `C := (L₂ B/a)²`, into the counting lemma
`lem:separated-net-counting` with `2^K r₀ ≥ 2b√n ≥ diam` gives
`M ≤ ∏_{k<K} κ_k = exp(C ∑_{k<K} 4 · 4^{-k}) ≤ exp(16 C/3)` (`lem:geom-sum-four-le`), i.e.
`a² log M ≤ (16/3) L₂² B²`, so `a √(log M)/(8 L₂) ≤ B/√12 ≤ B`.
-/

open Real
open scoped BigOperators

namespace FoML.ToFoML

variable {n : ℕ}

/-! ### The constant -/

/- @[blueprint "def:L0"
  (statement := /-- The constant of the multiscale iteration (and of the unnormalised
    Bernoulli–Sudakov minoration): $L_0 := 8 L_2 = 8\sqrt2\,L_3 = 73728\sqrt2 + 192
    \approx 1.04 \cdot 10^5$. -/)] -/
noncomputable def L₀ : ℝ := 8 * L₂

/- @[blueprint "lem:L0-pos"
  (statement := /-- $L_0 > 0$. -/)] -/
theorem L₀_pos : 0 < L₀ := by
  unfold L₀; have := L₂_pos; positivity

/-! ### One scale: the packing bound from subset selection -/

/- @[blueprint "lem:bernoulli-pack-bound"
  (statement := /-- \textbf{Packing bound at one scale.} Let $u_1,\dots,u_M \in \mathbb R^n$
    with $\|u_j\|_\infty \le b$, $b > 0$, let $t \le M$, $a' > 0$ and let $J \subseteq
    \{1,\dots,M\}$ with $|J| \ge 2$ satisfy $\|u_j - u_t\|_2^2 \le 4a'^2$ for $j \in J$ and
    $\|u_j - u_l\|_2^2 \ge a'^2$ for $j \ne l$ in $J$. Then
    $$ \frac{1}{L_2}\min\Bigl(a'\sqrt{\log|J|},\ \frac{a'^2}{2b}\Bigr) \le b(u). $$
    Proof: enumerate $J$ by $\{1,\dots,|J|\}$ and apply \texttt{lem:bernoulli-subset-selection}
    to the shifted family $(u_j - u_t)_{j \in J}$ (with $\|u_j - u_t\|_\infty \le 2b$); by
    \texttt{lem:bernoulli-sup-sub-const} and \texttt{lem:bernoulli-sup-comp-injective} its
    Bernoulli supremum is at most $b(u)$. -/)] -/
theorem bernoulli_pack_bound {M : ℕ} (u : Fin M → Fin n → ℝ) {b : ℝ} (hb : 0 < b)
    (hub : ∀ j i, |u j i| ≤ b) (t : Fin M) {a' : ℝ} (ha' : 0 < a') (J : Finset (Fin M))
    (hJ2 : 2 ≤ J.card) (hJball : ∀ j ∈ J, ∑ i, (u j i - u t i) ^ 2 ≤ 4 * a' ^ 2)
    (hJsep : ∀ j ∈ J, ∀ l ∈ J, j ≠ l → a' ^ 2 ≤ ∑ i, (u j i - u l i) ^ 2) :
    min (a' * √(Real.log J.card)) (a' ^ 2 / (2 * b)) / L₂ ≤ bernoulliSup u := by
  set e : Fin J.card → Fin M := fun m => J.orderEmbOfFin rfl m with he
  have hemem : ∀ m, e m ∈ J := fun m => J.orderEmbOfFin_mem rfl m
  have heinj : Function.Injective e := (J.orderEmbOfFin rfl).injective
  set w : Fin J.card → Fin n → ℝ := fun m i => u (e m) i - u t i with hw
  have hw2 : ∀ m, ∑ i, w m i ^ 2 ≤ 4 * a' ^ 2 := fun m => hJball (e m) (hemem m)
  have hwb : ∀ m i, |w m i| ≤ 2 * b := fun m i => by
    calc |w m i| = |u (e m) i - u t i| := rfl
      _ ≤ |u (e m) i| + |u t i| := abs_sub _ _
      _ ≤ b + b := add_le_add (hub _ _) (hub _ _)
      _ = 2 * b := by ring
  have hwsep : ∀ m m', m ≠ m' → a' ^ 2 ≤ ∑ i, (w m i - w m' i) ^ 2 := fun m m' hmm' => by
    have h := hJsep (e m) (hemem m) (e m') (hemem m') (heinj.ne hmm')
    simpa only [hw, sub_sub_sub_cancel_right] using h
  have hB9 := bernoulli_subset_selection hJ2 w ha' (by positivity) hw2 hwb hwsep
  have hshift : bernoulliSup w = bernoulliSup (u ∘ e) := bernoulliSup_sub_const (u ∘ e) (u t)
  calc min (a' * √(Real.log J.card)) (a' ^ 2 / (2 * b)) / L₂ ≤ bernoulliSup w := hB9
    _ = bernoulliSup (u ∘ e) := hshift
    _ ≤ bernoulliSup u := bernoulliSup_comp_le u e

/- @[blueprint "lem:bernoulli-pack-log-bound"
  (statement := /-- \textbf{Logarithmic packing bound below the critical level.} In the setting
    of \texttt{lem:bernoulli-pack-bound} with $a' := 2^k (a/2)$, $a > 0$, and assuming
    $b(u) < a^2/(8 L_2 b)$, every $J$ as there (of any cardinality) satisfies
    $$ |J| \le \exp\bigl(4 \cdot 4^{-k}\,C\bigr), \qquad C := \Bigl(\frac{L_2\,b(u)}{a}\Bigr)^2 . $$
    Proof: for $|J| \le 1$ this is trivial. Otherwise, since $a' \ge a/2$,
    $a'^2/(2b L_2) \ge a^2/(8L_2 b) > b(u)$, so the minimum in \texttt{lem:bernoulli-pack-bound}
    is attained by $a'\sqrt{\log|J|}$, whence $\log|J| \le (L_2 b(u)/a')^2 = 4 \cdot 4^{-k} C$. -/)] -/
theorem bernoulli_pack_log_bound {M : ℕ} (u : Fin M → Fin n → ℝ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hub : ∀ j i, |u j i| ≤ b)
    (hB : bernoulliSup u < a ^ 2 / (8 * L₂ * b)) (k : ℕ) (t : Fin M) (J : Finset (Fin M))
    (hJball : ∀ j ∈ J, ∑ i, (u j i - u t i) ^ 2 ≤ 4 * (2 ^ k * (a / 2)) ^ 2)
    (hJsep : ∀ j ∈ J, ∀ l ∈ J, j ≠ l → (2 ^ k * (a / 2)) ^ 2 ≤ ∑ i, (u j i - u l i) ^ 2) :
    (J.card : ℝ) ≤ Real.exp (4 * (1 / 4) ^ k * (L₂ * bernoulliSup u / a) ^ 2) := by
  haveI : Nonempty (Fin M) := ⟨t⟩
  have hL2 := L₂_pos
  have hBnn : 0 ≤ bernoulliSup u := bernoulliSup_nonneg u
  have hexp1 : 1 ≤ Real.exp (4 * (1 / 4) ^ k * (L₂ * bernoulliSup u / a) ^ 2) :=
    Real.one_le_exp (by positivity)
  rcases lt_or_ge J.card 2 with hJ | hJ2
  · calc (J.card : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hJ
      _ ≤ _ := hexp1
  set a' : ℝ := 2 ^ k * (a / 2) with ha'
  have ha'pos : 0 < a' := by positivity
  have ha'ge : a / 2 ≤ a' := by
    calc a / 2 = 1 * (a / 2) := (one_mul _).symm
      _ ≤ 2 ^ k * (a / 2) := by gcongr; exact one_le_pow₀ (by norm_num)
  have hpack := bernoulli_pack_bound u hb hub t ha'pos J hJ2 hJball hJsep
  -- the second branch of the minimum exceeds `b(u)`
  have hsecond : a ^ 2 / (8 * L₂ * b) ≤ a' ^ 2 / (2 * b) / L₂ := by
    calc a ^ 2 / (8 * L₂ * b) = (a / 2) ^ 2 / (2 * b) / L₂ := by field_simp; ring
      _ ≤ a' ^ 2 / (2 * b) / L₂ := by gcongr
  have hfirst : a' * √(Real.log J.card) / L₂ ≤ bernoulliSup u := by
    rw [← min_div_div_right hL2.le] at hpack
    rcases min_le_iff.mp hpack with h | h
    · exact h
    · linarith
  -- hence `log |J| ≤ (L₂ b(u) / a')²`
  have hN0 : (0 : ℝ) < J.card := by exact_mod_cast (show 0 < J.card by omega)
  have hsqrt : √(Real.log J.card) ≤ L₂ * bernoulliSup u / a' := by
    rw [div_le_iff₀ hL2] at hfirst
    rw [le_div_iff₀ ha'pos]
    linarith
  have hlog : Real.log J.card ≤ (L₂ * bernoulliSup u / a') ^ 2 :=
    (Real.sqrt_le_left (div_nonneg (mul_nonneg hL2.le hBnn) ha'pos.le)).mp hsqrt
  have h4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hC : (L₂ * bernoulliSup u / a') ^ 2 = 4 * (1 / 4) ^ k * (L₂ * bernoulliSup u / a) ^ 2 := by
    rw [ha', one_div_pow, h4]
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    field_simp
    ring
  rw [hC] at hlog
  exact (Real.log_le_iff_le_exp hN0).mp hlog

/-! ### B11: the multiscale iteration -/

/- @[blueprint "lem:bernoulli-multiscale"
  (statement := /-- \textbf{Unnormalised Bernoulli--Sudakov minoration} (ULB Thm.~6.4.1;
    blueprint S11, row B11). Let $M \ge 2$, $u_1,\dots,u_M \in \mathbb R^n$, $a, b > 0$ with
    $\|u_j\|_\infty \le b$ and $\|u_j - u_k\|_2^2 \ge a^2$ for $j \ne k$. Then
    $$ b(u) \ \ge\ \frac{1}{L_0}\min\Bigl(a\sqrt{\log M},\ \frac{a^2}{b}\Bigr), \qquad
       L_0 = 8 L_2 . $$
    Proof. If $b(u) \ge a^2/(8L_2 b)$ we are done. Otherwise apply the counting lemma
    \texttt{lem:separated-net-counting} in $\ell^2(\{1,\dots,n\})$ with $r_0 = a/2$,
    $\kappa_k = \exp(4\cdot4^{-k}C)$, $C = (L_2 b(u)/a)^2$ (\texttt{lem:bernoulli-pack-log-bound})
    and $2^K r_0 \ge 2b\sqrt n \ge \operatorname{diam}$: $M \le \exp(C\sum_{k<K}4\cdot4^{-k})
    \le \exp(16C/3)$ (\texttt{lem:geom-sum-four-le}), so $a^2\log M \le \frac{16}{3}L_2^2 b(u)^2$
    and $a\sqrt{\log M}/(8L_2) \le b(u)$. -/)] -/
theorem bernoulli_multiscale {M : ℕ} (hM : 2 ≤ M) (u : Fin M → Fin n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hub : ∀ j i, |u j i| ≤ b)
    (hsep : ∀ j k, j ≠ k → a ^ 2 ≤ ∑ i, (u j i - u k i) ^ 2) :
    min (a * √(Real.log M)) (a ^ 2 / b) / L₀ ≤ bernoulliSup u := by
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have hL2 := L₂_pos
  have hL0 := L₀_pos
  have hBnn : 0 ≤ bernoulliSup u := bernoulliSup_nonneg u
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  set B := bernoulliSup u with hBdef
  by_cases hB : a ^ 2 / (8 * L₂ * b) ≤ B
  · calc min (a * √(Real.log M)) (a ^ 2 / b) / L₀ ≤ a ^ 2 / b / L₀ := by
          gcongr; exact min_le_right _ _
      _ = a ^ 2 / (8 * L₂ * b) := by unfold L₀; field_simp
      _ ≤ B := hB
  push Not at hB
  -- the family as points of `ℓ²(Fin n)`
  set v : Fin M → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (u j) with hv
  have hdist : ∀ j l, dist (v j) (v l) = √(∑ i, (u j i - u l i) ^ 2) := fun j l =>
    dist_toLp_two_eq_sqrt_sum (u j) (u l)
  have hsep' : ∀ j l, j ≠ l → a ≤ dist (v j) (v l) := fun j l hjl => by
    rw [hdist]
    exact (Real.le_sqrt ha.le (Finset.sum_nonneg fun i _ => sq_nonneg _)).mpr (hsep j l hjl)
  have hdiam0 : ∀ j l, dist (v j) (v l) ≤ 2 * b * √n := fun j l => by
    rw [hdist]
    have h : ∑ i, (u j i - u l i) ^ 2 ≤ n * (2 * b) ^ 2 :=
      sum_sq_le_of_abs_le fun i => by
        calc |u j i - u l i| ≤ |u j i| + |u l i| := abs_sub _ _
          _ ≤ b + b := add_le_add (hub _ _) (hub _ _)
          _ = 2 * b := by ring
    calc √(∑ i, (u j i - u l i) ^ 2) ≤ √(n * (2 * b) ^ 2) := Real.sqrt_le_sqrt h
      _ = 2 * b * √n := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by positivity)]; ring
  -- a scale `K` beyond the diameter
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 * b * √n / (a / 2)) (by norm_num : (1 : ℝ) < 2)
  have hdiam : ∀ j l, dist (v j) (v l) ≤ 2 ^ K * (a / 2) := fun j l => by
    have ha2 : 0 < a / 2 := by positivity
    calc dist (v j) (v l) ≤ 2 * b * √n := hdiam0 j l
      _ = 2 * b * √n / (a / 2) * (a / 2) := by field_simp
      _ ≤ 2 ^ K * (a / 2) := by gcongr
  -- the counting lemma
  set C : ℝ := (L₂ * B / a) ^ 2 with hCdef
  have hC0 : 0 ≤ C := sq_nonneg _
  set κ : ℕ → ℝ := fun k => Real.exp (4 * (1 / 4) ^ k * C) with hκ
  have hpack : ∀ k < K, ∀ t, ∀ J : Finset (Fin M),
      (∀ j ∈ J, dist (v j) (v t) ≤ 2 ^ (k + 1) * (a / 2)) →
      (∀ j ∈ J, ∀ l ∈ J, j ≠ l → 2 ^ k * (a / 2) ≤ dist (v j) (v l)) → (J.card : ℝ) ≤ κ k := by
    intro k _ t J hJball hJsep
    refine bernoulli_pack_log_bound u ha hb hub hB k t J ?_ ?_
    · intro j hj
      have h := hJball j hj
      rw [hdist] at h
      have hsum : 0 ≤ ∑ i, (u j i - u t i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      calc ∑ i, (u j i - u t i) ^ 2 = (√(∑ i, (u j i - u t i) ^ 2)) ^ 2 :=
            (Real.sq_sqrt hsum).symm
        _ ≤ (2 ^ (k + 1) * (a / 2)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
        _ = 4 * (2 ^ k * (a / 2)) ^ 2 := by ring
    · intro j hj l hl hjl
      have h := hJsep j hj l hl hjl
      rw [hdist] at h
      have hsum : 0 ≤ ∑ i, (u j i - u l i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      calc (2 ^ k * (a / 2)) ^ 2 ≤ (√(∑ i, (u j i - u l i) ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h 2
        _ = ∑ i, (u j i - u l i) ^ 2 := Real.sq_sqrt hsum
  have hcount := card_le_prod_of_separated v (by positivity : (0 : ℝ) < a / 2)
    (by linarith : a / 2 < a) hsep' K κ hpack hdiam
  rw [Fintype.card_fin] at hcount
  -- `M ≤ exp(16 C / 3)`
  have hprod : ∏ k ∈ Finset.range K, κ k ≤ Real.exp (16 / 3 * C) := by
    calc ∏ k ∈ Finset.range K, κ k = Real.exp (∑ k ∈ Finset.range K, 4 * (1 / 4) ^ k * C) := by
          rw [Real.exp_sum]
      _ = Real.exp ((∑ k ∈ Finset.range K, 4 * (1 / 4) ^ k) * C) := by rw [Finset.sum_mul]
      _ ≤ Real.exp (16 / 3 * C) := by
          gcongr
          exact geom_sum_four_le K
  have hlogM' : Real.log M ≤ 16 / 3 * C :=
    (Real.log_le_iff_le_exp (by positivity)).mpr (hcount.trans hprod)
  -- conclude: `a √(log M) / (8 L₂) ≤ B`
  have hkey : a ^ 2 * Real.log M ≤ 16 / 3 * (L₂ * B) ^ 2 := by
    have : a ^ 2 * C = (L₂ * B) ^ 2 := by rw [hCdef]; field_simp
    calc a ^ 2 * Real.log M ≤ a ^ 2 * (16 / 3 * C) := by gcongr
      _ = 16 / 3 * (L₂ * B) ^ 2 := by rw [← this]; ring
  have hfinal : a * √(Real.log M) / L₀ ≤ B := by
    rw [div_le_iff₀ hL0]
    have hsq : (a * √(Real.log M)) ^ 2 ≤ (B * L₀) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlogM]
      unfold L₀
      nlinarith [sq_nonneg (L₂ * B)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  calc min (a * √(Real.log M)) (a ^ 2 / b) / L₀ ≤ a * √(Real.log M) / L₀ := by
        gcongr; exact min_le_left _ _
    _ ≤ B := hfinal

end FoML.ToFoML
