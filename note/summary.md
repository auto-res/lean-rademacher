# `lean-rademacher` の主要な定義・定理

最終確認日: 2026-07-20

## 0. 対象と全体像

この文書は、Lean project ``lean-rademahcer``　の local clone を整理したものである。確認したスナップショットは `main` branch、commit `f34ab4f0a9029682f1af3179a3fe9b5e114e511f`（2026-05-14）である。公開用の入口は [`FoML/Main.lean`](./lean-rademacher/FoML/Main.lean)、ライブラリ全体の入口は [`FoML.lean`](./lean-rademacher/FoML.lean) である。

プロジェクトの主な成果は次の四系統に分かれる。

1. **汎化誤差の共通パイプライン**: 一様偏差の期待値を symmetrization で Rademacher complexity に帰着し、McDiarmid の不等式で高確率評価にする。
2. **可算クラスから可分クラスへの拡張**: 非可算な仮説クラスの上限に伴う可測性の問題を、稠密可算部分クラスへの制限で解消する。
3. **線形予測器の具体例**: $\ell_2$ 制約では $O(n^{-1/2})$、$\ell_1/\ell_\infty$ 制約では $O(\sqrt{\log d/n})$ の経験 Rademacher complexity を示す。
4. **Dudley entropy integral**: 標本依存の擬距離、被覆数、Massart の補題、chaining を組み合わせ、一般の関数クラスを metric entropy で評価する。

概念上の依存関係は以下の通りである。

```text
Defs ─ Symmetrization ─ Rademacher ─ Main: expectation bound
                         └─ BoundedDifference ─┐
Moments ─ Hoeffding ─ McDiarmid ──────────────┼─ Main: countable tail bound
MeasurePiLemmas ──────────────────────────────┘
Main: countable tail bound + SeparableSpaceSup ─ Main: separable tail bound

Defs ─ RademacherVariableProperty ─ LinearPredictorL2
  └─ RademacherVariableProperty ─ Massart ─ LinearPredictorL1

CoveringNumber ─ PseudoMetric ─┐
Massart ───────────────────────┴─ DudleyEntropy
```

## 1. 共通の設定と記法

基本的な対象は以下である。

- $(\Omega,\mu)$: 基礎確率空間。主定理では `[IsProbabilityMeasure μ]` を仮定する。
- $X:\Omega\to\mathcal X$: 一つのデータ点を表す確率変数。
- $\iota$: 仮説またはパラメータの添字型。
- $f:\iota\to\mathcal X\to\mathbb R$: 関数クラス $\{f_i\}_{i\in\iota}$。
- $S:\operatorname{Fin}n\to\mathcal X$: サイズ $n$ の固定標本。
- $\omega:\operatorname{Fin}n\to\Omega$: 積空間上の点。ランダム標本は $X\circ\omega$ と表す。
- $\mu^n:=\operatorname{Measure.pi}(\lambda\_\Rightarrow\mu)$: i.i.d. 標本を生成する有限積測度。

同一分布の $n$ 標本を、独立性を別途仮定した $n$ 個の確率変数としてではなく、一つの $X$ と積測度 $\mu^n$ の座標射影で表している点が重要である。

## 2. 共通基盤

### 2.1 中心となる定義

定義は [`FoML/Defs.lean`](./lean-rademacher/FoML/Defs.lean) に集約されている。

#### `Signs`

```lean
def Signs (n : ℕ) : Type := Fin n → ({-1, 1} : Finset ℤ)
```

$n$ 個の Rademacher 符号を有限型として表す。`Signs.card` により

$$
|\operatorname{Signs}(n)|=2^n
$$

が証明されている。

#### `empiricalRademacherComplexity`

```lean
def empiricalRademacherComplexity
    (n : ℕ) (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ
```

絶対値付きの経験 Rademacher complexity:

$$
\widehat{\mathfrak R}_n(f;S)
=\frac1{2^n}\sum_{\sigma\in\{\pm1\}^n}
 \sup_{i\in\iota}
 \left|\frac1n\sum_{k=1}^n\sigma_k f_i(S_k)\right|.
$$

符号について別の確率空間を導入せず、有限型 `Signs n` 上の明示的な有限平均として定義される。

#### `rademacherComplexity`

```lean
def rademacherComplexity
    (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳) : ℝ
```

経験量を標本について平均した expected Rademacher complexity:

$$
\mathfrak R_n(f;\mu,X)
=\mathbb E_{\omega\sim\mu^n}
  \left[\widehat{\mathfrak R}_n(f;X\circ\omega)\right].
$$

#### `empiricalRademacherComplexity_without_abs`

```lean
def empiricalRademacherComplexity_without_abs ...
```

上限の中の絶対値を外した片側版:

$$
\widehat{\mathfrak R}^{\mathrm{noabs}}_n(f;S)
=\frac1{2^n}\sum_\sigma
 \sup_i\frac1n\sum_k\sigma_k f_i(S_k).
$$

Massart の補題と Dudley chaining はこの片側版を対象にする。一様有界性の下で

```lean
empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity
```

すなわち $\widehat{\mathfrak R}^{\mathrm{noabs}}_n\le\widehat{\mathfrak R}_n$ は証明されているが、逆向きではない。

#### `uniformDeviation`

```lean
def uniformDeviation
    (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω)
    (X : Ω → 𝒳) (S : Fin n → 𝒳) : ℝ
```

経験平均と母平均の一様偏差:

$$
\operatorname{UD}_n(f;\mu,X;S)
=\sup_{i\in\iota}
 \left|\frac1n\sum_{k=1}^n f_i(S_k)
       -\mathbb E_\mu[f_i(X)]\right|.
$$

学習後に標本依存で $i$ を選んでも、この量がクラス全体の汎化ギャップを同時に支配する。

### 2.2 積測度と独立性

[`FoML/MeasurePiLemmas.lean`](./lean-rademacher/FoML/MeasurePiLemmas.lean) は有限積測度の座標に関する共通補題を提供する。

| 宣言 | 内容 |
|---|---|
| `pi_map_eval` | $\mu^n$ を座標評価写像で push-forward すると元の $\mu$ になる。 |
| `pi_eval_iIndepFun` | $\mu^n$ 上の座標評価関数族が独立である。 |
| `pi_comp_eval_iIndepFun` | 座標評価に同じ可測写像 $X$ を合成しても独立性が保たれる。 |

これらが `mcdiarmid_inequality_pos'` の i.i.d. 積測度版、および標本平均と母平均の書き換えを支える。

### 2.3 Rademacher 符号の性質と PMF 版への橋渡し

[`FoML/RademacherVariableProperty.lean`](./lean-rademacher/FoML/RademacherVariableProperty.lean) の主要な宣言は以下である。

| 宣言 | 内容 |
|---|---|
| `rademacher_flip` | 一座標の符号を反転する involution。 |
| `sign_sum_eq_zero` | 各座標の符号の総和が $0$。 |
| `rademacher_orthogonality` | $k\ne l$ なら $\sum_\sigma\sigma_k\sigma_l=0$。 |
| `signVecPMF` | `Signs n` 上の一様確率質量関数。 |
| `empiricalRademacherComplexity_pmf` | 絶対値付き経験量の PMF 積分版。 |
| `empiricalRademacherComplexity_pmf_without_abs` | 片側経験量の PMF 積分版。 |
| `..._eq_..._pmf` | 明示的有限平均と PMF 積分が等しいことを示す二つの bridge lemma。 |

有限和で定義した基本量を、測度論的な maximal inequality や Massart の補題へ渡すための層である。

### 2.4 期待値・指数傾斜・Hoeffding の補題

[`FoML/ExpectationInequalities.lean`](./lean-rademacher/FoML/ExpectationInequalities.lean) は、一様なノルム上界から期待値のノルム上界を得る `norm_expectation_le_of_norm_le_const` と、その実数版 `abs_expectation_le_of_abs_le_const` を提供する。

[`FoML/ForMathlib/Probability/Moments.lean`](./lean-rademacher/FoML/ForMathlib/Probability/Moments.lean) は Mathlib 補完層であり、以下を証明する。

- 有界確率変数に対する指数関数の可積分性。
- exponential tilting 後の分散上界 `tilt_var_bound`。
- MGF と tilted expectation の微分公式 `tilt_first_deriv`, `tilt_second_deriv`。
- cumulant generating function の一階・二階微分 `cgf_deriv_one`, `cgf_deriv_two`。

これを用いて [`FoML/Hoeffding.lean`](./lean-rademacher/FoML/Hoeffding.lean) は `ProbabilityTheory.hoeffding` を証明する。$\mathbb E X=0$ かつ $a\le X\le b$ a.s. なら、全ての $t\in\mathbb R$ について

$$
\operatorname{mgf}_X(t)
\le \exp\!\left(\frac{t^2(b-a)^2}{8}\right).
$$

非負の $t$ に限定した `hoeffding_nonneg` と、CGF の二次上界 `cgf_le_quadratic_of_nonneg` も公開されている。

### 2.5 McDiarmid の不等式

[`FoML/McDiarmid.lean`](./lean-rademacher/FoML/McDiarmid.lean) は、条件付き期待値を primitive とせず、独立性と反復積分から McDiarmid の不等式を構成する。

主要な一般形 `mcdiarmid_inequality_pos` は、独立な確率変数族 $X_i$ と bounded-difference 条件

$$
|g(x)-g(x^{(i\leftarrow x')})|\le c_i
$$

の下で、$t\sum_i c_i^2\le1$, $\varepsilon\ge0$ なら

$$
\Pr\{g(X)-\mathbb Eg(X)\ge\varepsilon\}
\le \exp(-2\varepsilon^2t)
$$

を与える。

| 宣言 | 役割 |
|---|---|
| `mcdiarmid_inequality_pos` | 一般の独立・非同分布な有限族に対する上側 tail。 |
| `mcdiarmid_inequality_neg` | 下側 tail。 |
| `mcdiarmid_inequality_pos'` | 同じ $X$ を積測度の各座標に適用する i.i.d. 版。 |
| `bounded_difference_iff` | 絶対値付き感度条件と片側条件の同値。 |

### 2.6 可分空間上の上限

[`FoML/SeparableSpaceSup.lean`](./lean-rademacher/FoML/SeparableSpaceSup.lean) の中心は

```lean
theorem separableSpaceSup_eq_real ...
```

である。可分位相空間 $I$ 上の連続関数 $g:I\to\mathbb R$ に対して

$$
\sup_{i\in I}g(i)
=\sup_{m\in\mathbb N}g(\operatorname{denseSeq}(I,m))
$$

を示す。`closure_range_eq_closure_denseSeq` と `sSup_eq_closure_sSup` がその一般的な位相・順序論的基盤である。

## 3. 大定理 A: Rademacher complexity による汎化誤差評価

### 3.1 Symmetrization

[`FoML/Symmetrization.lean`](./lean-rademacher/FoML/Symmetrization.lean) の主結果は `symmetrization_equation` と `abs_symmetrization_equation` である。

後者は、ghost sample $(X'_k)$ を導入した差

$$
\sup_i\left|\sum_k(f_i(X_k)-f_i(X'_k))\right|
$$

の積測度上の期待値を、符号平均

$$
2^{-n}\sum_\sigma
\sup_i\left|\sum_k\sigma_k(f_i(X_k)-f_i(X'_k))\right|
$$

に等置する。`[Countable ι]`, `[Nonempty ι]`、各 $f_i\circ X$ の可測性、一様有界性を明示的に仮定する。

### 3.2 期待一様偏差の評価

[`FoML/Rademacher.lean`](./lean-rademacher/FoML/Rademacher.lean) の

```lean
theorem expectation_le_rademacher ...
```

は非正規化形

$$
\mathbb E\left[
 \sup_i\left|\sum_{k=1}^n f_i(X_k)
             -n\mathbb E f_i(X)\right|
\right]
\le 2n\,\mathfrak R_n(f;\mu,X)
$$

を証明する。`replace_mean_with_coordinate_mean` による母平均の積測度上への移送、ghost sample、`abs_symmetrization_equation`、二つの signed supremum の分離が主要な段階である。

[`FoML/Main.lean`](./lean-rademacher/FoML/Main.lean) はこれを利用者向けに正規化する。

```lean
theorem uniform_deviation_expectation_le_two_smul_rademacher_complexity ...
```

すなわち $n>0$ の下で

$$
\mathbb E_{S\sim\mu^n}[\operatorname{UD}_n(S)]
\le 2\mathfrak R_n(f;\mu,X).
$$

### 3.3 Bounded difference と一様偏差の可測性

[`FoML/BoundedDifference.lean`](./lean-rademacher/FoML/BoundedDifference.lean) は以下を提供する。

```lean
uniformDeviation_bounded_difference
```

$|f_i(x)|\le b$ なら、一標本だけを置き換えたとき

$$
|\operatorname{UD}_n(S)-\operatorname{UD}_n(S^{(k\leftarrow x')})|
\le\frac{2b}{n}.
$$

```lean
uniformDeviation_measurable
```

`[Countable ι]` かつ各 $f_i$ が可測なら、$S\mapsto\operatorname{UD}_n(S)$ が可測である。

### 3.4 可算仮説クラスの高確率定理

`FoML/Main.lean` ではまず平均のまわりの tail を示す。

```lean
uniform_deviation_mcdiarmid_tail
```

$t b^2\le1/2$ なら

$$
\Pr\{\operatorname{UD}_n-\mathbb E\operatorname{UD}_n\ge\varepsilon\}
\le \exp(-\varepsilon^2tn).
$$

これと期待値評価を合成した可算クラス版が

```lean
uniform_deviation_tail_bound_countable
```

であり、

$$
\Pr\{2\mathfrak R_n+\varepsilon\le\operatorname{UD}_n\}
\le \exp(-\varepsilon^2tn)
$$

を与える。`uniform_deviation_tail_bound_countable_of_pos` は $b>0$ のとき $t=1/(2b^2)$ を代入した形

$$
\boxed{
\Pr\{\operatorname{UD}_n\ge2\mathfrak R_n+\varepsilon\}
\le \exp\!\left(-\frac{n\varepsilon^2}{2b^2}\right)
}
$$

である。Lean の命題は「悪い事象」$2\mathfrak R_n+\varepsilon\le\operatorname{UD}_n$ の測度を `ENNReal.toReal` で実数に移して上から評価している。

### 3.5 可分仮説クラスへの拡張

`FoML/Main.lean` は $f$ を `f ∘ denseSeq ι` に制限しても三つの量が変わらないことを証明する。

| 宣言 | 等しい量 |
|---|---|
| `empiricalRademacherComplexity_eq` | 固定標本上の経験 Rademacher complexity。 |
| `RademacherComplexity_eq` | 標本について期待した Rademacher complexity。 |
| `uniformDeviation_eq` | 一様偏差。母平均のパラメータ連続性も必要。 |

最終的な `uniform_deviation_tail_bound_separable` と最適化形

```lean
uniform_deviation_tail_bound_separable_of_pos
```

は可算性 `[Countable ι]` の代わりに次を仮定する。

- `[TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]`。
- 各 $f_i:\mathcal X\to\mathbb R$ が可測。
- 各 $x$ に対して $i\mapsto f_i(x)$ が連続。
- $|f_i(x)|\le b$ の一様支配。

`FirstCountableTopology` は $i\mapsto\int f_i(X(\omega))\,d\mu$ の連続性を一様支配から導く `continuous_of_dominated` の適用に使われる。結論の定数は可算版と同じである。

固定標本について一様な評価

$$
\forall S,\qquad
\widehat{\mathfrak R}_n(f;S)\le C
$$

を期待量と汎化評価へ移す bridge も公開されている。

| 対象 | 可算クラス | 可分クラス |
|---|---|---|
| 期待 Rademacher complexity | `rademacherComplexity_le_of_empirical_le_countable` | `rademacherComplexity_le_of_empirical_le_separable` |
| 期待一様偏差 | `uniform_deviation_expectation_le_of_empirical_le_countable` | `uniform_deviation_expectation_le_of_empirical_le_separable` |
| 決定論的閾値の tail | `uniform_deviation_tail_bound_countable_of_empirical_le` | `uniform_deviation_tail_bound_separable_of_empirical_le` |

## 4. サブプロジェクト B: $\ell_2$ 制約付き線形予測器

実装は [`FoML/LinearPredictorL2.lean`](./lean-rademacher/FoML/LinearPredictorL2.lean)、公開 wrapper は `FoML/Main.lean` の

```lean
linear_predictor_l2_bound
```

である。

$Y_k\in\mathbb R^d$, $\|Y_k\|_2\le X$、$w_i\in\mathbb R^d$, $\|w_i\|_2\le W$ とすると、$f_i(x)=\langle w_i,x\rangle$ に対して

$$
\boxed{
\widehat{\mathfrak R}_n(f;Y)
\le \frac{XW}{\sqrt n}
}
$$

を示す。Lean では入力と重みを `Metric.closedBall 0 X`, `Metric.closedBall 0 W` の部分型として受け取る。

主な補題は以下である。

- `weighted_sum_norm_squared_expansion`: $\|\sum_k\sigma_kY_k\|^2$ を二重内積和に展開。
- `rademacher_sum_variance_zero`: `rademacher_orthogonality` により非対角交差項の符号平均が消える。
- Cauchy--Schwarz により符号平均を二乗平均で抑え、符号直交性を使って最終的に $X\sqrt n$ で抑える。

`linear_predictor_l2_bound` は固定標本ごとの **経験** Rademacher complexity の定理である。これを上記 bridge へ接続した公開定理として、期待量の
`linear_predictor_l2_rademacher_complexity_bound`、期待一様偏差の
`linear_predictor_l2_uniform_deviation_expectation_bound`、高確率汎化評価の
`linear_predictor_l2_uniform_deviation_tail_bound` がある。

## 5. サブプロジェクト C: $\ell_1/\ell_\infty$ 制約付き線形予測器

実装は [`FoML/LinearPredictorL1.lean`](./lean-rademacher/FoML/LinearPredictorL1.lean)、公開 wrapper は

```lean
linear_predictor_l1_bound
```

である。

### 5.1 幾何学的な定義

| 宣言 | 内容 |
|---|---|
| `l1Norm` | $\|w\|_1=\sum_j|w_j|$。 |
| `L1Ball W` | $\|w\|_1\le W$ を満たす Euclidean vector の部分型。 |
| `LinftyBall X` | 全座標で $|x_j|\le X$ を満たす部分型。 |
| `coordSigned` | $(j,\pm)$ に対応する signed coordinate $x\mapsto\pm x_j$。 |
| `abs_sum_mul_le_l1_mul` | $|\sum_jw_jz_j|\le\|w\|_1M$（各 $|z_j|\le M$）。 |

### 5.2 Maximal inequality と Massart の補題

[`FoML/MaximalInequality.lean`](./lean-rademacher/FoML/MaximalInequality.lean) の `ProbabilityTheory.maximal_inequality_supR` は、有限個の確率変数 $X_j=\sum_iY_{ij}$ について、各 $Y_{ij}$ が独立・平均 $0$・$|Y_{ij}|\le r_{ij}$ なら

$$
\mathbb E\max_jX_j
\le \max_j\sqrt{\sum_i r_{ij}^2}\,\sqrt{2\log N}
$$

を示す。期待値の **内側** で pointwise な有限上限を取る形なので、Massart の補題へ直接使える。

[`FoML/Massart.lean`](./lean-rademacher/FoML/Massart.lean) の `massart_lemma_pmf` は、有限な添字集合 $J$ に制限した片側 PMF 版経験 Rademacher complexity を

$$
\max_{j\in J}
\sqrt{\sum_{k=1}^n\left(\frac{|F_j(S_k)|}{n}\right)^2}
\sqrt{2\log|J|}
$$

で抑える。

### 5.3 $\ell_1$ 線形クラスの定理

$d,n>0$、$\|Y_k\|_\infty\le X_\infty$、$\|w_i\|_1\le W$ の下で

$$
\boxed{
\widehat{\mathfrak R}_n(f;Y)
\le
\frac{X_\infty W}{\sqrt n}\sqrt{2\log(2d)}
}
$$

を示す。証明は、サイズ $2d$ の signed-coordinate class に `massart_lemma_pmf` を適用し、$\ell_1/\ell_\infty$ duality で元の線形クラスをそこへ帰着する。

`linear_predictor_l1_bound` 自体は固定標本ごとの経験量である。期待量と汎化評価まで接続した
`linear_predictor_l1_rademacher_complexity_bound`,
`linear_predictor_l1_uniform_deviation_expectation_bound`,
`linear_predictor_l1_uniform_deviation_tail_bound` も公開されている。

## 6. サブプロジェクト D: Dudley entropy integral

### 6.1 標本依存の擬距離

[`FoML/PseudoMetric.lean`](./lean-rademacher/FoML/PseudoMetric.lean) は

```lean
empiricalNorm S f
empiricalDist S f g
EmpiricalFunctionSpace F S
```

を定義する。

$$
\|f\|_S
=\sqrt{\frac1n\sum_{k=1}^n f(S_k)^2},
\qquad
d_S(f,g)=\|f-g\|_S.
$$

標本点上で一致する異なる関数の距離は $0$ になり得るため metric ではなく pseudometric である。`EmpiricalFunctionSpace F S` は添字 $i:\iota$ を保持しつつ $F_i$ に coercion され、この擬距離を備える。

### 6.2 被覆数

[`FoML/CoveringNumber.lean`](./lean-rademacher/FoML/CoveringNumber.lean) は、totally bounded な集合 $A$ と $\varepsilon>0$ に対し、有限 $\varepsilon$-cover の最小要素数を `Nat.find` で選ぶ。

| 宣言 | 内容 |
|---|---|
| `coveringNumber` | $\varepsilon>0$ なら最小被覆数、$\varepsilon\le0$ なら $0$。 |
| `coveringNumber_antitone` | 正の半径上で $N(\varepsilon)$ は反単調。 |
| `coveringNumber_nonzero` | $A$ が非空かつ $\varepsilon>0$ なら $N(\varepsilon)>0$。 |
| `coveringNumber_aemeasurable` | Lebesgue 測度に関して a.e. measurable。 |
| `coveringFinset` | 最小被覆数を実現する有限中心集合の一つを選択。 |
| `coveringFinset_cover`, `coveringFinset_card` | 被覆性と要素数を保証。 |

ここで中心は ambient pseudometric space の点であり、定義上 `A` 自身に属することまでは要求していない。

### 6.3 Chaining と主定理

実装本体は [`FoML/DudleyEntropy.lean`](./lean-rademacher/FoML/DudleyEntropy.lean) である。内部では次の手順を形式化している。

1. dyadic radius $e_j=c/2^j$ を取る。
2. 各スケールで `coveringFinset` から近似 `coverApprox` を選ぶ。
3. `chainApprox` により $F_i$ を telescoping sum に分解する。
4. 残差を empirical distance で抑える（Part A）。
5. 各 increment が属する有限集合の要素数を、隣接二スケールの被覆数の積で抑える。
6. increment ごとに `massart_lemma_pmf` を適用する（Part B）。
7. dyadic sum を `AntitoneOn.leftRiemann_sum_le_integral` で entropy integral に移す。
8. `choose_dyadic_scale_for_epsilon` で $\varepsilon$ に合う打切りスケールを選ぶ。

中心定理 `dudley_entropy_integral'` と `FoML/Main.lean` の wrapper

```lean
dudley_entropy_integral_bound
```

は、$n>0$, $\varepsilon>0$, $\varepsilon<c/2$、

$$
\forall i,\quad \|F_i\|_S\le c,
$$

および `Set.univ : Set (EmpiricalFunctionSpace F S)` の total boundedness の下で

$$
\boxed{
\widehat{\mathfrak R}^{\mathrm{noabs}}_n(F;S)
\le 4\varepsilon
+\frac{12}{\sqrt n}
 \int_{\varepsilon}^{c/2}
   \sqrt{\log N(u)}\,du
}
$$

を示す。ここで $N(u)$ は empirical pseudometric による関数クラス全体の被覆数である。

絶対値付き経験量への接続には

```lean
signSymmetrization F
```

を用いる。これは各 $F_i$ と $-F_i$ を含むクラスであり、一様有界性の下で

$$
\widehat{\mathfrak R}_n(F;S)
=
\widehat{\mathfrak R}^{\mathrm{noabs}}_n
  (\operatorname{signSymmetrization}(F);S)
$$

が `empiricalRademacherComplexity_eq_without_abs_signSymmetrization` により示される。経験ノルムと経験距離は負号で不変であり、`signSymmetrization_totallyBounded` が元のクラスの total boundedness を符号対称化後へ移す。その結果、
`dudley_entropy_integral_abs` と公開 wrapper
`dudley_entropy_integral_bound_abs` は、符号対称化したクラスの被覆数を用いて
絶対値付き経験 Rademacher complexity を評価する。

元のクラスが `IsNegClosed F` を満たす場合は
`dudley_entropy_integral_bound_abs_of_neg_closed` により、クラスを拡大せず元の被覆数を使える。

## 7. `FoML/Main.lean` に集約された利用者向け宣言

| 分類 | 宣言 |
|---|---|
| 期待値評価 | `uniform_deviation_expectation_le_two_smul_rademacher_complexity` |
| McDiarmid tail | `uniform_deviation_mcdiarmid_tail` |
| 可算クラス | `uniform_deviation_tail_bound_countable`, `uniform_deviation_tail_bound_countable_of_pos` |
| 稠密可算化 | `empiricalRademacherComplexity_eq`, `RademacherComplexity_eq`, `uniformDeviation_eq` |
| 固定標本評価からの bridge | `rademacherComplexity_le_of_empirical_le_separable`, `uniform_deviation_tail_bound_separable_of_empirical_le` |
| 可分クラス | `uniform_deviation_tail_bound_separable`, `uniform_deviation_tail_bound_separable_of_pos` |
| $\ell_2$ 具体例 | `linear_predictor_l2_bound`, `linear_predictor_l2_rademacher_complexity_bound`, `linear_predictor_l2_uniform_deviation_tail_bound` |
| $\ell_1$ 具体例 | `linear_predictor_l1_bound`, `linear_predictor_l1_rademacher_complexity_bound`, `linear_predictor_l1_uniform_deviation_tail_bound` |
| Dudley | `dudley_entropy_integral_bound`, `dudley_entropy_integral_bound_abs` |
| 一様 Dudley 評価からの接続 | `rademacher_complexity_le_dudley_of_uniform_entropy`, `uniform_deviation_tail_bound_separable_of_uniform_dudley` |

抽象的な汎化定理としては、定数を最適化済みの `uniform_deviation_tail_bound_separable_of_pos` が再利用しやすい。固定標本の複雑度評価がある場合は `uniform_deviation_tail_bound_separable_of_empirical_le`、標本一様な Dudley entropy 評価がある場合は `uniform_deviation_tail_bound_separable_of_uniform_dudley` を使える。

## 8. ファイルごとの役割

| ファイル | 主な役割 |
|---|---|
| `Defs.lean` | 符号、二種類の経験 Rademacher complexity、期待 Rademacher complexity、一様偏差。 |
| `MeasurePiLemmas.lean` | 積測度の座標分布と独立性。 |
| `ExpectationInequalities.lean` | 一様上界から期待値の上界を得る補助定理。 |
| `ForMathlib/Probability/Moments.lean` | exponential tilting、MGF/CGF 微分、分散上界。 |
| `Hoeffding.lean` | Hoeffding の補題。 |
| `McDiarmid.lean` | 一般版・下側版・積測度版 McDiarmid。 |
| `Symmetrization.lean` | ghost sample と符号平均の symmetrization identity。 |
| `Rademacher.lean` | symmetrization から期待一様偏差評価まで。 |
| `BoundedDifference.lean` | 一様偏差の感度 $2b/n$ と可測性。 |
| `SeparableSpaceSup.lean` | 可分空間の上限を稠密可算列上の上限へ還元。 |
| `RademacherVariableProperty.lean` | 符号の直交性、PMF 版、有限平均との同値。 |
| `MaximalInequality.lean` | 有限個の sub-Gaussian 和の expected maximum。 |
| `Massart.lean` | PMF 版 Massart finite-class lemma。 |
| `LinearPredictorL2.lean` | $\ell_2$ 線形予測器。 |
| `LinearPredictorL1.lean` | $\ell_1/\ell_\infty$ 線形予測器。 |
| `CoveringNumber.lean` | 被覆数と最小被覆有限集合。 |
| `PseudoMetric.lean` | empirical seminorm/pseudometric と関数空間。 |
| `DudleyEntropy.lean` | dyadic chaining と entropy integral。 |
| `Main.lean` | 主要 theorem の組み立てと公開 wrapper。 |

`FoML/WIP/RademacherProperty.lean` は符号反転・直交性に関する旧/WIP 実装であり、`FoML.lean` からは import されない。現行の公開経路では `RademacherVariableProperty.lean` を参照すべきである。

## 9. 現状の接続関係と注意点

### 9.1 固定標本の具体評価から汎化定理への接続

この接続は実装済みである。全標本に共通する
`empiricalRademacherComplexity n f S ≤ C` を受け取る bridge により、期待
Rademacher complexity、期待一様偏差、決定論的閾値の tail 評価を得られる。
$\ell_2$ と $\ell_1/\ell_\infty$ の線形予測器については、経験評価から期待量・高確率汎化評価までを結合した専用定理も `Main.lean` に公開されている。

Dudley の右辺は一般には標本 $S$ に依存するため、接続定理
`rademacher_complexity_le_dudley_of_uniform_entropy` と
`uniform_deviation_tail_bound_separable_of_uniform_dudley` は、Dudley の norm 条件、total boundedness、および entropy integral の数値上界 $C$ が全標本で成立することを明示的に仮定する。経験複雑度そのものをランダムな閾値とする data-dependent tail 定理は、この API の対象外である。

### 9.2 Dudley の片側版と絶対値付き版

従来の `dudley_entropy_integral_bound` の左辺は
`empiricalRademacherComplexity_without_abs` である。比較補題

$$
\widehat{\mathfrak R}^{\mathrm{noabs}}_n
\le \widehat{\mathfrak R}_n
$$

だけを逆向きに使うことはできない。この問題は符号対称化による等式と total boundedness の移送で解消され、
`dudley_entropy_integral_bound_abs` が絶対値付き経験 Rademacher complexity を直接評価する。右辺の被覆数は `signSymmetrization F` に対するものである。`IsNegClosed F` の場合は
`dudley_entropy_integral_bound_abs_of_neg_closed` により元のクラスの被覆数をそのまま使える。

### 9.3 $n=0$ と正値条件

Lean の実数では $0^{-1}=0$ なので定義自体は $n=0$ でも総関数だが、正規化した期待値定理、線形予測器、Dudley など本質的に除算・平方根を使う結果は $0<n$ を仮定する。tail theorem の一部は $n=0$ を確率 $\le1$ の自明な場合として内部処理する。

### 9.4 主な未実装の応用層

README の future plans と現行 import graph から、少なくとも以下はまだ主要 API に含まれない。

- Lipschitz loss に対する contraction inequality。
- RKHS の具体的な complexity bound。
- Lipschitz 関数、ニューラルネットワーク等の具体的な covering-number estimate。

したがって現状のプロジェクトは、**汎化誤差の抽象パイプライン**に加え、線形予測器と標本一様な Dudley entropy 評価については **経験評価から汎化評価までの接続**も形式化した構成になっている。
