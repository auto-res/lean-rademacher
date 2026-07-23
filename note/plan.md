# Rademacher 複雑度評価と汎化評価を接続するための実装計画

## 1. 目的

`note/summary.md` の 9.1, 9.2 を解消し、次の流れを公開 API として利用できるようにする。

```text
固定標本ごとの経験 Rademacher 複雑度の上界
  → 標本について平均した Rademacher 複雑度の上界
  → 一様偏差の期待値評価・高確率評価
```

具体的な完了条件は次のとおりとする。

1. 固定標本上で一様な上界を、`rademacherComplexity` の上界へ持ち上げる共通補題がある。
2. その共通補題を用い、汎化評価の閾値に未知の
   `rademacherComplexity` ではなく既知の定数上界を代入できる。
3. $\ell_2$ 線形予測器と $\ell_1/\ell_\infty$ 線形予測器について、経験複雑度評価から汎化評価までを接続した公開定理がある。
4. Dudley entropy integral について、片側版の評価を絶対値付き経験 Rademacher 複雑度へ安全に移す定理がある。
5. Dudley の標本依存な右辺に標本一様な上界を仮定した場合、それを期待 Rademacher 複雑度および汎化評価へ接続できる。

既存の Rademacher 複雑度の定義、定数、および既存定理の主張は変更せず、補題と系を追加する方針とする。

## 2. 現状の型に由来する論点

### 2.1 経験量から期待量への移行

定義から

```lean
rademacherComplexity n f μ X =
  μⁿ[fun ω ↦ empiricalRademacherComplexity n f (X ∘ ω)]
```

である。したがって

```lean
∀ S, empiricalRademacherComplexity n f S ≤ C
```

と被積分関数の可積分性があれば、確率測度上の積分の単調性により

```lean
rademacherComplexity n f μ X ≤ C
```

を得られる。Lean の Bochner 積分は非可積分な関数に対しても値を持つため、非可積分時に積分が `0` となる仕様を利用して証明を短絡させず、共通補題では可積分性を明示する。

### 2.2 汎化評価の事象の包含

既存の高確率定理が評価する悪い事象は

```text
2 * rademacherComplexity n f μ X + ε ≤ uniformDeviation ...
```

である。`rademacherComplexity n f μ X ≤ C` なら

```text
{2 * C + ε ≤ uniformDeviation}
  ⊆
{2 * rademacherComplexity n f μ X + ε ≤ uniformDeviation}
```

なので、`measure_mono` によって既存の tail 評価をそのまま再利用できる。

### 2.3 線形予測器の定義域

既存の汎化定理は `∀ i x, |f i x| ≤ b` を関数の全定義域で仮定する。したがって、入力を周辺の Euclidean space 全体とした非自明な線形関数には直接適用できない。

end-to-end の定理では次の有界な部分型を入力空間および添字空間として使う。

- $\ell_2$ 版:
  - 入力: `Metric.closedBall 0 X`
  - 重み: `Metric.closedBall 0 W`
- $\ell_1/\ell_\infty$ 版:
  - 入力: `LinftyBall Xinf`
  - 重み: `L1Ball W`

既存の経験複雑度評価は部分型の値を周辺空間へ写して適用し、関数合成に関する経験 Rademacher 複雑度の等式で部分型版へ戻す。

### 2.4 Dudley の片側版

現在証明済みなのは

```lean
empiricalRademacherComplexity_without_abs n F S
  ≤ empiricalRademacherComplexity n F S
```

であり、この向きから Dudley の上界を絶対値付き版へ移すことはできない。

関数クラスを

```text
F± = {F i | i ∈ ι} ∪ {-F i | i ∈ ι}
```

と符号対称化すれば、各符号列について

```text
sup_i |A i| = sup_(i,s) s * A i
```

となる。この等式を Lean 上で明示的に証明してから、`F±` に既存の Dudley 定理を適用する。

## 3. 追加する共通補題

### 3.1 経験 Rademacher 複雑度の基本補題

`FoML/RademacherVariableProperty.lean` に以下を追加する。

1. 非負性

   ```lean
   empiricalRademacherComplexity_nonneg
   ```

   有限平均の係数、有限和の各項、絶対値の上限がすべて非負であることから示す。

2. 定義域の写像との可換性

   ```lean
   empiricalRademacherComplexity_comp
   ```

   想定する主張は次の形である。

   ```lean
   empiricalRademacherComplexity n
       (fun i x ↦ g i (q x)) S
     =
   empiricalRademacherComplexity n g (q ∘ S)
   ```

   線形予測器の部分型版を既存定理へ接続する際に使う。同様の補題が Dudley の符号対称化でも必要になれば、片側版についても追加する。

3. 可測性・可積分性

   可算添字、各 `f i ∘ X` の可測性、一様有界性の下で

   ```lean
   Measurable fun ω ↦
     empiricalRademacherComplexity n f (X ∘ ω)

   Integrable (fun ω ↦
     empiricalRademacherComplexity n f (X ∘ ω)) μⁿ
   ```

   を示す補題を追加する。既存の
   `measurable_signed_sup_sum_fst_core`,
   `abs_sum_sup_signed_le_pow_mul_bound` で使われている議論を正規化済みの定義へまとめ直す。

### 3.2 経験量から期待量への共通 bridge

`FoML/Rademacher.lean` に次の二段階の補題を追加する。

1. a.e. の上界を積分する一般形

   ```lean
   rademacherComplexity_le_of_ae_empirical_le
   ```

   主な仮定:

   - `[IsProbabilityMeasure μ]`
   - `Integrable (fun ω ↦ empiricalRademacherComplexity n f (X ∘ ω)) μⁿ`
   - `∀ᵐ ω ∂μⁿ, empiricalRademacherComplexity n f (X ∘ ω) ≤ C`

   結論:

   ```lean
   rademacherComplexity n f μ X ≤ C
   ```

2. 全固定標本に対する上界を受け取る簡便形

   ```lean
   rademacherComplexity_le_of_empirical_le
   ```

   主な仮定:

   - 上記の可積分性
   - `∀ S, empiricalRademacherComplexity n f S ≤ C`

   一般形に `Filter.Eventually.of_forall` を渡す薄い wrapper とする。

可算クラス用には、3.1 の可積分性補題から可積分性を自動で補う系も用意する。可分クラス用には `RademacherComplexity_eq` による稠密可算部分クラスへの還元を優先し、可積分性の重複証明を避ける。

## 4. 汎化評価側の共通 corollary

`FoML/Main.lean` に、既知の定数 `C` を閾値へ代入する公開定理を追加する。

候補名:

```lean
uniform_deviation_expectation_le_of_empirical_le_countable
uniform_deviation_expectation_le_of_empirical_le_separable
uniform_deviation_tail_bound_countable_of_empirical_le
uniform_deviation_tail_bound_separable_of_empirical_le
```

期待値版では既存の
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`
と `rademacherComplexity n f μ X ≤ C` を合成し、

```text
E[uniformDeviation] ≤ 2 * C
```

を示す。可分クラス版は既存の稠密可算化の等式を経由して導く。

まず定数を最適化済みの既存定理

```lean
uniform_deviation_tail_bound_countable_of_pos
uniform_deviation_tail_bound_separable_of_pos
```

に対応する版を実装する。必要性が確認できた場合のみ、自由な `t` を取る版も薄い wrapper として追加する。

主張の形は次のようにする。

```text
仮定:
  ∀ S, empiricalRademacherComplexity n f S ≤ C

結論:
  P(2 * C + ε ≤ uniformDeviation)
    ≤ exp(-n * ε^2 / (2 * b^2))
```

証明は次の二段階に限定する。

1. 3.2 により `rademacherComplexity n f μ X ≤ C` を示す。
2. 2.2 の事象包含と既存の tail 定理を使う。

この共通 corollary を個別モデルの定理から再利用し、モデルごとに積分・事象包含を再証明しない。

## 5. 線形予測器の end-to-end corollary

### 5.1 $\ell_2$ 線形予測器

`FoML/LinearPredictorL2.lean` に、入力と重みの両方を有界球の部分型として受け取る関数と経験評価 wrapper を追加する。

候補名:

```lean
linearPredictorL2
linear_predictor_l2_empirical_bound
```

設定:

```text
ι  = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W
𝒳  = Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) X
f w x = ⟪(w : EuclideanSpace ...), (x : EuclideanSpace ...)⟫
```

証明する評価:

```text
empiricalRademacherComplexity n f S
  ≤ X * W / sqrt n
```

既存の `linear_predictor_l2_bound'` と
`empiricalRademacherComplexity_comp` から導く。

続いて `FoML/Main.lean` に以下を公開する。

```lean
linear_predictor_l2_rademacher_complexity_bound
linear_predictor_l2_uniform_deviation_expectation_bound
linear_predictor_l2_uniform_deviation_tail_bound
```

前者:

```text
rademacherComplexity n f μ Z
  ≤ X * W / sqrt n
```

後者:

```text
P(2 * (X * W / sqrt n) + ε ≤ uniformDeviation)
  ≤ exp(-n * ε^2 / (2 * (X * W)^2))
```

主な仮定:

- `0 < n`, `0 < X`, `0 < W`
- `Z : Ω → Metric.closedBall 0 X`
- `Measurable Z`
- `[IsProbabilityMeasure μ]`

汎化定理に必要な一様有界性は Cauchy--Schwarz により

```text
|f w x| ≤ W * X
```

と示す。重み球が可分かつ第一可算であること、パラメータに関する連続性、入力に関する可測性を確認し、自然な非可算クラスなので可分クラス版の汎化定理を使う。

### 5.2 $\ell_1/\ell_\infty$ 線形予測器

`FoML/LinearPredictorL1.lean` に次を追加する。

```lean
linearPredictorL1
linear_predictor_l1_empirical_bound
```

設定:

```text
ι  = L1Ball W
𝒳  = LinftyBall Xinf
f w x = ∑ j, (w : EuclideanSpace ...) j * (x : EuclideanSpace ...) j
```

経験評価:

```text
empiricalRademacherComplexity n f S
  ≤ (Xinf * W / sqrt n) * sqrt (2 * log (2 * d))
```

既存の `linear_predictor_l1_bound'` と定義域写像の補題から導く。

`FoML/Main.lean` に以下を公開する。

```lean
linear_predictor_l1_rademacher_complexity_bound
linear_predictor_l1_uniform_deviation_expectation_bound
linear_predictor_l1_uniform_deviation_tail_bound
```

高確率評価の閾値には上の経験複雑度上界を、指数部の一様有界定数には

```text
b = Xinf * W
```

を使う。`abs_sum_mul_le_l1_mul` と部分型の条件から
`|f w x| ≤ Xinf * W` を示す。

主な仮定:

- `0 < d`, `0 < n`, `0 < Xinf`, `0 < W`
- `Z : Ω → LinftyBall Xinf`
- `Measurable Z`
- `[IsProbabilityMeasure μ]`

## 6. Dudley の絶対値付き版

### 6.1 符号対称化の定義と等式

`FoML/RademacherVariableProperty.lean` に、例えば

```lean
def signSymmetrization (F : ι → 𝒳 → ℝ) :
    ι × Bool → 𝒳 → ℝ
```

を追加し、`Bool` の一方を `F i`、他方を `-F i` とする。

固定標本上で関数値が一様有界という仮定の下で、条件付き上限が有限であることを明示して次を証明する。

```lean
empiricalRademacherComplexity_eq_without_abs_signSymmetrization
```

主張:

```lean
empiricalRademacherComplexity n F S
  =
empiricalRademacherComplexity_without_abs n
  (signSymmetrization F) S
```

`iSup` の書き換えでは上限有界性を省略しない。既存の
`empiricalRademacherComplexity_without_abs_le_empiricalRademacherComplexity`
を逆向きに使用しないことを証明レビューの確認項目とする。

併せて、もともと負号で閉じたクラス向けに

```lean
empiricalRademacherComplexity_eq_without_abs_of_neg_closed
```

を用意する。この場合はクラスを拡大せず、元の covering number をそのまま Dudley の右辺に使える。

### 6.2 empirical norm と total boundedness の移送

`FoML/PseudoMetric.lean` または `FoML/DudleyEntropy.lean` に以下を追加する。

1. `empiricalNorm S (-f) = empiricalNorm S f`
2. 正側・負側の
   `EmpiricalFunctionSpace F S` から
   `EmpiricalFunctionSpace (signSymmetrization F) S` への写像が isometry であること
3. 元の関数空間全体が totally bounded なら符号対称化後も totally bounded であること

候補名:

```lean
signSymmetrization_totallyBounded
```

正側と負側の像がそれぞれ totally bounded であり、その有限和集合が符号対称化後の全体になることから示す。この補題を名前付きで定義し、`coveringNumber` の引数となる total boundedness の証明項を安定させる。

### 6.3 絶対値付き Dudley 定理

`FoML/DudleyEntropy.lean` に内部定理、`FoML/Main.lean` に公開 wrapper を追加する。

候補名:

```lean
dudley_entropy_integral_abs
dudley_entropy_integral_bound_abs
```

基本形の結論:

```text
empiricalRademacherComplexity n F S
  ≤ 4 * ε
    + 12 / sqrt n
      * ∫ u in ε..c/2,
          sqrt (log (coveringNumber of signSymmetrization(F) at u))
```

証明順:

1. 6.1 の等式で絶対値付き経験量を符号対称化クラスの片側経験量へ変換する。
2. `empiricalNorm` の上界を `F` から `signSymmetrization F` へ移す。
3. 6.2 で total boundedness を移す。
4. 既存の `dudley_entropy_integral'` を適用する。

負号で閉じたクラスについては、符号対称化した covering number ではなく元の covering number を使う専用 corollary を追加する。

余力があれば、正負二つの cover を合併して

```text
N(signSymmetrization F, u) ≤ 2 * N(F, u)
```

も証明する。ただし、絶対値付き Dudley 定理の成立には必須とせず、core の接続を先に完了する。

## 7. Dudley から期待量・汎化評価への接続

Dudley の右辺は標本 `S` に依存するため、固定標本版だけから標本非依存の数値上界は得られない。公開 corollary では、この点を仮定として明示する。

以下を満たす標本非依存の `C` を受け取る。

```text
すべての S について
  4 * ε
    + 12 / sqrt n * entropyIntegral(signSymmetrization F, S)
  ≤ C
```

また、すべての `S` について Dudley の norm 条件と total boundedness 条件を仮定する。6.3 により

```lean
∀ S, empiricalRademacherComplexity n F S ≤ C
```

を作り、3.2 と 4 の共通定理へ渡す。

候補名:

```lean
rademacher_complexity_le_dudley_of_uniform_entropy
uniform_deviation_tail_bound_separable_of_uniform_dudley
```

この段階では、経験 Rademacher 複雑度そのものをランダムな閾値に置く data-dependent tail 定理は扱わない。それには経験複雑度の bounded-difference 評価など、現在の「期待 Rademacher 複雑度を使う汎化定理」とは別の確率評価が必要になる。

## 8. 実装順

### Phase 1: 共通 bridge

- [x] 経験 Rademacher 複雑度の非負性、写像補題、可測性、可積分性を追加する。
- [x] `rademacherComplexity_le_of_ae_empirical_le` を追加する。
- [x] 全標本上界を受け取る wrapper を追加する。
- [x] 可算・可分クラスの deterministic-threshold 期待値 corollary を追加する。
- [x] 可算・可分クラスの deterministic-threshold tail corollary を追加する。

この phase の完了時点で、任意の固定標本一様評価を汎化定理へ投入できるようになる。

### Phase 2: 線形予測器

- [x] $\ell_2$ 線形予測器の部分型版経験評価を追加する。
- [x] $\ell_2$ の期待 Rademacher 複雑度評価と高確率汎化評価を追加する。
- [x] $\ell_1/\ell_\infty$ 線形予測器の部分型版経験評価を追加する。
- [x] $\ell_1/\ell_\infty$ の期待 Rademacher 複雑度評価と高確率汎化評価を追加する。

### Phase 3: Dudley の絶対値付き版

- [ ] `signSymmetrization` と経験複雑度の等式を追加する。
- [ ] 負号で閉じたクラス用の等式を追加する。
- [ ] empirical norm と total boundedness を符号対称化へ移す。
- [ ] `dudley_entropy_integral_bound_abs` を公開する。
- [ ] 標本一様な entropy 上界から期待量・汎化評価を得る corollary を追加する。
- [ ] 必要に応じて covering number の係数 `2` の評価を追加する。

### Phase 4: 公開 API と文書

- [ ] `FoML/Main.lean` の docstring を、経験評価・期待評価・汎化評価の区別が分かる表現にする。
- [ ] `README.md` の selected contents に新しい end-to-end 定理を追加する。
- [ ] `note/summary.md` の 9.1, 9.2 を、解消済みの宣言名と残る仮定に合わせて更新する。

## 9. ファイルごとの変更予定

| ファイル | 変更内容 |
|---|---|
| `FoML/RademacherVariableProperty.lean` | 非負性、定義域写像、符号対称化、絶対値付き版と片側版の等式 |
| `FoML/Rademacher.lean` | 可測性・可積分性の整理、経験量上界から期待量上界への bridge |
| `FoML/PseudoMetric.lean` | `empiricalNorm` の負号不変性、必要なら符号対称化写像の距離補題 |
| `FoML/LinearPredictorL2.lean` | 有界入力部分型上の線形予測器と経験評価 wrapper |
| `FoML/LinearPredictorL1.lean` | `LinftyBall` 上の線形予測器と経験評価 wrapper |
| `FoML/DudleyEntropy.lean` | total boundedness の移送、絶対値付き Dudley 定理 |
| `FoML/Main.lean` | deterministic-threshold 汎化定理、線形予測器と Dudley の公開 corollary |
| `README.md`, `note/summary.md` | 新 API と接続関係の反映 |

循環 import が生じる場合は、符号対称化の一般補題だけを新しい小さなファイルへ分離する。最初から大きな新規モジュールを作ることは避ける。

## 10. 検証方針

各 phase で以下を実行する。

1. 変更した各ファイルを `lake env lean <file>` で個別に検査する。
2. `lake build` で公開入口 `FoML.lean` を含む全体を検査する。
3. `rg -n 'sorry|admit' FoML` で未完の証明が増えていないことを確認する。
4. `#check` または小さな利用例で、`FoML.Main` のみの import から新しい公開定理を適用できることを確認する。
5. 線形予測器の最終定理について、次を目視確認する。
   - 閾値の複雑度項が既存の経験評価の定数と一致する。
   - McDiarmid の指数部では関数値の一様上界 `X * W` または `Xinf * W` を使っている。
   - `0 < n` と正の半径条件が主張に明記されている。
6. Dudley について、片側版から絶対値付き版へ不等号を逆向きに使っていないことを確認する。

## 11. 想定される難所と対処

1. **`iSup` の上限有界性**

   符号対称化の等式では、`ℝ` 上の条件付き上限の補題が `BddAbove` を要求する。固定標本上の数値的な一様上界を補題の仮定に残し、無条件の書き換えとして証明しない。

2. **可分クラスの可積分性**

   非可算上限を直接可測としようとせず、既存の
   `empiricalRademacherComplexity_eq` と `RademacherComplexity_eq`
   により `denseSeq` 上の可算クラスへ還元する。

3. **`L1Ball`, `LinftyBall` の位相・可測構造**

   まず Euclidean space の部分型として既存 instance の推論を使う。推論できない性質だけを局所補題または instance として補い、型の定義自体は変更しない。

4. **`coveringNumber` が total boundedness の証明項を引数に持つこと**

   `signSymmetrization_totallyBounded` を名前付き補題にし、各所で異なる匿名証明を生成しない。必要な等式では proof irrelevance を明示して書き換える。

5. **`n = 0`**

   共通定義は `n = 0` でも保つが、平方根による具体評価と end-to-end の応用定理では `0 < n` を仮定する。`0⁻¹ = 0` に依存した見かけ上の自明化を応用 API へ露出させない。

6. **定数の二つの役割**

   経験複雑度の上界 `C` と、関数値の一様上界 `b` を混同しない。例えば $\ell_1$ 版では

   ```text
   C = (Xinf * W / sqrt n) * sqrt (2 * log (2 * d))
   b = Xinf * W
   ```

   であり、tail の閾値には `C`、指数部には `b` が現れる。
