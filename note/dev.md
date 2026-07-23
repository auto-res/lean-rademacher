このプロジェクトは統計的学習理論の Lean 形式化プロジェクト lean-rademacher の公開版リポジトリです．

note/summary.md に現在のリポジトリの分析があります．
「9. 現状の接続関係と注意点」の指摘事項に対応したいです．

特に　9.1, 9.2 について， Rademacher複雑度による汎化評価定理と，Rademacher複雑度を評価する個別定理を接続したいです．
plan.md に計画を立ててください．

---

data/Mohri_FML.pdf に参考文献を追加しました．

$\forall S, \ \widehat{\mathfrak R}_n(f;S)\le C\Longrightarrow\mathfrak R_n(f;\mu,X)\le C$
というのは，よく使われる方法でしょうか．

例えば Mohri, Theorem 3.3 では別の論法で $\mathfrak R$ と $\widehat{\mathfrak R}$ に対する高確率評価を導出しているように見えます．

Dudley を活かすため， empirical Rademacher に対する高確率汎化評価を追加したいです．

統計的学習理論の典型的な notation に Lean の記号を合わせたいです．
特に，仮説空間の添字を ι と書くと，Rademacher複雑度の定義に現れる $\sup_{h \in H}$ が $\sup_{i \in \iota}$ となり，あまり見慣れない印象を受けます．とはいえ， $h : H$ とすると Lean において一般の項を表す記号が h なので，混乱を招きそうです．どのように修正するのがよいでしょうか．

リポジトリ全体を通じて，共通または類似の議論が多いと思います（複数のRademacherの書き換え，高確率評価と平均評価の書き換え，可分性への書き換えなど）．うまく bridge を使って補題を整理できますか．
これに限らず，リファクタリングの案があれば提案してください．

良いですね．まず plan.md に追記して，1-3 から着手してください．

- 再利用可能な補題は ForMathlib に移してください

10. Main.lean を簡潔にすることには賛成です．
ただし Main.lean は主要な使い方を示すために置いてあるので，単なる import の羅列ではなく，corollary or example で主要な定理を繰り返してください．代わりに docstring を少し充実させてください．例えば latex の数式も使ってください．

11. について，最後以外はただちに実施してください．Mathlib convention に基づく名前のつけ直しや，docstring の充実も図りたいです．

Main.lean には，UD を Rademacher で押さえる基本定理も掲載してください．いくつかバージョンがありますが，可分・高確率・経験Rademacherの組を例として挙げてください．

- FoML 配下のファイルが多くなってきたので，適当なサブディレクトリに分けてください． Main.lean や Defs.lean などは一番外側でよいです．

以下について，まず計画を立ててください:
- RKHS の場合（Mohri, Theorem 6.12）を実装したいです．
- 被複数を具体化してDudleyを評価する例がほしいです．
- 損失関数、ERM、余剰誤差まで含む評価を実装したいです．
