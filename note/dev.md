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
