# Lean Formalization of Generalization Error Bound by Rademacher Complexity
[![arXiv](https://img.shields.io/badge/arXiv-2503.19605-b31b1b.svg)](https://arxiv.org/abs/2503.19605)

## Abstract
We formalize the generalization error bound using Rademacher complexity in the Lean 4 theorem
prover. Generalization error quantifies the gap between a learning machine’s performance on given
training data versus unseen test data, and Rademacher complexity serves as an estimate of this error
based on the complexity of learning machines, or hypothesis class. Unlike traditional methods such as
PAC learning and VC dimension, Rademacher complexity is applicable across diverse machine learning
scenarios including deep learning and kernel methods. We formalize key concepts and theorems, including
the empirical and population Rademacher complexities, and establish generalization error bounds through
formal proofs of McDiarmid’s inequality, Hoeffding’s lemma, and symmetrization arguments.

## How to Run
- Open a terminal. Run the following commands.
  ```bash
  git clone https://github.com/auto-res/lean-rademacher.git
  cd lean-rademacher

  # get Mathlib4 cache 
  lake exe cache get
  ```
- Launch VS code,
- open the folder ```lean-rademacher```,
- select the file ```FoML/Main.lean```, and
- push ```Restart File``` button to rebuild the project.
