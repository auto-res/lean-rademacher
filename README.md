# Lean Formalization of Generalization Error Bound by Rademacher Complexity
[![arXiv](https://img.shields.io/badge/arXiv-2503.19605-b31b1b.svg)](https://arxiv.org/abs/2503.19605)

## Abstract
We formalize the generalization error bound using the Rademacher complexity for the Lean 4 theorem prover based on the probability theory in the Mathlib 4 library. Generalization error quantifies the gap between a learning machine's performance on given training data versus unseen test data, and the Rademacher complexity is a powerful tool to upper-bound the generalization error of a variety of modern learning problems. Previous studies have only formalized extremely simple cases such as bounds by parameter counts and analyses for very simple models (decision stumps). Formalizing the Rademacher complexity bound, also known as the uniform law of large numbers, requires substantial development and is achieved for the first time in this study. In the course of development, we formalize the Rademacher complexity and its unique arguments such as symmetrization, and clarify the topological assumptions on hypothesis classes under which the bound holds. As an application, we also present the formalization of generalization error bound for $L^2$-regularization models.

### Major updated:
(2026 Jan) We have formalized **Dudley's entropy integral bound** for Rademacher complexity for the first time.

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
