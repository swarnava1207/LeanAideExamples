import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect "http://drongo:8042"

/-
### Theorem:
Let $A$ be the $2 \times 2$ matrix:$$A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$$.
Prove that for all integers $n \ge 1$, the $n$-th power of $A$ is given by:$$A^n = \begin{pmatrix} 1 & n \\ 0 & 1 \end{pmatrix}$$.

### Proof:
Assume that $A$ is the $2 \times 2$ real matrix
$A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$.
The goal is to show that for every integer $n \ge 1$ one has
$A^n = \begin{pmatrix} 1 & n \\ 0 & 1 \end{pmatrix}$.

The proof proceeds by induction on the integer $n \ge 1$.

For the base case, take $n = 1$. By definition of the first power of a matrix, one has $A^1 = A$. Substituting the given expression for $A$ yields
$A^1 = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$.
On the other hand, the claimed formula for $A^n$ gives, when $n = 1$,
$\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$.
Therefore the formula holds for $n = 1$.

For the induction step, let $n$ be an arbitrary integer with $n \ge 1$, and assume as induction hypothesis that
$A^n = \begin{pmatrix} 1 & n \\ 0 & 1 \end{pmatrix}$.
Under this assumption, we compute $A^{n+1}$ using the definition of matrix powers. By that definition,
$A^{n+1} = A^n \cdot A$,
where $\cdot$ denotes matrix multiplication. Substituting the induction hypothesis and the explicit form of $A$ into this product gives
\[
A^{n+1}
= \begin{pmatrix} 1 & n \\ 0 & 1 \end{pmatrix}
  \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}.
\]
The product of these two $2 \times 2$ matrices is computed entrywise as follows.

The entry in the first row and first column of the product is
$1 \cdot 1 + n \cdot 0 = 1$.

The entry in the first row and second column of the product is
$1 \cdot 1 + n \cdot 1 = 1 + n$.

The entry in the second row and first column of the product is
$0 \cdot 1 + 1 \cdot 0 = 0$.

The entry in the second row and second column of the product is
$0 \cdot 1 + 1 \cdot 1 = 1$.

Therefore
\[
A^{n+1}
= \begin{pmatrix} 1 & 1 + n \\ 0 & 1 \end{pmatrix}.
\]
Since $1 + n = n + 1$, this can be rewritten as
\[
A^{n+1}
= \begin{pmatrix} 1 & n + 1 \\ 0 & 1 \end{pmatrix}.
\]
Thus, under the assumption that $A^n = \begin{pmatrix} 1 & n \\ 0 & 1 \end{pmatrix}$, we have shown that $A^{n+1} = \begin{pmatrix} 1 & n + 1 \\ 0 & 1 \end{pmatrix}$.

This completes the induction step: if the formula holds for a given integer $n \ge 1$, then it also holds for $n + 1$. Since the formula has been verified in the base case $n = 1$, the principle of mathematical induction implies that for all integers $n \ge 1$ one has
$A^n = \begin{pmatrix} 1 & n \\ 0 & 1 \end{pmatrix}$.

-/


def example14 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:matrix-power",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "A",
            "variable_type": "2 × 2 real matrix",
            "value": "\\begin{pmatrix} 1 & 1 \\\\ 0 & 1 \\end{pmatrix}",
            "statement": "Let A be the 2 × 2 real matrix A = \\begin{pmatrix} 1 & 1 \\\\ 0 & 1 \\end{pmatrix}."
          }
        ],
        "claim": "For all integers n \\ge 1, one has A^n = \\begin{pmatrix} 1 & n \\\\ 0 & 1 \\end{pmatrix}.",
        "proof": {
          "type": "induction_proof",
          "on": "n \\in \\mathbb{Z}, n \\ge 1",
          "base_case_proof": [
            {
              "type": "let_statement",
              "variable_name": "n",
              "variable_type": "integer",
              "properties": "n \\ge 1 and n = 1",
              "statement": "For the base case, take n = 1."
            },
            {
              "type": "assert_statement",
              "claim": "By definition of the first power of a matrix, A^1 = A.",
              "proof_method": "unfolding the definition of the first power of a matrix"
            },
            {
              "type": "assert_statement",
              "claim": "A^1 = \\begin{pmatrix} 1 & 1 \\\\ 0 & 1 \\end{pmatrix}.",
              "proof_method": "substituting the given expression for A"
            },
            {
              "type": "assert_statement",
              "claim": "The claimed formula for A^n gives, when n = 1, A^1 = \\begin{pmatrix} 1 & 1 \\\\ 0 & 1 \\end{pmatrix}.",
              "proof_method": "substituting n = 1 into the claimed formula"
            },
            {
              "type": "conclude_statement",
              "claim": "Therefore the formula holds for n = 1."
            }
          ],
          "induction_step_proof": [
            {
              "type": "let_statement",
              "variable_name": "n",
              "variable_type": "integer",
              "properties": "n \\ge 1",
              "statement": "For the induction step, let n be an arbitrary integer with n \\ge 1."
            },
            {
              "type": "assume_statement",
              "assumption": "Induction hypothesis: A^n = \\begin{pmatrix} 1 & n \\\\ 0 & 1 \\end{pmatrix}."
            },
            {
              "type": "assert_statement",
              "claim": "A^{n+1} = A^n \\cdot A.",
              "proof_method": "definition of matrix powers"
            },
            {
              "type": "assert_statement",
              "claim": "A^{n+1} = \\begin{pmatrix} 1 & n \\\\ 0 & 1 \\end{pmatrix} \\begin{pmatrix} 1 & 1 \\\\ 0 & 1 \\end{pmatrix}.",
              "proof_method": "substituting the induction hypothesis and the explicit form of A"
            },
            {
              "type": "assert_statement",
              "claim": "The (1,1) entry of the product is 1 \\cdot 1 + n \\cdot 0 = 1.",
              "calculation": {
                "type": "calculation",
                "inline_calculation": "1 \\cdot 1 + n \\cdot 0 = 1"
              }
            },
            {
              "type": "assert_statement",
              "claim": "The (1,2) entry of the product is 1 \\cdot 1 + n \\cdot 1 = 1 + n.",
              "calculation": {
                "type": "calculation",
                "inline_calculation": "1 \\cdot 1 + n \\cdot 1 = 1 + n"
              }
            },
            {
              "type": "assert_statement",
              "claim": "The (2,1) entry of the product is 0 \\cdot 1 + 1 \\cdot 0 = 0.",
              "calculation": {
                "type": "calculation",
                "inline_calculation": "0 \\cdot 1 + 1 \\cdot 0 = 0"
              }
            },
            {
              "type": "assert_statement",
              "claim": "The (2,2) entry of the product is 0 \\cdot 1 + 1 \\cdot 1 = 1.",
              "calculation": {
                "type": "calculation",
                "inline_calculation": "0 \\cdot 1 + 1 \\cdot 1 = 1"
              }
            },
            {
              "type": "assert_statement",
              "claim": "A^{n+1} = \\begin{pmatrix} 1 & 1 + n \\\\ 0 & 1 \\end{pmatrix}.",
              "proof_method": "combining the computed entries into the resulting matrix"
            },
            {
              "type": "assert_statement",
              "claim": "A^{n+1} = \\begin{pmatrix} 1 & n + 1 \\\\ 0 & 1 \\end{pmatrix}.",
              "proof_method": "using commutativity of addition, 1 + n = n + 1"
            },
            {
              "type": "conclude_statement",
              "claim": "Thus, under the assumption that A^n = \\begin{pmatrix} 1 & n \\\\ 0 & 1 \\end{pmatrix}, we have shown that A^{n+1} = \\begin{pmatrix} 1 & n + 1 \\\\ 0 & 1 \\end{pmatrix}, so if the formula holds for a given integer n \\ge 1, then it also holds for n + 1."
            }
          ]
        }
      },
      {
        "type": "conclude_statement",
        "claim": "Since the formula has been verified in the base case n = 1 and the induction step has been proved, the principle of mathematical induction implies that for all integers n \\ge 1 one has A^n = \\begin{pmatrix} 1 & n \\\\ 0 & 1 \\end{pmatrix}."
      }
    ]
  }
}

#codegen example14
