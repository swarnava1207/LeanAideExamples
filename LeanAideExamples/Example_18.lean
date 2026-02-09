import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect "http://drongo:8042"

/-
### Theorem:
For all real numbers $x$,
\[
(x+1)^2 > x^2 \quad \text{if and only if} \quad x > -\frac{1}{2}.
\]

### Proof:
Let $x$ be an arbitrary real number.

First, assume that $(x+1)^2 > x^2$. Subtract $x^2$ from both sides of this inequality. Since subtraction preserves strict inequalities, this yields
\[
(x+1)^2 - x^2 > 0.
\]
Expand the left-hand side:
\[
(x+1)^2 - x^2 = (x^2 + 2x + 1) - x^2 = 2x + 1.
\]
Thus
\[
2x + 1 > 0.
\]
Subtract $1$ from both sides to obtain
\[
2x > -1.
\]
Since $2$ is a positive real number, dividing both sides by $2$ preserves the direction of the inequality, and we obtain
\[
x > -\frac{1}{2}.
\]
This shows that $(x+1)^2 > x^2$ implies $x > -\frac{1}{2}$.

Conversely, assume that $x > -\dfrac{1}{2}$. Multiply both sides of this inequality by $2$, which is positive, so the inequality direction is preserved. This gives
\[
2x > -1.
\]
Add $1$ to both sides to obtain
\[
2x + 1 > 0.
\]
Now compute the difference $(x+1)^2 - x^2$:
\[
(x+1)^2 - x^2 = (x^2 + 2x + 1) - x^2 = 2x + 1.
\]
From $2x + 1 > 0$ we conclude that
\[
(x+1)^2 - x^2 > 0.
\]
Adding $x^2$ to both sides of this strict inequality yields
\[
(x+1)^2 > x^2.
\]
This shows that $x > -\dfrac{1}{2}$ implies $(x+1)^2 > x^2$.

Since both implications have been established, it follows that for all real numbers $x$,
\[
(x+1)^2 > x^2 \quad \text{if and only if} \quad x > -\frac{1}{2}.
\]
-/

def example18 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:x-plus-one-squared",
        "header": "Theorem",
        "claim": "For all real numbers x, (x+1)^2 > x^2 if and only if x > -1/2.",
        "proof": [
          {
            "type": "assume_statement",
            "assumption": "Let x be an arbitrary real number."
          },
          {
            "type": "bi-implication_cases_proof",
            "if_proof": [
              {
                "type": "assume_statement",
                "assumption": "(x+1)^2 > x^2."
              },
              {
                "type": "assert_statement",
                "claim": "(x+1)^2 - x^2 > 0",
                "proof_method": "Subtract x^2 from both sides of (x+1)^2 > x^2; subtraction preserves strict inequalities."
              },
              {
                "type": "assert_statement",
                "claim": "(x+1)^2 - x^2 = 2x + 1",
                "proof_method": "Expand (x+1)^2 = x^2 + 2x + 1 and simplify.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "(x+1)^2 - x^2 = (x^2 + 2x + 1) - x^2",
                    "(x^2 + 2x + 1) - x^2 = 2x + 1"
                  ]
                }
              },
              {
                "type": "assert_statement",
                "claim": "2x + 1 > 0",
                "proof_method": "Combine (x+1)^2 - x^2 > 0 with (x+1)^2 - x^2 = 2x + 1."
              },
              {
                "type": "assert_statement",
                "claim": "2x > -1",
                "proof_method": "Subtract 1 from both sides of 2x + 1 > 0."
              },
              {
                "type": "assert_statement",
                "claim": "x > -1/2",
                "proof_method": "Divide both sides of 2x > -1 by 2, which is positive, so the inequality direction is preserved."
              },
              {
                "type": "conclude_statement",
                "claim": "(x+1)^2 > x^2 implies x > -1/2."
              }
            ],
            "only_if_proof": [
              {
                "type": "assume_statement",
                "assumption": "x > -1/2."
              },
              {
                "type": "assert_statement",
                "claim": "2x > -1",
                "proof_method": "Multiply both sides of x > -1/2 by 2, which is positive, so the inequality direction is preserved."
              },
              {
                "type": "assert_statement",
                "claim": "2x + 1 > 0",
                "proof_method": "Add 1 to both sides of 2x > -1."
              },
              {
                "type": "assert_statement",
                "claim": "(x+1)^2 - x^2 = 2x + 1",
                "proof_method": "Expand (x+1)^2 = x^2 + 2x + 1 and simplify.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "(x+1)^2 - x^2 = (x^2 + 2x + 1) - x^2",
                    "(x^2 + 2x + 1) - x^2 = 2x + 1"
                  ]
                }
              },
              {
                "type": "assert_statement",
                "claim": "(x+1)^2 - x^2 > 0",
                "proof_method": "Combine 2x + 1 > 0 with (x+1)^2 - x^2 = 2x + 1."
              },
              {
                "type": "assert_statement",
                "claim": "(x+1)^2 > x^2",
                "proof_method": "Add x^2 to both sides of (x+1)^2 - x^2 > 0."
              },
              {
                "type": "conclude_statement",
                "claim": "x > -1/2 implies (x+1)^2 > x^2."
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "For all real numbers x, (x+1)^2 > x^2 if and only if x > -1/2."
          }
        ]
      }
    ]
  }
}

-- ### LeanCode generated by LeanAide
theorem add_one_sq_gt_sq_iff :
      ∀ {x : ℝ}, (x + (1 : ℝ)) ^ (2 : ℕ) > x ^ (2 : ℕ) ↔ x > (-1 / 2 : ℝ) :=
    by
    intro x
    grind only [#5212]
