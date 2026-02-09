import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

/-
### Theorem:
Let $X = \mathbb{R}$. Consider the function $d: \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ defined by:$$d(x, y) = |x^3 - y^3|$$.  Then, the function $d$ is a metric on $\mathbb{R}$.

### Proof:
For each pair of real numbers $x,y \in \mathbb{R}$ define
\[
d(x,y) = |x^3 - y^3|.
\]
The goal is to prove that $d$ is a metric on $\mathbb{R}$.

To show that $d$ is a metric, we must verify the following four properties for all $x,y,z \in \mathbb{R}$:

1. $d(x,y) \ge 0$ (nonnegativity),
2. $d(x,y) = 0$ if and only if $x = y$ (identity of indiscernibles),
3. $d(x,y) = d(y,x)$ (symmetry),
4. $d(x,z) \le d(x,y) + d(y,z)$ (triangle inequality).

All quantifiers will be over $\mathbb{R}$.

---

First, for any $x,y \in \mathbb{R}$, by definition $d(x,y) = |x^3 - y^3|$. For any real number $a$, the absolute value satisfies $|a| \ge 0$. Hence, for $a = x^3 - y^3$, it follows that $d(x,y) = |x^3 - y^3| \ge 0$. This proves nonnegativity.

---

Next, we prove the identity of indiscernibles.

Assume $d(x,y) = 0$. Then $|x^3 - y^3| = 0$. The absolute value of a real number is $0$ if and only if the number itself is $0$. Therefore $x^3 - y^3 = 0$, hence $x^3 = y^3$. The function $f:\mathbb{R} \to \mathbb{R}$ given by $f(t) = t^3$ is injective: if $u^3 = v^3$ then $(u-v)(u^2 + uv + v^2) = 0$, and since $u^2 + uv + v^2 \ge 0$ for all real $u,v$ and this sum can be $0$ only when $u = v = 0$, it follows that $u^3 = v^3$ implies $u = v$. Applying this with $u = x$ and $v = y$, we obtain $x = y$. Thus $d(x,y) = 0$ implies $x = y$.

Conversely, assume $x = y$. Then $x^3 = y^3$, hence $x^3 - y^3 = 0$, so $|x^3 - y^3| = 0$. Therefore $d(x,y) = 0$.

Combining both directions, we have $d(x,y) = 0$ if and only if $x = y$.

---

Now we verify symmetry. Let $x,y \in \mathbb{R}$. Then
\[
d(x,y) = |x^3 - y^3|.
\]
On the other hand,
\[
d(y,x) = |y^3 - x^3|.
\]
Since $y^3 - x^3 = -(x^3 - y^3)$, and for any real $a$ we have $|-a| = |a|$, it follows that
\[
d(y,x) = |y^3 - x^3| = |-(x^3 - y^3)| = |x^3 - y^3| = d(x,y).
\]
Thus $d(x,y) = d(y,x)$ for all $x,y$, so symmetry holds.

---

It remains to prove the triangle inequality. Let $x,y,z \in \mathbb{R}$. Then
\[
d(x,z) = |x^3 - z^3|.
\]
We write
\[
x^3 - z^3 = (x^3 - y^3) + (y^3 - z^3).
\]
Hence
\[
|x^3 - z^3| = |(x^3 - y^3) + (y^3 - z^3)|.
\]
The absolute value on $\mathbb{R}$ satisfies the triangle inequality:
\[
|u + v| \le |u| + |v|
\]
for all real $u,v$. Applying this with $u = x^3 - y^3$ and $v = y^3 - z^3$ gives
\[
|x^3 - z^3| \le |x^3 - y^3| + |y^3 - z^3|.
\]
By the definition of $d$, this is
\[
d(x,z) \le d(x,y) + d(y,z).
\]
Therefore, the triangle inequality holds for $d$.

---

All four metric axioms are satisfied by $d(x,y) = |x^3 - y^3|$ on $\mathbb{R}$, so $d$ is a metric on $\mathbb{R}$.

-/

-- ## Structured JSON Proof

def example11 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:d-cube-metric",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "X",
            "value": "\\mathbb{R}",
            "variable_type": "set",
            "statement": "Let X = \\mathbb{R}."
          },
          {
            "type": "let_statement",
            "variable_name": "d",
            "variable_type": "function",
            "properties": "d : \\mathbb{R} \\times \\mathbb{R} \\to \\mathbb{R} is defined by d(x,y) = |x^3 - y^3| for all x,y \\in \\mathbb{R}.",
            "statement": "Consider the function d : \\mathbb{R} \\times \\mathbb{R} \\to \\mathbb{R} defined by d(x,y) = |x^3 - y^3|."
          }
        ],
        "claim": "The function d is a metric on \\mathbb{R}.",
        "proof": [
          {
            "type": "Paragraph",
            "text": "The goal is to prove that d is a metric on \\mathbb{R}. To show that d is a metric, we must verify the following four properties for all x,y,z \\in \\mathbb{R}: (1) d(x,y) \\ge 0 (nonnegativity), (2) d(x,y) = 0 if and only if x = y (identity of indiscernibles), (3) d(x,y) = d(y,x) (symmetry), (4) d(x,z) \\le d(x,y) + d(y,z) (triangle inequality). All quantifiers will be over \\mathbb{R}."
          },
          {
            "type": "Section",
            "label": "sec:nonnegativity",
            "level": 2,
            "header": "Nonnegativity",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Let x,y \\in \\mathbb{R}."
              },
              {
                "type": "assert_statement",
                "claim": "d(x,y) = |x^3 - y^3| \\ge 0.",
                "proof_method": "Since for any real number a, the absolute value satisfies |a| \\ge 0, applying this to a = x^3 - y^3 gives the inequality.",
                "calculation": {
                  "type": "calculation",
                  "inline_calculation": "d(x,y) = |x^3 - y^3| \\ge 0"
                }
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:identity-indiscernibles",
            "level": 2,
            "header": "Identity of indiscernibles",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Assume d(x,y) = 0."
              },
              {
                "type": "assert_statement",
                "claim": "|x^3 - y^3| = 0 implies x^3 - y^3 = 0.",
                "proof_method": "The absolute value of a real number is 0 if and only if the number itself is 0."
              },
              {
                "type": "assert_statement",
                "claim": "x^3 - y^3 = 0, hence x^3 = y^3.",
                "proof_method": "Algebraic rearrangement."
              },
              {
                "type": "assert_statement",
                "label": "stmt:cubic-injective",
                "claim": "If u^3 = v^3 for real numbers u,v, then u = v.",
                "proof_method": "Injectivity of the function f(t) = t^3 on \\mathbb{R}.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "u^3 - v^3 = (u-v)(u^2 + uv + v^2)",
                    "u^3 = v^3 \\Rightarrow u^3 - v^3 = 0",
                    "(u-v)(u^2 + uv + v^2) = 0"
                  ]
                }
              },
              {
                "type": "assert_statement",
                "claim": "If u^3 = v^3, then u = v.",
                "proof_method": "From (u-v)(u^2 + uv + v^2) = 0 and the fact that u^2 + uv + v^2 \\ge 0 for all real u,v and this sum can be 0 only when u = v = 0, it follows that u^3 = v^3 implies u = v.",
                "results_used": [
                  {
                    "statement": "For all real u,v, u^2 + uv + v^2 \\ge 0, and u^2 + uv + v^2 = 0 implies u = v = 0."
                  }
                ],
                "internal_references": [
                  {
                    "target_identifier": "stmt:cubic-injective"
                  }
                ]
              },
              {
                "type": "assert_statement",
                "claim": "From x^3 = y^3, we obtain x = y.",
                "proof_method": "Apply the injectivity result of the cubic function with u = x and v = y.",
                "results_used": [
                  {
                    "statement": "If u^3 = v^3 for real numbers u,v, then u = v.",
                    "target_identifier": "stmt:cubic-injective"
                  }
                ]
              },
              {
                "type": "assume_statement",
                "assumption": "Conversely, assume x = y."
              },
              {
                "type": "assert_statement",
                "claim": "If x = y then d(x,y) = 0.",
                "proof_method": "If x = y then x^3 = y^3, so x^3 - y^3 = 0 and hence |x^3 - y^3| = 0.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "x = y \\Rightarrow x^3 = y^3",
                    "x^3 - y^3 = 0",
                    "|x^3 - y^3| = 0",
                    "d(x,y) = 0"
                  ]
                }
              },
              {
                "type": "conclude_statement",
                "claim": "Therefore d(x,y) = 0 if and only if x = y."
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:symmetry",
            "level": 2,
            "header": "Symmetry",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Let x,y \\in \\mathbb{R}."
              },
              {
                "type": "assert_statement",
                "claim": "d(x,y) = |x^3 - y^3| and d(y,x) = |y^3 - x^3|.",
                "proof_method": "By the definition of d."
              },
              {
                "type": "assert_statement",
                "claim": "|y^3 - x^3| = |x^3 - y^3|.",
                "proof_method": "Since y^3 - x^3 = -(x^3 - y^3) and for any real a we have |-a| = |a|.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "y^3 - x^3 = -(x^3 - y^3)",
                    "|y^3 - x^3| = |-(x^3 - y^3)|",
                    "|-(x^3 - y^3)| = |x^3 - y^3|"
                  ]
                }
              },
              {
                "type": "assert_statement",
                "claim": "d(y,x) = d(x,y).",
                "proof_method": "Substitute the definitions of d(x,y) and d(y,x) into the equality of absolute values.",
                "calculation": {
                  "type": "calculation",
                  "inline_calculation": "d(y,x) = |y^3 - x^3| = |x^3 - y^3| = d(x,y)"
                }
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:triangle-inequality",
            "level": 2,
            "header": "Triangle inequality",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Let x,y,z \\in \\mathbb{R}."
              },
              {
                "type": "assert_statement",
                "claim": "x^3 - z^3 = (x^3 - y^3) + (y^3 - z^3).",
                "proof_method": "Algebraic rearrangement.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "x^3 - z^3 = x^3 - y^3 + y^3 - z^3",
                    "x^3 - z^3 = (x^3 - y^3) + (y^3 - z^3)"
                  ]
                }
              },
              {
                "type": "assert_statement",
                "claim": "|x^3 - z^3| = |(x^3 - y^3) + (y^3 - z^3)|.",
                "proof_method": "Apply the absolute value to both sides of the equality x^3 - z^3 = (x^3 - y^3) + (y^3 - z^3)."
              },
              {
                "type": "assert_statement",
                "claim": "|(x^3 - y^3) + (y^3 - z^3)| \\le |x^3 - y^3| + |y^3 - z^3|.",
                "proof_method": "The absolute value on \\mathbb{R} satisfies the triangle inequality |u + v| \\le |u| + |v| for all real u,v, applied with u = x^3 - y^3 and v = y^3 - z^3.",
                "results_used": [
                  {
                    "statement": "For all real u,v, |u + v| \\le |u| + |v| (triangle inequality for absolute value)."
                  }
                ]
              },
              {
                "type": "assert_statement",
                "claim": "d(x,z) = |x^3 - z^3| \\le |x^3 - y^3| + |y^3 - z^3| = d(x,y) + d(y,z).",
                "proof_method": "Substitute the definition of d into the inequality for absolute values.",
                "calculation": {
                  "type": "calculation",
                  "calculation_sequence": [
                    "d(x,z) = |x^3 - z^3|",
                    "|x^3 - z^3| \\le |x^3 - y^3| + |y^3 - z^3|",
                    "|x^3 - y^3| + |y^3 - z^3| = d(x,y) + d(y,z)",
                    "d(x,z) \\le d(x,y) + d(y,z)"
                  ]
                }
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "All four metric axioms are satisfied by d(x,y) = |x^3 - y^3| on \\mathbb{R}, so d is a metric on \\mathbb{R}."
          }
        ]
      }
    ]
  }
}

#codegen example11
