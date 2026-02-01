import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect "http://drongo:8042"

/-
### Theorem:

A Boolean Ring is a ring $R$ where every element $x$ satisfies $x^2 = x$ (every element is idempotent).
Prove that if $R$ is a Boolean Ring, then $R$ is commutative (i.e., $xy = yx$ for all $x, y$ in $R$).

### Proof:

Let $R$ be a Boolean ring. By definition, this means that for every $x \in R$ we have $x^2 = x$.

The goal is to show that $R$ is commutative, that is, for all $x,y \in R$ we have $xy = yx$.

First, set $x = 1$ in the identity $x^2 = x$. We obtain
\[
1^2 = 1.
\]
This holds in every ring, but we note it explicitly.

Next, we show that every element of $R$ has additive order $2$. Let $x \in R$ be arbitrary. Consider $(x + x)^2$. Since $R$ is Boolean, we have
\[
(x + x)^2 = x + x.
\]
On the other hand, by the distributive law and ring axioms,
\[
(x + x)^2 = x^2 + x^2 + x^2 + x^2.
\]
Using idempotency $x^2 = x$ four times, this simplifies to
\[
(x + x)^2 = x + x + x + x.
\]
Combining the two expressions for $(x + x)^2$, we obtain
\[
x + x + x + x = x + x.
\]
Adding the additive inverse of $x + x$ to both sides, we get
\[
x + x = 0.
\]
Thus $2x = 0$ for all $x \in R$. In particular, substituting $x = 1$, we obtain
\[
1 + 1 = 0.
\]

Now let $x,y \in R$ be arbitrary. Consider the element $x + y \in R$. Since $R$ is Boolean, we have
\[
(x + y)^2 = x + y.
\]
Expanding the left-hand side using distributivity,
\[
(x + y)^2 = x^2 + xy + yx + y^2.
\]
Using idempotency $x^2 = x$ and $y^2 = y$, this becomes
\[
x + xy + yx + y = x + y.
\]
We now subtract $x + y$ from both sides (that is, we add the additive inverse of $x + y$ to both sides) to obtain
\[
xy + yx = 0.
\]

Using $1 + 1 = 0$, we compute
\[
(xy + yx) + (xy + yx) = 0 + 0 = 0.
\]
The left-hand side can be regrouped using associativity and commutativity of addition:
\[
(xy + xy) + (yx + yx) = 0.
\]
Since $xy + xy = 2(xy)$ and $yx + yx = 2(yx)$ and $2z = 0$ for all $z \in R$, we have $xy + xy = 0$ and $yx + yx = 0$. Thus the equation above reduces to
\[
0 + 0 = 0,
\]
which is an identity and does not give new information. Instead, we use directly that $xy + yx = 0$ and $1 + 1 = 0$.

From $1 + 1 = 0$ we have $-1 = 1$, since $1 + 1 = 0$ implies $1 = -1$. For any $z \in R$,
\[
-z = (-1)z = 1 \cdot z = z.
\]
Apply this to $z = xy$ and $z = yx$:
\[
-xy = xy, \quad -yx = yx.
\]
From $xy + yx = 0$ we can write
\[
xy = -(yx).
\]
Using $-yx = yx$, this becomes
\[
xy = yx.
\]

Since $x,y \in R$ were arbitrary, this shows that $xy = yx$ for all $x,y \in R$. Therefore $R$ is commutative.
-/

def example16 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "hypothesis": [
          {
            "type": "assume_statement",
            "assumption": "R is a Boolean ring, i.e., a ring in which every element x satisfies x^2 = x (every element is idempotent).",
            "label": "asm:boolean_ring"
          }
        ],
        "claim": "If R is a Boolean ring, then R is commutative; that is, for all x, y in R we have xy = yx.",
        "label": "thm:boolean_ring_commutative",
        "header": "Theorem",
        "proof": [
          {
            "type": "assume_statement",
            "assumption": "R is a Boolean ring. By definition, this means that for every x in R we have x^2 = x.",
            "label": "asm:boolean_def"
          },
          {
            "type": "assert_statement",
            "claim": "1^2 = 1.",
            "proof_method": "Set x = 1 in the identity x^2 = x and use the definition of Boolean ring.",
            "label": "stmt:one_idempotent"
          },
          {
            "type": "assert_statement",
            "claim": "For every x in R, (x + x)^2 = x + x.",
            "proof_method": "Use that R is Boolean, so any element, in particular x + x, is idempotent.",
            "label": "stmt:xx_idempotent",
            "internal_references": [
              {
                "target_identifier": "asm:boolean_ring"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every x in R, (x + x)^2 = x^2 + x^2 + x^2 + x^2.",
            "proof_method": "Expand (x + x)^2 using the distributive law and ring axioms.",
            "label": "stmt:expand_xx_square"
          },
          {
            "type": "assert_statement",
            "claim": "For every x in R, (x + x)^2 = x + x + x + x.",
            "proof_method": "Use idempotency x^2 = x four times in the expression x^2 + x^2 + x^2 + x^2.",
            "label": "stmt:four_x",
            "internal_references": [
              {
                "target_identifier": "asm:boolean_def"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every x in R, x + x + x + x = x + x.",
            "proof_method": "Combine the two expressions for (x + x)^2 obtained previously.",
            "label": "stmt:four_x_equals_two_x",
            "internal_references": [
              {
                "target_identifier": "stmt:xx_idempotent"
              },
              {
                "target_identifier": "stmt:four_x"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every x in R, x + x = 0 (equivalently, 2x = 0).",
            "proof_method": "Add the additive inverse of x + x to both sides of x + x + x + x = x + x.",
            "label": "stmt:two_x_zero",
            "internal_references": [
              {
                "target_identifier": "stmt:four_x_equals_two_x"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "1 + 1 = 0.",
            "proof_method": "Apply the statement 2x = 0 with x = 1.",
            "label": "stmt:one_plus_one_zero",
            "internal_references": [
              {
                "target_identifier": "stmt:two_x_zero"
              }
            ]
          },
          {
            "type": "assume_statement",
            "assumption": "Let x, y be arbitrary elements of R.",
            "label": "asm:arbitrary_xy"
          },
          {
            "type": "assert_statement",
            "claim": "(x + y)^2 = x + y.",
            "proof_method": "Use that R is Boolean, so x + y is idempotent.",
            "label": "stmt:xy_idempotent",
            "internal_references": [
              {
                "target_identifier": "asm:boolean_ring"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "(x + y)^2 = x^2 + xy + yx + y^2.",
            "proof_method": "Expand (x + y)^2 using distributivity.",
            "label": "stmt:expand_xy_square"
          },
          {
            "type": "assert_statement",
            "claim": "x + xy + yx + y = x + y.",
            "proof_method": "In x^2 + xy + yx + y^2 substitute x^2 = x and y^2 = y, and use the equality (x + y)^2 = x + y.",
            "label": "stmt:xy_rearranged",
            "internal_references": [
              {
                "target_identifier": "asm:boolean_def"
              },
              {
                "target_identifier": "stmt:xy_idempotent"
              },
              {
                "target_identifier": "stmt:expand_xy_square"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "xy + yx = 0.",
            "proof_method": "Subtract x + y from both sides of x + xy + yx + y = x + y.",
            "label": "stmt:xy_plus_yx_zero",
            "internal_references": [
              {
                "target_identifier": "stmt:xy_rearranged"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "-1 = 1.",
            "proof_method": "From 1 + 1 = 0, rearrange to obtain 1 = -1.",
            "label": "stmt:minus_one_equals_one",
            "internal_references": [
              {
                "target_identifier": "stmt:one_plus_one_zero"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "For every z in R, -z = z.",
            "proof_method": "Compute -z = (-1)z and use -1 = 1 so that (-1)z = 1·z = z.",
            "label": "stmt:negation_is_identity",
            "internal_references": [
              {
                "target_identifier": "stmt:minus_one_equals_one"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "-xy = xy and -yx = yx.",
            "proof_method": "Apply the property -z = z to z = xy and z = yx.",
            "label": "stmt:neg_xy_yx",
            "internal_references": [
              {
                "target_identifier": "stmt:negation_is_identity"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "xy = yx.",
            "proof_method": "From xy + yx = 0, obtain xy = -(yx); then use -yx = yx.",
            "label": "stmt:comm_xy_yx",
            "internal_references": [
              {
                "target_identifier": "stmt:xy_plus_yx_zero"
              },
              {
                "target_identifier": "stmt:neg_xy_yx"
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "R is commutative, i.e., for all x, y in R we have xy = yx.",
            "results_used": [
              {
                "statement": "For arbitrary x, y in R, xy = yx.",
                "target_identifier": "stmt:comm_xy_yx"
              }
            ]
          }
        ],
        "citations": [],
        "internal_references": []
      }
    ],
    "title": "Commutativity of Boolean Rings",
    "abstract": "We show that any Boolean ring, i.e., a ring in which every element is idempotent, is necessarily commutative."
  }
}

-- ## LeanCode generated by LeanAide
theorem is_commutative_mul_of_boolean_ring :
      ∀ {R : Type u} [inst : BooleanRing R] (x y : R), x * y = y * x :=
    by
    intro R inst x y
    grind only
