import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect "http://drongo:8042"

/-
### Theorem:
Let $T : V \to V$ be a linear transformation.
Prove that
\[
V = \ker(T) \oplus \operatorname{im}(T)
\]
if and only if for every $v \in V$, there exists a unique
$w \in \operatorname{im}(T)$ such that
\[
v - w \in \ker(T).
\]

### Proof:

Assume that $V$ is a vector space over a field and that $T : V \to V$ is a linear transformation.

Suppose first that $V = \ker(T) \oplus \operatorname{im}(T)$. By the definition of a direct sum, this means that every $v \in V$ can be written as
\[
v = k + u
\]
with $k \in \ker(T)$ and $u \in \operatorname{im}(T)$, and that this decomposition is unique, in the sense that if $v = k_1 + u_1 = k_2 + u_2$ with $k_1, k_2 \in \ker(T)$ and $u_1, u_2 \in \operatorname{im}(T)$, then $k_1 = k_2$ and $u_1 = u_2$.

Let $v \in V$ be arbitrary. By the above, there exist $k \in \ker(T)$ and $u \in \operatorname{im}(T)$ such that $v = k + u$. Set $w := u$. Then $w \in \operatorname{im}(T)$ and
\[
v - w = (k + u) - u = k.
\]
Since $k \in \ker(T)$, this shows the existence of $w$ with the desired property.

To prove uniqueness, suppose that $w_1, w_2 \in \operatorname{im}(T)$ both satisfy
\[
v - w_1 \in \ker(T) \quad\text{and}\quad v - w_2 \in \ker(T).
\]
Define
\[
k_1 := v - w_1, \quad k_2 := v - w_2.
\]
Then $k_1, k_2 \in \ker(T)$ by assumption, and we have
\[
v = k_1 + w_1 = k_2 + w_2
\]
with $k_1, k_2 \in \ker(T)$ and $w_1, w_2 \in \operatorname{im}(T)$. By uniqueness of the decomposition in the direct sum $\ker(T) \oplus \operatorname{im}(T)$, it follows that $w_1 = w_2$. Therefore, for each $v \in V$ there exists a unique $w \in \operatorname{im}(T)$ such that $v - w \in \ker(T)$.

Conversely, suppose that for every $v \in V$ there exists a unique $w \in \operatorname{im}(T)$ such that $v - w \in \ker(T)$. We need to show that $V = \ker(T) \oplus \operatorname{im}(T)$.

First, to show that $V = \ker(T) + \operatorname{im}(T)$, let $v \in V$ be arbitrary. By assumption, there exists $w \in \operatorname{im}(T)$ such that $v - w \in \ker(T)$. Set
\[
k := v - w.
\]
Then $k \in \ker(T)$ by assumption, and we have
\[
v = k + w
\]
with $k \in \ker(T)$ and $w \in \operatorname{im}(T)$. This shows that every $v \in V$ belongs to $\ker(T) + \operatorname{im}(T)$, so
\[
V = \ker(T) + \operatorname{im}(T).
\]

Next, to prove that the sum is direct, we need to show that
\[
\ker(T) \cap \operatorname{im}(T) = \{0\}.
\]
Let $x \in \ker(T) \cap \operatorname{im}(T)$. Then $x \in \operatorname{im}(T)$, and $x \in \ker(T)$ as well. Consider the vector $v := x \in V$.

By the assumed property, there exists a unique $w \in \operatorname{im}(T)$ such that
\[
v - w \in \ker(T).
\]
First, observe that $w = x$ satisfies the condition: since $x \in \operatorname{im}(T)$ and $v - x = x - x = 0 \in \ker(T)$, the pair $(v,w) = (x,x)$ fits the requirement.

On the other hand, $w = 0$ also satisfies the condition: $0 \in \operatorname{im}(T)$ because $T(0) = 0$, and $v - 0 = x \in \ker(T)$ by assumption. Thus both $w = x$ and $w = 0$ are elements of $\operatorname{im}(T)$ such that $v - w \in \ker(T)$.

By the uniqueness hypothesis, it follows that $x = 0$. Therefore, every element of $\ker(T) \cap \operatorname{im}(T)$ is zero, and hence
\[
\ker(T) \cap \operatorname{im}(T) = \{0\}.
\]

Combining the two facts
\[
V = \ker(T) + \operatorname{im}(T) \quad\text{and}\quad \ker(T) \cap \operatorname{im}(T) = \{0\},
\]
we conclude that
\[
V = \ker(T) \oplus \operatorname{im}(T).
\]

-/

-- ### JSON Structured Proof

def example24 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:ker-im-direct-sum-characterization",
        "header": "Theorem",
        "claim": "Let T : V → V be a linear transformation. Then\n\nV = ker(T) ⊕ im(T)\n\nif and only if for every v ∈ V, there exists a unique w ∈ im(T) such that\n\nv − w ∈ ker(T).",
        "proof": [
          {
            "type": "assume_statement",
            "assumption": "V is a vector space over a field and T : V → V is a linear transformation."
          },
          {
            "type": "assume_statement",
            "assumption": "V = ker(T) ⊕ im(T)."
          },
          {
            "type": "assert_statement",
            "claim": "By the definition of a direct sum, every v ∈ V can be written as v = k + u with k ∈ ker(T) and u ∈ im(T), and this decomposition is unique: if v = k₁ + u₁ = k₂ + u₂ with k₁, k₂ ∈ ker(T) and u₁, u₂ ∈ im(T), then k₁ = k₂ and u₁ = u₂.",
            "proof_method": "Unpacking the definition of a direct sum"
          },
          {
            "type": "some_statement",
            "variable_name": "v",
            "variable_kind": "element of V",
            "properties": "v is arbitrary",
            "statement": "Let v ∈ V be arbitrary."
          },
          {
            "type": "assert_statement",
            "claim": "There exist k ∈ ker(T) and u ∈ im(T) such that v = k + u.",
            "proof_method": "Apply the decomposition property from the direct sum assumption"
          },
          {
            "type": "let_statement",
            "variable_name": "w",
            "value": "u",
            "variable_type": "element of im(T)",
            "statement": "Set w := u. Then w ∈ im(T)."
          },
          {
            "type": "assert_statement",
            "claim": "v − w = k.",
            "proof_method": "Direct calculation from v = k + u and w = u",
            "calculation": {
              "type": "calculation",
              "calculation_sequence": [
                "v − w = (k + u) − u",
                "(k + u) − u = k"
              ]
            }
          },
          {
            "type": "assert_statement",
            "claim": "Since k ∈ ker(T), there exists w ∈ im(T) such that v − w ∈ ker(T).",
            "proof_method": "Take w = u and use the previous calculation"
          },
          {
            "type": "assume_statement",
            "assumption": "w₁, w₂ ∈ im(T) both satisfy v − w₁ ∈ ker(T) and v − w₂ ∈ ker(T).",
            "label": "asm:two-ws"
          },
          {
            "type": "let_statement",
            "variable_name": "k₁",
            "variable_type": "element of ker(T)",
            "statement": "Define k₁ := v − w₁.",
            "properties": "k₁ ∈ ker(T) by assumption"
          },
          {
            "type": "let_statement",
            "variable_name": "k₂",
            "variable_type": "element of ker(T)",
            "statement": "Define k₂ := v − w₂.",
            "properties": "k₂ ∈ ker(T) by assumption"
          },
          {
            "type": "assert_statement",
            "claim": "v = k₁ + w₁ = k₂ + w₂ with k₁, k₂ ∈ ker(T) and w₁, w₂ ∈ im(T).",
            "proof_method": "Rewriting v from the definitions of k₁ and k₂"
          },
          {
            "type": "assert_statement",
            "claim": "w₁ = w₂.",
            "proof_method": "Apply uniqueness of the decomposition in the direct sum ker(T) ⊕ im(T) to v = k₁ + w₁ = k₂ + w₂"
          },
          {
            "type": "assert_statement",
            "claim": "For each v ∈ V there exists a unique w ∈ im(T) such that v − w ∈ ker(T).",
            "proof_method": "Combine the existence and uniqueness arguments above"
          },
          {
            "type": "assume_statement",
            "assumption": "For every v ∈ V there exists a unique w ∈ im(T) such that v − w ∈ ker(T).",
            "label": "asm:unique-decomposition-property"
          },
          {
            "type": "assert_statement",
            "claim": "V = ker(T) + im(T).",
            "proof_method": "Show that every v ∈ V can be expressed as k + w with k ∈ ker(T) and w ∈ im(T)"
          },
          {
            "type": "some_statement",
            "variable_name": "v",
            "variable_kind": "element of V",
            "properties": "v is arbitrary",
            "statement": "Let v ∈ V be arbitrary."
          },
          {
            "type": "assert_statement",
            "claim": "There exists w ∈ im(T) such that v − w ∈ ker(T).",
            "proof_method": "Apply the uniqueness hypothesis for this v"
          },
          {
            "type": "let_statement",
            "variable_name": "k",
            "variable_type": "element of ker(T)",
            "statement": "Set k := v − w.",
            "properties": "Then k ∈ ker(T) by assumption."
          },
          {
            "type": "assert_statement",
            "claim": "v = k + w with k ∈ ker(T) and w ∈ im(T).",
            "proof_method": "Rearrange the definition of k"
          },
          {
            "type": "assert_statement",
            "claim": "Every v ∈ V belongs to ker(T) + im(T), so V = ker(T) + im(T).",
            "proof_method": "Since v was arbitrary, this holds for all v ∈ V"
          },
          {
            "type": "assert_statement",
            "claim": "ker(T) ∩ im(T) = {0}.",
            "proof_method": "Use the uniqueness hypothesis applied to a vector v in the intersection"
          },
          {
            "type": "some_statement",
            "variable_name": "x",
            "variable_kind": "element of ker(T) ∩ im(T)",
            "properties": "x is arbitrary",
            "statement": "Let x ∈ ker(T) ∩ im(T)."
          },
          {
            "type": "let_statement",
            "variable_name": "v",
            "value": "x",
            "variable_type": "element of V",
            "statement": "Consider the vector v := x ∈ V."
          },
          {
            "type": "assert_statement",
            "claim": "There exists a unique w ∈ im(T) such that v − w ∈ ker(T).",
            "proof_method": "Apply the uniqueness hypothesis to v = x"
          },
          {
            "type": "assert_statement",
            "claim": "w = x satisfies the condition: x ∈ im(T) and v − x = 0 ∈ ker(T).",
            "proof_method": "Use that x ∈ im(T) and x ∈ ker(T)"
          },
          {
            "type": "assert_statement",
            "claim": "w = 0 also satisfies the condition: 0 ∈ im(T) and v − 0 = x ∈ ker(T).",
            "proof_method": "Use linearity of T to see 0 ∈ im(T) and the assumption x ∈ ker(T)"
          },
          {
            "type": "assert_statement",
            "claim": "x = 0.",
            "proof_method": "By uniqueness of w in im(T) such that v − w ∈ ker(T), the two admissible choices w = x and w = 0 must coincide"
          },
          {
            "type": "assert_statement",
            "claim": "Every element of ker(T) ∩ im(T) is zero, hence ker(T) ∩ im(T) = {0}.",
            "proof_method": "Since x was arbitrary in ker(T) ∩ im(T)"
          },
          {
            "type": "conclude_statement",
            "claim": "V = ker(T) ⊕ im(T).",
            "results_used": [
              {
                "statement": "V = ker(T) + im(T)."
              },
              {
                "statement": "ker(T) ∩ im(T) = {0}."
              }
            ]
          }
        ]
      }
    ]
  }
}


-- ## LeanCode generated by LeanAide
#codegen example24
