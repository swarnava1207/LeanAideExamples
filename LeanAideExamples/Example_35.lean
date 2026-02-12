import LeanAideCore
import Mathlib
import Lean.Data.Json
import Lean
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

/- ## Theorem
Prove that the function $\phi(n) = -n$ is a group homomorphism on $(\mathbb{Z}, +)$.
-/

/- ## Proof
**Theorem.**
Let \(\mathbb{Z}\) be the additive group with operation \(+\), identity element \(0\), and inverse given by negation.  Define
\[
φ : \mathbb{Z} \to \mathbb{Z},
\quad φ(n) := -\,n.
\]
Then \(φ\) is a group homomorphism from \((\mathbb{Z},+)\) to \((\mathbb{Z},+)\).

**Proof.**
Assume the following context and definitions:
• \(\mathbb{Z}\) is an additive group with identity \(0\).
• For each \(a\in\mathbb{Z}\), the element \(-a\) is the additive inverse of \(a\), characterized by \(a + (-a) = 0\).
• A function \(ψ : \mathbb{Z}\to\mathbb{Z}\) is a group homomorphism if and only if
  1. \(ψ(0) = 0\), and
  2. for all \(x,y\in\mathbb{Z}\), \(ψ(x+y) = ψ(x) + ψ(y)\).

We verify these two properties for \(φ\).

**Lemma 1 (Preservation of the identity).**
Claim: \(φ(0) = 0\).
Proof of Lemma 1:
By definition of \(φ\),
\[
φ(0) = -\,0.
\]
By the defining property of additive inverses in \(\mathbb{Z}\), \(-0\) is the unique element \(b\) satisfying \(0 + b = 0\).  Since \(0 + 0 = 0\), uniqueness of inverses yields \(-0 = 0\).  Therefore \(φ(0) = 0\). □

**Lemma 2 (Additivity).**
Claim: For all \(m,n\in\mathbb{Z}\), \(φ(m + n) = φ(m) + φ(n)\).
Proof of Lemma 2:
Let \(m\) and \(n\) be arbitrary elements of \(\mathbb{Z}\).  Then
\[
φ(m + n)
= -\,(m + n)
\quad\text{(by definition of }φ\text{)}
= (-\,m) + (-\,n)
\quad\text{(by the property of additive inverses in \(\mathbb{Z}\))}
= φ(m) + φ(n)
\quad\text{(by definition of }φ\text{).}
\]
This establishes the desired additivity. □

By Lemmas 1 and 2, the function \(φ\) preserves the identity element and the group operation.  Hence \(φ\) is a group homomorphism.
-/

def negative_hom := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:negation_homomorphism",
        "claim": "The function φ: ℤ → ℤ defined by φ(n) := -n is a group homomorphism on (ℤ, +).",
        "proof": [
          {
            "type": "Paragraph",
            "text": "Recall that (ℤ, +) is the additive group with identity 0 and inverse given by negation. A function ψ: ℤ → ℤ is a group homomorphism if and only if ψ(0) = 0 and ψ(x+y) = ψ(x) + ψ(y) for all x,y ∈ ℤ."
          },
          {
            "type": "assert_statement",
            "claim": "φ(0) = 0",
            "proof_method": "By definition of φ and the fact that −0 = 0 in ℤ"
          },
          {
            "type": "assert_statement",
            "claim": "φ(m + n) = φ(m) + φ(n)",
            "proof_method": "By definition of φ and the property that –(m + n) = (–m) + (–n) in ℤ"
          },
          {
            "type": "conclude_statement"
          }
        ]
      }
    ]
  }
}


/- ## LeanAide response -/
def token_negative_hom := 2876963958857813979

noncomputable def int.neg_int_hom_is_add_monoid_hom : ℤ →+ ℤ := by exact Int.castAddHom ℤ
