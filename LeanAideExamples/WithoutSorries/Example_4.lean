import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.unusedTactic false

/-
## Theorem:
Let $(a_n)$ be a sequence defined by $a_0=c$ and $a_{n+1} = a_n$ for all $n$.
Then $a_n = c$ for all $n$.

## Proof:
Let $(a_n)$ be a sequence defined on the natural numbers with values in some type, and suppose that $a_0 = c$ and that for every natural number $n$ we have $a_{n+1} = a_n$. The goal is to prove that for every natural number $n$ we have $a_n = c$.

The proof proceeds by induction on $n$.

First, consider the base case $n = 0$. By the defining condition of the sequence, we have $a_0 = c$. Thus the conclusion holds for $n = 0$.

Next, assume as the inductive hypothesis that for some arbitrary but fixed natural number $k$ we have $a_k = c$. Under this assumption, we must prove that $a_{k+1} = c$. By the recursive definition of the sequence, we know that $a_{k+1} = a_k$. Combining this with the inductive hypothesis $a_k = c$, and using transitivity of equality, we obtain $a_{k+1} = c$.

Since the base case holds and the inductive step has been verified, the principle of mathematical induction implies that for every natural number $n$ we have $a_n = c$.
-/

--## Structured JSON Proof

def example4 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:constant-sequence",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "a_n",
            "variable_type": "sequence defined on the natural numbers with values in some type",
            "statement": "Let (a_n) be a sequence defined on the natural numbers with values in some type."
          },
          {
            "type": "let_statement",
            "variable_name": "c",
            "variable_type": "element of the codomain of (a_n)",
            "statement": "Let c be an element of the codomain of (a_n)."
          },
          {
            "type": "assume_statement",
            "assumption": "a_0 = c."
          },
          {
            "type": "assume_statement",
            "assumption": "For every natural number n we have a_{n+1} = a_n."
          }
        ],
        "claim": "Then a_n = c for all natural numbers n.",
        "proof": {
          "type": "induction_proof",
          "on": "n",
          "base_case_proof": [
            {
              "type": "assume_statement",
              "assumption": "Consider the base case n = 0."
            },
            {
              "type": "assert_statement",
              "claim": "a_0 = c.",
              "proof_method": "This follows directly from the defining condition a_0 = c of the sequence."
            },
            {
              "type": "conclude_statement",
              "claim": "The conclusion a_n = c holds for n = 0."
            }
          ],
          "induction_step_proof": [
            {
              "type": "assume_statement",
              "assumption": "Assume as the inductive hypothesis that for some arbitrary but fixed natural number k we have a_k = c."
            },
            {
              "type": "assert_statement",
              "claim": "a_{k+1} = a_k.",
              "proof_method": "By the recursive definition of the sequence, for every natural number n we have a_{n+1} = a_n; taking n = k gives a_{k+1} = a_k."
            },
            {
              "type": "assert_statement",
              "claim": "a_{k+1} = c.",
              "proof_method": "Combining a_{k+1} = a_k with the inductive hypothesis a_k = c and using transitivity of equality."
            },
            {
              "type": "conclude_statement",
              "claim": "The conclusion a_n = c holds for n = k + 1."
            }
          ]
        }
      },
      {
        "type": "conclude_statement",
        "claim": "By the principle of mathematical induction, for every natural number n we have a_n = c."
      }
    ]
  }
}

#leanaide_connect "http://drongo:8042"
  theorem forall_eq_of_zero_eq_and_succ_eq_self :
      ∀ {α : Type u} {a : ℕ → α} {c : α},
        a (0 : ℕ) = c → (∀ (n : ℕ), a (n + (1 : ℕ)) = a n) → ∀ (n : ℕ), a n = c :=
    by
    intro α a c a_18193650970466190054 a_18068984259474765511 n
    induction n with
    | zero => grind only
    | succ n ih => grind only [#4b08]
    done
  #check "Error: codegen: no valid function found for key conclude_statement"
  #check "Tried functions: #[LeanAide.concludeCode]"
  #check "Errors in functions:"
  #check ""
  #check "LeanAide.concludeCode: codegen: conclude_statement does not work for kind [commandSeq]"
  #check "source:"
  #check "{\"claim\":"
  #check
    " \"By the principle of mathematical induction, for every natural number n we have a_n = c.\"}"

/- ### Issues

1. There are these unnecessary `#check` statements going around.

-/
