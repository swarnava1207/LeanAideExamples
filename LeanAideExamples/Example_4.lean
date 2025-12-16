import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

/-Theorem:
Let $(a_n)$ be a sequence defined by $a_0=c$ and $a_{n+1} = a_n$ for all $n$.
Then $a_n = c$ for all $n$.

Proof:
By induction.
Base case: $a_0=c$ by definition.
Inductive step: if $a_n=c$, then $a_{n+1}=a_n=c$.
Thus $a_n=c$ for all $n$.
-/

#leanaide_connect

def example4 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:constant_sequence",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "a_n",
            "variable_type": "sequence",
            "properties": "defined by a_0 = c and a_{n+1} = a_n for all n",
            "statement": "Let (a_n) be a sequence defined by a_0 = c and a_{n+1} = a_n for all n."
          }
        ],
        "claim": "a_n = c for all n.",
        "proof": [
          {
            "type": "induction_proof",
            "on": "n",
            "base_case_proof": [
              {
                "type": "assert_statement",
                "claim": "a_0 = c",
                "proof_method": "definition"
              }
            ],
            "induction_step_proof": [
              {
                "type": "assume_statement",
                "assumption": "a_n = c"
              },
              {
                "type": "assert_statement",
                "claim": "a_{n+1} = c",
                "proof_method": "substitution"
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "a_n = c for all n."
          }
        ]
      }
    ]
  }
}
/-
theorem forall_eq_const_of_succ_eq :
      ∀ {α : Type u} {a : ℕ → α} {c : α},
        a 0 = c → (∀ (n : ℕ), a (n + 1) = a n) → ∀ (n : ℕ), a n = c :=
    by
    intro α a c a_18193650970466190054 a_18068984259474765511 n
    induction n with
    | zero =>
      trace "Automation tactics found for a 0 = c, closing goal"
      grind only
    | succ n ih =>
      trace "Automation tactics found for a (n + 1) = c, closing goal"
      grind only
    done
-/
def example4_rewritten := json%
{
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:const_seq",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "α",
            "variable_type": "Type",
            "statement": "Let α be a type"
          },
          {
            "type": "let_statement",
            "variable_name": "c",
            "variable_type": "α",
            "statement": "Let c : α"
          },
          {
            "type": "let_statement",
            "variable_name": "a",
            "variable_type": "ℕ → α",
            "statement": "Let a : ℕ → α"
          },
          {
            "type": "assume_statement",
            "assumption": "a 0 = c",
            "label": "h₀"
          },
          {
            "type": "assume_statement",
            "assumption": "∀ n : ℕ, a (n + 1) = a n",
            "label": "h_rec"
          }
        ],
        "claim": "∀ n : ℕ, a n = c",
        "proof": {
          "type": "induction_proof",
          "on": "n",
          "base_case_proof": [
            {
              "type": "assert_statement",
              "claim": "a 0 = c",
              "results_used": [
                {
                  "statement": "a 0 = c",
                  "target_identifier": "h₀"
                }
              ]
            }
          ],
          "induction_step_proof": [
            {
              "type": "let_statement",
              "variable_name": "k",
              "variable_type": "ℕ",
              "statement": "Let k : ℕ"
            },
            {
              "type": "assume_statement",
              "assumption": "a k = c",
              "label": "h_ih"
            },
            {
              "type": "assert_statement",
              "claim": "a (k + 1) = a k",
              "label": "h_step",
              "results_used": [
                {
                  "statement": "a (k + 1) = a k",
                  "target_identifier": "h_rec"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "a (k + 1) = c",
              "results_used": [
                {
                  "statement": "a (k + 1) = a k",
                  "target_identifier": "h_step"
                },
                {
                  "statement": "a k = c",
                  "target_identifier": "h_ih"
                }
              ]
            }
          ]
        }
      }
    ]
  }
}

/-
theorem forall_eq_of_eq_zero_of_succ_eq :
      ∀ {α : Type u} {c : α} {a : ℕ → α},
        a 0 = c → (∀ (n : ℕ), a (n + 1) = a n) → ∀ (n : ℕ), a n = c :=
    by
    intro α c a a_18193650970466190054 a_18068984259474765511 n
    induction n with
    | zero =>
      trace "Automation tactics found for a 0 = c, closing goal"
      grind only
    | succ n ih =>
      trace "Automation tactics found for a (n + 1) = c, closing goal"
      grind only
    done
-/
