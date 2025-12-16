import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

/-
Theorem: Let $$G$$ be a group and let $$a,b\in G$$.
If $$ab=ba$$, then $$a b a^{-1} = b$$.
Proof:
Since $$ab=ba$$, multiply on the right by $$a^{-1}$$ to get
$$aba^{-1}=ba a^{-1}=b$$.
-/

def example2 := json%{
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:conjugation_commutes",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "assume_statement",
            "assumption": "G is a group"
          },
          {
            "type": "assume_statement",
            "assumption": "a, b ∈ G"
          },
          {
            "type": "assume_statement",
            "assumption": "ab = ba"
          }
        ],
        "claim": "a b a^{-1} = b",
        "proof": [
          {
            "type": "calculation",
            "inline_calculation": "aba^{-1} = baa^{-1} = b"
          },
          {
            "type": "conclude_statement"
          }
        ]
      }
    ]
  }
}



/-theorem commute.conj_eq :
      ∀ {G : Type u_1} [inst : Group G] {a b : G}, a * b = b * a → a * b * a⁻¹ = b :=
    by
    intro G inst_14157295161945824867 a b a_8184523838834061057
    trace "Automation tactics found for a * b * a⁻¹ = b, closing goal"
    exact Eq.symm (eq_mul_inv_of_mul_eq (id (Eq.symm a_8184523838834061057)))
-/

def example2_rewritten := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:conjugation_commutes",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "G",
            "variable_type": "group",
            "statement": "Let G be a group with identity element e and multiplication denoted by juxtaposition."
          },
          {
            "type": "let_statement",
            "variable_name": "a",
            "variable_type": "element of G",
            "statement": "Let a \u2208 G."
          },
          {
            "type": "let_statement",
            "variable_name": "b",
            "variable_type": "element of G",
            "statement": "Let b \u2208 G."
          },
          {
            "type": "assume_statement",
            "assumption": "a b = b a",
            "label": "h_comm"
          }
        ],
        "claim": "If a b = b a, then a b a^{-1} = b.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "a b = b a",
            "proof_method": "by assumption",
            "internal_references": [
              {
                "target_identifier": "h_comm"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "(a b) a^{-1} = (b a) a^{-1}",
            "proof_method": "congruence of right-multiplication with a^{-1}",
            "internal_references": [
              {
                "target_identifier": "h_comm"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "a (b a^{-1}) = b (a a^{-1})",
            "proof_method": "associativity"
          },
          {
            "type": "assert_statement",
            "claim": "a a^{-1} = e",
            "proof_method": "definition of inverse"
          },
          {
            "type": "assert_statement",
            "claim": "a (b a^{-1}) = b e",
            "proof_method": "substitution using step 4"
          },
          {
            "type": "assert_statement",
            "claim": "b e = b",
            "proof_method": "definition of identity"
          },
          {
            "type": "conclude_statement",
            "claim": "a b a^{-1} = b"
          }
        ]
      }
    ]
  }
}

/-
theorem conj_eq_of_commute :
      ∀ {G : Type u} [inst : Group G] {a b : G}, a * b = b * a → a * b * a⁻¹ = b :=
    by
    intro G inst a b a_8184523838834061057
    trace "Automation tactics found for a * b * a⁻¹ = b, closing goal"
    exact Eq.symm (eq_mul_inv_of_mul_eq (id (Eq.symm a_8184523838834061057)))
-/
