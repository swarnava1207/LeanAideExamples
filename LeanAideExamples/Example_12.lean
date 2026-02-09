import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

def example_12 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:min-permutation",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "assume_statement",
            "assumption": "Let A and B be two lists."
          },
          {
            "type": "assume_statement",
            "assumption": "Assume that B is a permutation of A."
          }
        ],
        "claim": "If B is a permutation of A, then min(A) = min(B).",
        "proof": [
          {
            "type": "assume_statement",
            "assumption": "Let A and B be two (finite) lists of elements of a linearly ordered type, and assume that B is a permutation of A. By definition, this means that for every element x, the number of times x appears in A is equal to the number of times x appears in B."
          },
          {
            "type": "condition_cases_proof",
            "condition": "A is nonempty",
            "true_case_proof": [
              {
                "type": "assume_statement",
                "assumption": "Assume first that A is nonempty."
              },
              {
                "type": "some_statement",
                "variable_name": "m",
                "variable_kind": "element of A",
                "properties": "m is a minimal element of A",
                "statement": "By definition of min on a nonempty list, there exists an element m in A such that (1) m ≤ a for every element a in A, and (2) m actually occurs in A."
              },
              {
                "type": "assert_statement",
                "claim": "m ∈ B",
                "proof_method": "Since B is a permutation of A, every element of A appears in B the same number of times, so m appears in B at least once."
              },
              {
                "type": "some_statement",
                "variable_name": "b",
                "variable_kind": "element of B",
                "statement": "Let b be an arbitrary element of B."
              },
              {
                "type": "assert_statement",
                "claim": "b ∈ A",
                "proof_method": "Because B is a permutation of A, every element of B appears in A the same number of times."
              },
              {
                "type": "assert_statement",
                "claim": "m ≤ b for every element b ∈ B",
                "proof_method": "Since m is a minimum of A and every b ∈ B also lies in A, we have m ≤ b for all b ∈ B."
              },
              {
                "type": "assert_statement",
                "claim": "min(B) = m",
                "proof_method": "By the definition of min on a nonempty list, since m is an element of B and is less than or equal to every element of B."
              },
              {
                "type": "assert_statement",
                "claim": "min(A) = m",
                "proof_method": "By the definition of min on a nonempty list, m is the minimum of A."
              },
              {
                "type": "conclude_statement",
                "claim": "min(A) = min(B)",
                "results_used": [
                  {
                    "statement": "min(A) = m"
                  },
                  {
                    "statement": "min(B) = m"
                  }
                ]
              }
            ],
            "false_case_proof": [
              {
                "type": "assume_statement",
                "assumption": "Assume that A is empty."
              },
              {
                "type": "assert_statement",
                "claim": "B is also empty",
                "proof_method": "If A is empty and B is a permutation of A, then B must also be empty, since a permutation preserves the multiset of elements and in particular the length."
              },
              {
                "type": "assert_statement",
                "claim": "min(A) = min(B)",
                "proof_method": "In the Lean library, min on the empty list is defined in some fixed way. Whatever this value is, it is the same for both min([]) and min([])."
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "For any two lists A and B with B a permutation of A, one has min(A) = min(B)."
          }
        ]
      }
    ]
  }
}

theorem minimum_eq_of_perm :
      ∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableLT α] {A B : List α},
        A.Perm B → A.minimum = B.minimum :=
    by
    intro α inst inst_5329030952668389086 A B a_11621284035724616176
    if condition_15733013893012534595 :
        ∀ [LinearOrder α] [inst : BEq α] [LawfulBEq α] {A B : List α},
          A.Perm B → A ≠ [] → ∀ (x : α), List.count x A = List.count x B then

      have assert_7565562541323906428 :
        ∀ [inst : LinearOrder α] (A B : List α), A.Perm B → A ≠ [] → ∃ m ∈ A, ∀ a ∈ A, m ≤ a := by
        apply?
        repeat (sorry)
      have assert_7068124007307670891 :
        ∀ [inst : LinearOrder α] {A B : List α},
          A.Perm B → A ≠ [] → ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ m ∈ B :=
        by repeat (sorry)
      have assert_17118607566038472996 :
        ∀ [inst : LinearOrder α] {A B : List α},
          A.Perm B → A ≠ [] → ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ ∀ b ∈ B, m ≤ b :=
        by repeat (sorry)
      have assert_3283546629895099713 :
        ∀ [inst : LinearOrder α] {A B : List α} {b : α}, A.Perm B → b ∈ B → b ∈ A := by
        grind only [usr List.Perm.mem_iff]
      have assert_17118607566038472996 :
        ∀ [inst : LinearOrder α] {A B : List α},
          A.Perm B → A ≠ [] → ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ ∀ b ∈ B, m ≤ b :=
        by assumption
      have assert_182178963535595628 :
        ∀ [inst : LinearOrder α] [inst_1 : DecidableEq α] {A B : List α},
          B.Perm A →
            A ≠ [] →
              ∃ m ∈ A, (∀ a ∈ A, m ≤ a) ∧ ∀ (hB : B.toFinset.Nonempty), B.toFinset.min' hB = m :=
        by repeat (sorry)
      have assert_7565562541323906428 :
        ∀ [inst : LinearOrder α] (A B : List α), A.Perm B → A ≠ [] → ∃ m ∈ A, ∀ a ∈ A, m ≤ a := by
        assumption
      have :
        ∀ [inst : LinearOrder α] [inst_1 : DecidableEq α] {A B : List α},
          A.Perm B →
            ∀ (hA : A.toFinset.Nonempty) (hB : B.toFinset.Nonempty),
              A.toFinset.min' hA = B.toFinset.min' hB :=
        by repeat (sorry)
      repeat (sorry)
    else grind only [List.Perm.count_eq]
    done
