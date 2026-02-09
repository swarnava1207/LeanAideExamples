import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect "http://drongo:8042"

def example13:= json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:telescoping-sequence",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "a_n",
            "variable_type": "sequence of real numbers (or elements of any field of characteristic 0) indexed by integers n ≥ 0",
            "statement": "Let the sequence (a_n)_{n \u0019e 0} be defined by the initial value a_0 = 2 and the recurrence relation a_{n+1} = a_n^2 - a_n + 1 for all integers n \u0019e 0."
          }
        ],
        "claim": "For all integers n \u0019e 1, the following equality holds: \\(\\sum_{k=0}^{n-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_n - 1}\\).",
        "proof": [
          {
            "type": "Paragraph",
            "text": "We assume throughout that (a_n)_{n\u0019e 0} is a sequence of real numbers (or elements of any field of characteristic 0) defined by a_0 = 2 and, for every integer n \u0019e 0, a_{n+1} = a_n^2 - a_n + 1. The goal is to prove that, for every integer n \u0019e 1, we have \\(\\sum_{k=0}^{n-1} 1/a_k = 1 - 1/(a_n - 1)\\)."
          },
          {
            "type": "Section",
            "label": "sec:step1",
            "level": 2,
            "header": "Step 1: Rewrite the recurrence in a useful form.",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Fix an integer n \u0019e 0."
              },
              {
                "type": "assert_statement",
                "claim": "a_{n+1} = a_n^2 - a_n + 1 = a_n(a_n - 1) + 1.",
                "proof_method": "direct algebraic manipulation of the recurrence relation"
              },
              {
                "type": "assert_statement",
                "label": "eq:anplus1-minus1",
                "claim": "For every integer n \u0019e 0, we have a_{n+1} - 1 = a_n(a_n - 1).",
                "proof_method": "subtract 1 from both sides of the identity a_{n+1} = a_n(a_n - 1) + 1"
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:step2",
            "level": 2,
            "header": "Step 2: Show that all terms a_n are nonzero and different from 1.",
            "content": [
              {
                "type": "assert_statement",
                "label": "assert:a0-not-0-1",
                "claim": "We have a_0 = 2, so a_0 \\neq 0 and a_0 \\neq 1, and therefore a_0 - 1 \\neq 0.",
                "proof_method": "evaluation of the initial condition"
              },
              {
                "type": "induction_proof",
                "on": "n (with n \u0019e 0)",
                "base_case_proof": [
                  {
                    "type": "assert_statement",
                    "claim": "For n = 0 we have a_0 - 1 \\neq 0.",
                    "proof_method": "this holds by the claim a_0 - 1 \\neq 0",
                    "internal_references": [
                      {
                        "target_identifier": "assert:a0-not-0-1"
                      }
                    ]
                  }
                ],
                "induction_step_proof": [
                  {
                    "type": "assume_statement",
                    "assumption": "Assume a_n - 1 \\neq 0 for some n \u0019e 0."
                  },
                  {
                    "type": "assert_statement",
                    "claim": "Then a_n(a_n - 1) \\neq 0.",
                    "proof_method": "product of two nonzero elements is nonzero"
                  },
                  {
                    "type": "assert_statement",
                    "claim": "Hence a_{n+1} - 1 \\neq 0.",
                    "proof_method": "use the relation a_{n+1} - 1 = a_n(a_n - 1)",
                    "internal_references": [
                      {
                        "target_identifier": "eq:anplus1-minus1"
                      }
                    ]
                  }
                ]
              },
              {
                "type": "assert_statement",
                "label": "assert:an-not-1",
                "claim": "For every n \u0019e 0 we have a_n \\neq 1.",
                "proof_method": "from a_n - 1 \\neq 0 for all n \u0019e 0"
              },
              {
                "type": "assert_statement",
                "label": "assert:an-not-0",
                "claim": "For every n \u0019e 0 we have a_n \\neq 0.",
                "proof_method": "if a_n = 0 then a_n - 1 = -1 \\neq 0 and a_{n+1} - 1 = 0 \\cdot (0 - 1) = 0, contradicting a_{n+1} \\neq 1, so such an n cannot exist",
                "internal_references": [
                  {
                    "target_identifier": "eq:anplus1-minus1"
                  },
                  {
                    "target_identifier": "assert:an-not-1"
                  }
                ]
              },
              {
                "type": "conclude_statement",
                "claim": "Thus, for every n \u0019e 0 we have a_n \\neq 0 and a_n \\neq 1, so all denominators a_n and a_n - 1 that appear in what follows are nonzero."
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:step3",
            "level": 2,
            "header": "Step 3: Derive a key identity involving reciprocals.",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Let n be an integer with n \u0019e 0."
              },
              {
                "type": "assert_statement",
                "label": "eq:reciprocal-equality",
                "claim": "For every n \u0019e 0, we have \\(\\frac{1}{a_{n+1} - 1} = \\frac{1}{a_n(a_n - 1)}\\).",
                "proof_method": "take reciprocals in the equality a_{n+1} - 1 = a_n(a_n - 1), using that a_n and a_n - 1 are nonzero",
                "internal_references": [
                  {
                    "target_identifier": "eq:anplus1-minus1"
                  },
                  {
                    "target_identifier": "assert:an-not-0"
                  },
                  {
                    "target_identifier": "assert:an-not-1"
                  }
                ]
              },
              {
                "type": "assert_statement",
                "label": "eq:partial-fraction",
                "claim": "For every n \u0019e 0, we have \\(\\frac{1}{a_n(a_n - 1)} = \\frac{1}{a_n - 1} - \\frac{1}{a_n}\\).",
                "proof_method": "direct verification: (1/(a_n - 1) - 1/a_n) = (a_n - (a_n - 1))/(a_n(a_n - 1)) = 1/(a_n(a_n - 1))"
              },
              {
                "type": "assert_statement",
                "label": "eq:key-identity",
                "claim": "For every n \u0019e 0, we have \\(\\frac{1}{a_{n+1} - 1} = \\frac{1}{a_n - 1} - \\frac{1}{a_n}\\).",
                "proof_method": "combine the identities 1/(a_{n+1} - 1) = 1/(a_n(a_n - 1)) and 1/(a_n(a_n - 1)) = 1/(a_n - 1) - 1/a_n",
                "internal_references": [
                  {
                    "target_identifier": "eq:reciprocal-equality"
                  },
                  {
                    "target_identifier": "eq:partial-fraction"
                  }
                ]
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:step4",
            "level": 2,
            "header": "Step 4: Rearranging the identity for telescoping.",
            "content": [
              {
                "type": "assert_statement",
                "label": "eq:1-over-an",
                "claim": "For every integer n \u0019e 0, we have \\(\\frac{1}{a_n} = \\frac{1}{a_n - 1} - \\frac{1}{a_{n+1} - 1}\\).",
                "proof_method": "rearrange the equality 1/(a_{n+1} - 1) = 1/(a_n - 1) - 1/a_n by bringing 1/a_n to the left-hand side",
                "internal_references": [
                  {
                    "target_identifier": "eq:key-identity"
                  }
                ]
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:step5",
            "level": 2,
            "header": "Step 5: Sum the identity from k = 0 to k = n-1.",
            "content": [
              {
                "type": "assume_statement",
                "assumption": "Fix an integer n \u0019e 1."
              },
              {
                "type": "assert_statement",
                "label": "eq:sum-before-a0",
                "claim": "For every integer n \u0019e 1, we have \\(\\sum_{k=0}^{n-1} \\frac{1}{a_k} = \\sum_{k=0}^{n-1} \\left( \\frac{1}{a_k - 1} - \\frac{1}{a_{k+1} - 1} \\right)\\).",
                "proof_method": "sum the identity 1/a_k = 1/(a_k - 1) - 1/(a_{k+1} - 1) over k from 0 to n-1",
                "internal_references": [
                  {
                    "target_identifier": "eq:1-over-an"
                  }
                ]
              },
              {
                "type": "assert_statement",
                "label": "eq:telescoping",
                "claim": "For every integer n \u0019e 1, we have \\(\\sum_{k=0}^{n-1} \\left( \\frac{1}{a_k - 1} - \\frac{1}{a_{k+1} - 1} \\right) = \\frac{1}{a_0 - 1} - \\frac{1}{a_n - 1}\\).",
                "proof_method": "telescoping sum: all intermediate terms cancel pairwise, leaving only 1/(a_0 - 1) and -1/(a_n - 1)"
              },
              {
                "type": "assert_statement",
                "label": "eq:sum-with-a0",
                "claim": "For every integer n \u0019e 1, we have \\(\\sum_{k=0}^{n-1} \\frac{1}{a_k} = \\frac{1}{a_0 - 1} - \\frac{1}{a_n - 1}\\).",
                "proof_method": "combine the previous two equalities",
                "internal_references": [
                  {
                    "target_identifier": "eq:sum-before-a0"
                  },
                  {
                    "target_identifier": "eq:telescoping"
                  }
                ]
              }
            ]
          },
          {
            "type": "Section",
            "label": "sec:step6",
            "level": 2,
            "header": "Step 6: Substitute the initial value.",
            "content": [
              {
                "type": "assert_statement",
                "label": "eq:a0-1",
                "claim": "We have a_0 = 2, so a_0 - 1 = 1 and hence 1/(a_0 - 1) = 1.",
                "proof_method": "direct computation from the initial value"
              },
              {
                "type": "assert_statement",
                "label": "eq:final-identity",
                "claim": "For every integer n \u0019e 1, we have \\(\\sum_{k=0}^{n-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_n - 1}\\).",
                "proof_method": "substitute 1/(a_0 - 1) = 1 into the equality \\sum_{k=0}^{n-1} 1/a_k = 1/(a_0 - 1) - 1/(a_n - 1)",
                "internal_references": [
                  {
                    "target_identifier": "eq:sum-with-a0"
                  },
                  {
                    "target_identifier": "eq:a0-1"
                  }
                ]
              },
              {
                "type": "conclude_statement",
                "claim": "Thus, for all integers n \u0019e 1, we have \\(\\sum_{k=0}^{n-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_n - 1}\\), which is exactly the desired identity."
              }
            ]
          }
        ]
      }
    ]
  }
}


def example13' := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:sum-recurrence",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "a_n",
            "variable_type": "sequence (a_n)_{n \\ge 0}",
            "properties": "defined by the initial value a_0 = 2 and the recurrence relation a_{n+1} = a_n^2 - a_n + 1 for all integers n \\ge 0",
            "statement": "Let the sequence (a_n)_{n \\ge 0} be defined by the initial value a_0 = 2 and the recurrence relation a_{n+1} = a_n^2 - a_n + 1 for all integers n \\ge 0."
          }
        ],
        "claim": "For all integers n \\ge 1, the following equality holds: \\sum_{k=0}^{n-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_n - 1}.",
        "proof": {
          "type": "induction_proof",
          "on": "n",
          "base_case_proof": [
            {
              "type": "assume_statement",
              "assumption": "Let n = 1."
            },
            {
              "type": "assert_statement",
              "claim": "The left-hand side is \\sum_{k=0}^{0} \\frac{1}{a_k} = \\frac{1}{a_0} = \\frac{1}{2}.",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "\\sum_{k=0}^{0} \\frac{1}{a_k} = \\frac{1}{a_0}",
                  "\\frac{1}{a_0} = \\frac{1}{2}"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "a_1 = a_0^2 - a_0 + 1 = 3.",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "a_1 = a_0^2 - a_0 + 1",
                  "a_1 = 2^2 - 2 + 1",
                  "a_1 = 4 - 2 + 1",
                  "a_1 = 3"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "The right-hand side is 1 - \\frac{1}{a_1 - 1} = \\frac{1}{2}.",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "1 - \\frac{1}{a_1 - 1} = 1 - \\frac{1}{3 - 1}",
                  "1 - \\frac{1}{3 - 1} = 1 - \\frac{1}{2}",
                  "1 - \\frac{1}{2} = \\frac{1}{2}"
                ]
              }
            },
            {
              "type": "conclude_statement",
              "claim": "For n = 1, \\sum_{k=0}^{0} \\frac{1}{a_k} = 1 - \\frac{1}{a_1 - 1}."
            }
          ],
          "induction_step_proof": [
            {
              "type": "assume_statement",
              "assumption": "Assume that for some arbitrary integer m \\ge 1, \\sum_{k=0}^{m-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_m - 1}."
            },
            {
              "type": "assert_statement",
              "claim": "We must show that \\sum_{k=0}^{m} \\frac{1}{a_k} = 1 - \\frac{1}{a_{m+1} - 1}."
            },
            {
              "type": "assert_statement",
              "claim": "Starting with the left-hand side, \\sum_{k=0}^{m} \\frac{1}{a_k} = \\left( \\sum_{k=0}^{m-1} \\frac{1}{a_k} \\right) + \\frac{1}{a_m}.",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "\\sum_{k=0}^{m} \\frac{1}{a_k} = \\left( \\sum_{k=0}^{m-1} \\frac{1}{a_k} \\right) + \\frac{1}{a_m}"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "By the induction hypothesis, \\sum_{k=0}^{m} \\frac{1}{a_k} = \\left( 1 - \\frac{1}{a_m - 1} \\right) + \\frac{1}{a_m}.",
              "results_used": [
                {
                  "statement": "Induction hypothesis: \\sum_{k=0}^{m-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_m - 1}."
                }
              ],
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "\\sum_{k=0}^{m} \\frac{1}{a_k} = \\left( 1 - \\frac{1}{a_m - 1} \\right) + \\frac{1}{a_m}"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "We have \\sum_{k=0}^{m} \\frac{1}{a_k} = 1 - \\left( \\frac{1}{a_m - 1} - \\frac{1}{a_m} \\right).",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "\\left( 1 - \\frac{1}{a_m - 1} \\right) + \\frac{1}{a_m} = 1 - \\frac{1}{a_m - 1} + \\frac{1}{a_m}",
                  "1 - \\frac{1}{a_m - 1} + \\frac{1}{a_m} = 1 - \\left( \\frac{1}{a_m - 1} - \\frac{1}{a_m} \\right)"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "The difference of fractions simplifies to \\frac{1}{a_m(a_m - 1)}; hence \\sum_{k=0}^{m} \\frac{1}{a_k} = 1 - \\frac{1}{a_m^2 - a_m}.",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "\\frac{1}{a_m - 1} - \\frac{1}{a_m} = \\frac{a_m - (a_m - 1)}{a_m(a_m - 1)}",
                  "\\frac{a_m - (a_m - 1)}{a_m(a_m - 1)} = \\frac{1}{a_m(a_m - 1)}",
                  "a_m(a_m - 1) = a_m^2 - a_m",
                  "1 - \\left( \\frac{1}{a_m - 1} - \\frac{1}{a_m} \\right) = 1 - \\frac{1}{a_m^2 - a_m}"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "By the recurrence relation, a_{m+1} - 1 = a_m^2 - a_m.",
              "results_used": [
                {
                  "statement": "Recurrence relation: a_{m+1} = a_m^2 - a_m + 1."
                }
              ],
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "a_{m+1} = a_m^2 - a_m + 1",
                  "a_{m+1} - 1 = a_m^2 - a_m"
                ]
              }
            },
            {
              "type": "assert_statement",
              "claim": "Therefore \\sum_{k=0}^{m} \\frac{1}{a_k} = 1 - \\frac{1}{a_{m+1} - 1}.",
              "calculation": {
                "type": "calculation",
                "calculation_sequence": [
                  "1 - \\frac{1}{a_m^2 - a_m} = 1 - \\frac{1}{a_{m+1} - 1}"
                ]
              }
            },
            {
              "type": "conclude_statement",
              "claim": "If the formula holds for n = m, then it holds for n = m + 1."
            }
          ]
        }
      },
      {
        "type": "conclude_statement",
        "claim": "By the principle of mathematical induction, for all integers n \\ge 1, \\sum_{k=0}^{n-1} \\frac{1}{a_k} = 1 - \\frac{1}{a_n - 1}."
      }
    ]
  }
}
