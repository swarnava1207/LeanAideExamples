import LeanAideCore
import Mathlib
import Lean.Data.Json
import Lean
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

/-
Theorem:
For any real $x$,
\[
|x| =
\begin{cases}
x, & x\ge 0,\\
-x, & x<0.

Proof:
We prove the two cases.

Case 1: $x\ge 0$. By the definition of absolute value in this case, $|x|=x$. (No further manipulation is needed; the value is nonnegative and equals $x$.)

Case 2: $x<0$. Then $-x>0$. By the definition of absolute value for a negative input, $|x|=-x$, which is nonnegative. Hence the stated piecewise definition holds in both cases.
-/
#eval "open"

def example3 := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:absolute_value",
        "header": "Theorem",
        "claim": "For any real x,|x| = x & x ge 0,\\ -x & x < 0.",
        "proof": {
          "type": "condition_cases_proof",
          "condition": "x ge 0",
          "true_case_proof": [
            {
              "type": "assert_statement",
              "claim": "|x| = x",
              "proof_method": "definition of absolute value"
            }
          ],
          "false_case_proof": [
            {
              "type": "assert_statement",
              "claim": "|x| = -x",
              "proof_method": "definition of absolute value"
            }
          ]
        }
      }
    ]
  }
}

/-theorem abs_eq_ite : ∀ (x : ℝ), (0 ≤ x → |x| = x) ∧ (x < 0 → |x| = -x) :=
    by
    intro x
    if condition_4014921585265476193 : 0 ≤ x then

      trace "Automation tactics found for (0 ≤ x → |x| = x) ∧ (x < 0 → |x| = -x), closing goal"
      simp only [abs_eq_self, Lake.FamilyOut.fam_eq, imp_self, abs_eq_neg_self, true_and]
      exact fun a => le_of_lt a
    else
      trace "Automation tactics found for (0 ≤ x → |x| = x) ∧ (x < 0 → |x| = -x), closing goal"
      simp only [abs_eq_self, Lake.FamilyOut.fam_eq, imp_self, abs_eq_neg_self, true_and]
      exact fun a => le_of_lt a
    done-/

/-**Theorem.**  For any real $x$,
\[
|x| =
\begin{cases}
x, & x\ge 0,\\
-x, & x<0.

**Proof.**
Assume
1.  \(x\) is a real number.

Recall the definition of the absolute value on \(\mathbb{R}\):
\[
|x| = \begin{cases}
x, &\text{if }x \ge 0,\\
-\,x,&\text{if }x<0,
\end{cases}
\]
equivalently
\[
|x| = \mathit{ite}(x\ge0,\;x,\;-x),
\]
where \(\mathit{ite}(p,a,b)\) denotes the value \(a\) when the proposition \(p\) is true, and \(b\) when \(p\) is false.

By the trichotomy law for real numbers, exactly one of the propositions \(x\ge 0\) or \(x<0\) holds. We proceed by cases.

Case 1: \(x\ge 0\).
Then the condition in the \(\mathit{ite}\) is true. By definition of the conditional,
\[
|x| \;=\;\mathit{ite}(x\ge0,\;x,\;-x)\;=\;x.
\]

Case 2: \(x<0\).
Then the condition in the \(\mathit{ite}\) is false. By definition of the conditional,
\[
|x| \;=\;\mathit{ite}(x\ge0,\;x,\;-x)\;=\;-x.
\]

These two cases exhaust all possibilities for \(x\), and in each case \(|x|\) agrees with the stated piecewise formula.
-/


def example3_rewritten := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:absolute_value",
        "hypothesis": [
          {
            "type": "assume_statement",
            "assumption": "x is a real number."
          }
        ],
        "claim": "For any real x, |x| = x if x ≥ 0, and |x| = -x if x < 0.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "Recall the definition of the absolute value on ℝ: |x| = ite(x ≥ 0, x, -x)."
          },
          {
            "type": "assert_statement",
            "claim": "By the trichotomy law for real numbers, exactly one of x ≥ 0 or x < 0 holds."
          },
          {
            "type": "condition_cases_proof",
            "condition": "x ≥ 0",
            "true_case_proof": [
              {
                "type": "calculation",
                "inline_calculation": "|x| = ite(x ≥ 0, x, -x) = x"
              }
            ],
            "false_case_proof": [
              {
                "type": "calculation",
                "inline_calculation": "|x| = ite(x ≥ 0, x, -x) = -x"
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "|x| agrees with the piecewise formula in all cases."
          }
        ]
      }
    ]
  }
}

#codegen example3_rewritten
/-
theorem abs_by_cases : ∀ (x : ℝ), (0 ≤ x → |x| = x) ∧ (x < 0 → |x| = -x) :=
    by
    intro x
    trace "Automation tactics found for (0 ≤ x → |x| = x) ∧ (x < 0 → |x| = -x), closing goal"
    simp only [abs_eq_self, Lake.FamilyOut.fam_eq, imp_self, abs_eq_neg_self, true_and]
    exact fun a => le_of_lt a
-/
