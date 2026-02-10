import LeanAideCore
import Mathlib
import Lean.Data.Json
import Lean
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

/- ## Theorem
Prove that 2 is an upper bound for the set of real numbers
whose square is less than 4.
-/

/- ## Proof
Definitions and Lemmas

Let S := { x ∈ ℝ ∣ x² < 4 }.
We prove that 2 is an upper bound of S, i.e. ∀ x ∈ S, x ≤ 2.

Lemma 1 (nonnegativity of squares):
  ∀ x : ℝ, 0 ≤ x².

Proof of Lemma 1.
  For each x : ℝ, x² = x * x.  By the order‐field axiom that squares are nonnegative, 0 ≤ x * x. □

Lemma 2 (strict monotonicity of sqrt on nonnegatives):
  ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a < b → sqrt a < sqrt b.

Proof of Lemma 2.
  This follows from the property `real.sqrt_lt_iff_lt` and the fact that `sqrt` maps nonnegatives to nonnegatives. □

Lemma 3 (sqrt of a square is absolute value):
  ∀ x : ℝ, sqrt (x²) = |x|.

Proof of Lemma 3.
  This is the defining property of `real.sqrt` on nonnegative arguments together with `abs_eq_sqrt_sq`. □

Lemma 4 (strict‐to‐weak inequality):
  ∀ a b : ℝ, a < b → a ≤ b.

Proof of Lemma 4.
  This is the axiom `lt.le`. □

Lemma 5 (abs bounds the number):
  ∀ x : ℝ, -|x| ≤ x ∧ x ≤ |x|.

Proof of Lemma 5.
  This is the definition of `abs`. □

Lemma 6 (from |x| < 2 to x ≤ 2):
  ∀ x : ℝ, |x| < 2 → x ≤ 2.

Proof of Lemma 6.
  Let x : ℝ and h₁₀ : |x| < 2.
  From Lemma 5 we have h₅.1 : x ≤ |x|.
  From h₅.1 and h₁₀, by transitivity of ≤ and <, we get h₆₁ : x < 2.
  From h₆₁ and Lemma 4 we conclude x ≤ 2. □

Main proof

Let x : ℝ and assume h : x² < 4.
1. From Lemma 1 we have h₁ : 0 ≤ x².
2. From h₁, the fact 0 ≤ 4, and h, Lemma 2 gives
     sqrt (x²) < sqrt 4 = 2.
3. Lemma 3 yields |x| = sqrt (x²), so |x| < 2.
4. Lemma 6 applied to |x| < 2 yields x ≤ 2.

Since x : ℝ with x² < 4 was arbitrary, we conclude ∀ x ∈ S, x ≤ 2. Hence 2 is an upper bound of S.
-/

def upper_bound := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Definition",
        "label": "def: S",
        "header": "Definition",
        "name": "S",
        "definition": "S := { x ∈ ℝ ∣ x² < 4 }"
      },
      {
        "type": "Theorem",
        "header": "Lemma",
        "label": "lem:nonnegativity_of_squares",
        "claim": "∀ x : ℝ, 0 ≤ x².",
        "proof": [
          {
            "type": "let_statement",
            "variable_name": "x",
            "variable_type": "ℝ",
            "statement": "let x : ℝ"
          },
          {
            "type": "assert_statement",
            "claim": "x² = x * x"
          },
          {
            "type": "assert_statement",
            "claim": "0 ≤ x * x",
            "proof_method": "order-field axiom that squares are nonnegative"
          }
        ]
      },
      {
        "type": "Theorem",
        "header": "Lemma",
        "label": "lem:sqrt_strict_monotonicity",
        "claim": "∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a < b → sqrt a < sqrt b.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "sqrt a < sqrt b",
            "results_used": [
              {
                "statement": "real.sqrt_lt_iff_lt",
                "mathlib_identifier": "real.sqrt_lt_iff_lt"
              },
              {
                "statement": "sqrt maps nonnegatives to nonnegatives"
              }
            ]
          }
        ]
      },
      {
        "type": "Theorem",
        "header": "Lemma",
        "label": "lem:sqrt_of_square_abs",
        "claim": "∀ x : ℝ, sqrt (x²) = |x|.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "sqrt (x²) = |x|",
            "results_used": [
              {
                "statement": "defining property of real.sqrt on nonnegative arguments"
              },
              {
                "statement": "abs_eq_sqrt_sq",
                "mathlib_identifier": "abs_eq_sqrt_sq"
              }
            ]
          }
        ]
      },
      {
        "type": "Theorem",
        "header": "Lemma",
        "label": "lem:strict_to_weak_inequality",
        "claim": "∀ a b : ℝ, a < b → a ≤ b.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "a ≤ b",
            "results_used": [
              {
                "statement": "lt.le",
                "mathlib_identifier": "lt.le"
              }
            ]
          }
        ]
      },
      {
        "type": "Theorem",
        "header": "Lemma",
        "label": "lem:abs_bounds",
        "claim": "∀ x : ℝ, -|x| ≤ x ∧ x ≤ |x|.",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "-|x| ≤ x ∧ x ≤ |x|",
            "results_used": [
              {
                "statement": "definition of abs"
              }
            ]
          }
        ]
      },
      {
        "type": "Theorem",
        "header": "Lemma",
        "label": "lem:abs_lt_implies_le",
        "claim": "∀ x : ℝ, |x| < 2 → x ≤ 2.",
        "proof": [
          {
            "type": "let_statement",
            "variable_name": "x",
            "variable_type": "ℝ",
            "statement": "let x : ℝ"
          },
          {
            "type": "assume_statement",
            "assumption": "|x| < 2"
          },
          {
            "type": "assert_statement",
            "claim": "x ≤ |x|",
            "internal_references": [
              {
                "target_identifier": "lem:abs_bounds"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "x < 2",
            "proof_method": "transitivity of ≤ and <",
            "results_used": [
              {
                "statement": "x ≤ |x|"
              },
              {
                "statement": "|x| < 2"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "x ≤ 2",
            "internal_references": [
              {
                "target_identifier": "lem:strict_to_weak_inequality"
              }
            ]
          }
        ]
      },
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:2_upper_bound",
        "claim": "∀ x ∈ S, x ≤ 2.",
        "proof": [
          {
            "type": "let_statement",
            "variable_name": "x",
            "variable_type": "ℝ",
            "statement": "let x : ℝ"
          },
          {
            "type": "assume_statement",
            "assumption": "x² < 4"
          },
          {
            "type": "assert_statement",
            "claim": "0 ≤ x²",
            "internal_references": [
              {
                "target_identifier": "lem:nonnegativity_of_squares"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "sqrt (x²) < sqrt 4",
            "internal_references": [
              {
                "target_identifier": "lem:sqrt_strict_monotonicity"
              }
            ]
          },
          {
            "type": "calculation",
            "inline_calculation": "sqrt 4 = 2"
          },
          {
            "type": "assert_statement",
            "claim": "sqrt (x²) < 2",
            "results_used": [
              {
                "statement": "sqrt (x²) < sqrt 4"
              },
              {
                "statement": "sqrt 4 = 2"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "|x| < 2",
            "internal_references": [
              {
                "target_identifier": "lem:sqrt_of_square_abs"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "x ≤ 2",
            "internal_references": [
              {
                "target_identifier": "lem:abs_lt_implies_le"
              }
            ]
          },
          {
            "type": "conclude_statement"
          }
        ]
      }
    ]
  }
}

def token_upper_bound := 17306214056521062952

  -- #check "Obtained definition"
  -- def S : Set ℝ :=
  --   {x : ℝ | x ^ 2 < 4}
  -- theorem sq_nonneg : ∀ (x : ℝ), 0 ≤ x ^ 2 := by
  --   intro x
  --   grind only [sq_nonneg]
  -- theorem Real.sqrt_lt_sqrt_of_lt : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a < b → √a < √b :=
  --   by
  --   intro a b a_12938181604182621644 a_7744281164240614283 a_3587416207184603997
  --   simp [*]
  -- theorem Real.sqrt_sq_eq_abs : ∀ (x : ℝ), √(x ^ 2) = |x| :=
  --   by
  --   intro x
  --   grind only [Real.sqrt_sq_eq_abs]
  -- theorem le_of_lt : ∀ (a b : ℝ), a < b → a ≤ b :=
  --   by
  --   intro a b a_3587416207184603997
  --   grind only
  -- theorem neg_abs_le_self_and_le_abs_self : ∀ (x : ℝ), -|x| ≤ x ∧ x ≤ |x| :=
  --   by
  --   intro x
  --   grind only [= abs.eq_1, = max_def, #06dc, #53e0]
  -- theorem le_two_of_abs_lt_two : ∀ (x : ℝ), |x| < 2 → x ≤ 2. :=
  --   by
  --   intro x a_1787929219205045104
  --   have assert_8630539109063079629 : x ≤ |x| := by exact le_abs_self x
  --   have assert_17218785322226634807 : x < 2 := by
  --     exact Std.lt_of_le_of_lt assert_8630539109063079629 a_1787929219205045104
  --   have assert_12025421597626202246 : x ≤ 2 := by exact Std.le_of_lt assert_17218785322226634807
  --   repeat (sorry)
  -- theorem forall_mem_le_two :
  --     ∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OfNat α 2] (S : Set α), ∀ x ∈ S, x ≤ 2 :=
  --   by
  --   intro α inst inst_1 S x a_4792428952860197205
  --   have assert_15734687952764213268 : ∀ {x : ℝ}, x ^ 2 < 4 → 0 ≤ x ^ 2 := by
  --     exact fun {x} a => sq_nonneg x
  --   have assert_1747243453933795116 : ∀ {x : ℝ}, x ^ 2 < 4 → √(x ^ 2) < √4 := by
  --     exact fun {x} a => Real.sqrt_lt_sqrt (assert_15734687952764213268 a) a
  --   have assert_17136405317911211713 : ∀ (xℝ : ℝ), xℝ ^ 2 < 4 → √4 = 2 := by
  --     first
  --     | linarith
  --     | ring
  --     | norm_num
  --     | simp
  --     | omega
  --     | rfl
  --   have assert_11677213053849264783 : ∀ {x : ℝ}, x ^ 2 < 4 → √(x ^ 2) < 2 := by repeat (sorry)
  --   have assert_12101129085378509576 : ∀ {x : ℝ}, x ^ 2 < 4 → |x| < 2 := by repeat (sorry)
  --   have assert_12025421597626202246 : x ≤ 2 := by repeat (sorry)
  --   assumption

/- ## Rerun -/

def token_rerun := 301810945135539704

-- #codegen_async token_rerun
