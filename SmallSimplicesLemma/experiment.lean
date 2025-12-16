import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

open Nat

#leanaide_connect

#theorem : "There are 7 prime numbers" >> translate_theorem

def mSimplex (n m: ℕ) := stdSimplex ((Fin n → ℝ)) (Fin m)
