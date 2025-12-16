import LeanAideCore
import Mathlib
set_option linter.style.commandStart false
set_option linter.style.longLine false

#leanaide_connect

def definition_eg1 := json% {
  "definition":{
  "label":" def:commutator_group",
  "header": "Definition",
  "name": "comm_group",
  "definition": "def ∀ (G:Type) [Group G],  G ⧸ commutator G"
 }
}

--#codegen definition_eg1
#theorem : "The GCD of 16 and 8 is 4" >> translate_theorem
