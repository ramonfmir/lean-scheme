/-
  Same as covering bu thte Ui's are required to be on the basis. 
-/

import topology.basic
import to_mathlib.opens
import sheaves.covering.covering

universes u 

open topological_space

section covering_on_standard_basis

parameters {α : Type u} [topological_space α]
parameters (B : set (opens α)) [HB : opens.is_basis B]

-- Open cover for standard basis.

structure covering_standard_basis (U : opens α) extends covering U :=
(BUis : ∀ i, Uis i ∈ B)

end covering_on_standard_basis