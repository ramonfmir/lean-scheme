/-
    Stalk of rings on basis.

    https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import topology.basic
import sheaves.stalk_on_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

section stalk_of_rings_on_basis

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α )} {HB : opens.is_basis B}
variables (F : presheaf_of_rings_on_basis α HB) (x : α)

definition stalk_of_rings_on_basis := 
stalk_on_basis F.to_presheaf_on_basis x

end stalk_of_rings_on_basis
