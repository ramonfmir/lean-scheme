import sheaves.stalk
import sheaves.presheaf_of_rings

universe u 

section stalk_of_rings

variables {α : Type u} [T : topological_space α] 
variables (F : presheaf_of_rings α) (x : α)

definition stalk_of_rings := stalk F.to_presheaf_of_types x

end stalk_of_rings
