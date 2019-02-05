import sheaves.sheaf_of_types
import sheaves.presheaf_of_rings

universes u

-- A sheaf of rings is essentially a sheaf of types because we assume that the 
-- category of commutative rings has limits (proved later). This is tag 0073.

structure sheaf_of_rings (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_rings α)
(locality : presheaf_of_types.locality F.to_presheaf_of_types)
(gluing   : presheaf_of_types.gluing F.to_presheaf_of_types)

section sheaf_of_rings

variables {α : Type u} [T : topological_space α]
include T
instance : has_coe (sheaf_of_rings α) (presheaf_of_rings α) := 
⟨λ S, S.F⟩

def is_sheaf_of_rings (F : presheaf_of_rings α) :=
  presheaf_of_types.locality F.to_presheaf_of_types 
∧ presheaf_of_types.gluing F.to_presheaf_of_types

end sheaf_of_rings
