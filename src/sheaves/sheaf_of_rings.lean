import sheaves.sheaf_of_types
import sheaves.presheaf_of_rings

universes u

-- A sheaf of rings is essentially a sheaf of types because we assume that the 
-- category of commutative rings has limits (proved later). This is tag 0073.

structure sheaf_of_rings (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_rings α)
(locality : locality F.to_presheaf_of_types)
(gluing   : gluing F.to_presheaf_of_types)

variables {β : Type u} [T : topological_space β]
include T
instance : has_coe (sheaf_of_rings β) (presheaf_of_rings β) := 
⟨λ S, S.F⟩

def is_sheaf_of_rings {α : Type u} [T : topological_space α] (F : presheaf_of_rings α) :=
locality F.to_presheaf_of_types ∧ gluing F.to_presheaf_of_types
