/-
  Sheaf of rings.
  
  https://stacks.math.columbia.edu/tag/0071
-/

import sheaves.sheaf
import sheaves.presheaf_of_rings

universes u

-- A sheaf of rings is essentially a sheaf of types because we assume that the 
-- category of commutative rings has limits (proved later). This is tag 0073.

structure sheaf_of_rings (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_rings α)
(locality : locality F.to_presheaf)
(gluing   : gluing F.to_presheaf)

section sheaf_of_rings

def is_sheaf_of_rings {α : Type u} [topological_space α] (F : presheaf_of_rings α) :=
  locality F.to_presheaf 
∧ gluing F.to_presheaf

end sheaf_of_rings
