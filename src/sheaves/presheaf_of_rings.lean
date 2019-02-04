import sheaves.presheaf_of_types

universe u

-- Definition of a presheaf of rings.

structure presheaf_of_rings (α : Type u) [T : topological_space α] 
extends presheaf_of_types α :=
(Fring           : ∀ (U), comm_ring (F U))
(res_is_ring_hom : ∀ (U V) (HVU : V ⊆ U), is_ring_hom (res U V HVU))

attribute [instance] presheaf_of_rings.Fring
attribute [instance] presheaf_of_rings.res_is_ring_hom

namespace presheaf_of_rings

variables {α : Type u} [T : topological_space α]
include T

-- Morphism of presheaf of rings.

structure morphism (F G : presheaf_of_rings α)
extends presheaf_of_types.morphism F.to_presheaf_of_types G.to_presheaf_of_types :=
(ring_homs : ∀ (U), is_ring_hom (map U))

-- Isomorphic presheaves of rings.

def are_isomorphic (F G : presheaf_of_rings α) := 
∃ (fg : morphism F G) (gf : morphism G F),
    presheaf_of_types.morphism.is_identity (fg.to_morphism ⊚ gf.to_morphism)
  ∧ presheaf_of_types.morphism.is_identity (gf.to_morphism ⊚ fg.to_morphism)

end presheaf_of_rings
