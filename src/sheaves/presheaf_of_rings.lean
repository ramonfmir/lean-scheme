import sheaves.presheaf_of_types

universe u

-- Definition of a presheaf of rings.

structure presheaf_of_rings (α : Type u) [T : topological_space α] 
extends presheaf_of_types α :=
(Fring           : ∀ {U} (OU : T.is_open U), comm_ring (F OU))
(res_is_ring_hom : ∀ {U V} (OU : T.is_open U) (OV : T.is_open V) (HVU : V ⊆ U),
  is_ring_hom (res OU OV HVU))

attribute [instance] presheaf_of_rings.Fring
attribute [instance] presheaf_of_rings.res_is_ring_hom

namespace presheaf_of_rings

variables {α : Type u} [T : topological_space α]
include T

-- Morphism of presheaf of rings.

structure morphism (F G : presheaf_of_rings α)
extends presheaf_of_types.morphism F.to_presheaf_of_types G.to_presheaf_of_types :=
(ring_homs : ∀ {U} (OU : is_open U), is_ring_hom (map OU))

-- Isomorphic presheaves of rings.

def are_isomorphic (F G : presheaf_of_rings α) := 
∃ (fg : morphism F G) (gf : morphism G F),
    presheaf_of_types.morphism.is_identity (fg.to_morphism ⊚ gf.to_morphism)
  ∧ presheaf_of_types.morphism.is_identity (gf.to_morphism ⊚ fg.to_morphism)

end presheaf_of_rings
