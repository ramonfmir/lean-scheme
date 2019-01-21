import sheaves.presheaf_of_types

universe u

-- Definition of a presheaf of rings.

structure presheaf_of_rings (α : Type u) [T : topological_space α] 
extends presheaf_of_types α :=
[Fring           : ∀ {U} (OU : T.is_open U), comm_ring (F OU)]
(res_is_ring_hom : ∀ {U V} (HUV : V ⊆ U) (OU : T.is_open U) (OV : T.is_open V),
  is_ring_hom (res OU OV HUV))

attribute [instance] presheaf_of_rings.Fring

namespace presheaf_of_rings

-- Morphism of presheaf of rings

structure morphism {α : Type u} [T : topological_space α]
(F G : presheaf_of_rings α)
extends presheaf_of_types.morphism F.to_presheaf_of_types G.to_presheaf_of_types :=
(ring_homs : ∀ (U : set α) (OU : is_open U), is_ring_hom (map OU))

-- Isomorphic presheaves of rings.

def are_isomorphic {α : Type u} [T : topological_space α]
(F G : presheaf_of_rings α) : Prop := 
∃ (fg : morphism F G) (gf : morphism G F),
    presheaf_of_types.morphism.is_identity (fg.to_morphism ⊚ gf.to_morphism)
  ∧ presheaf_of_types.morphism.is_identity (gf.to_morphism ⊚ fg.to_morphism)

end presheaf_of_rings
