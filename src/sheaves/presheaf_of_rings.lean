/-
  Presheaf of rings.

  https://stacks.math.columbia.edu/tag/006N
-/

import sheaves.presheaf

universe u

-- Definition of a presheaf of rings.

structure presheaf_of_rings (α : Type u) [topological_space α] 
extends presheaf α :=
(Fring           : ∀ (U), comm_ring (F U))
(res_is_ring_hom : ∀ (U V) (HVU : V ⊆ U), is_ring_hom (res U V HVU))

attribute [instance] presheaf_of_rings.Fring
attribute [instance] presheaf_of_rings.res_is_ring_hom

namespace presheaf_of_rings

variables {α : Type u} [topological_space α]

-- Morphism of presheaf of rings.

structure morphism (F G : presheaf_of_rings α)
extends presheaf.morphism F.to_presheaf G.to_presheaf :=
(ring_homs : ∀ (U), is_ring_hom (map U))

-- Isomorphic presheaves of rings.

def are_isomorphic (F G : presheaf_of_rings α) := 
∃ (fg : morphism F G) (gf : morphism G F),
    presheaf.morphism.is_identity (fg.to_morphism ⊚ gf.to_morphism)
  ∧ presheaf.morphism.is_identity (gf.to_morphism ⊚ fg.to_morphism)

end presheaf_of_rings
