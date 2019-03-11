/-
  Presheaf of rings on basis.

  https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import sheaves.presheaf_on_basis

universe u 

open topological_space

structure presheaf_of_rings_on_basis (α : Type u) [TX : topological_space α] 
{B : set (opens α)} (HB : opens.is_basis B) 
extends presheaf_on_basis α HB :=
(Fring           : ∀ {U} (BU : U ∈ B), comm_ring (F BU))
(res_is_ring_hom : ∀ {U V} (BU : U ∈ B) (BV : V ∈ B) (HVU : V ⊆ U),
  is_ring_hom (res BU BV HVU))

attribute [instance] presheaf_of_rings_on_basis.Fring
attribute [instance] presheaf_of_rings_on_basis.res_is_ring_hom

namespace presheaf_of_rings_on_basis

variables {α : Type u} [topological_space α]
variables {B : set (opens α)} {HB : opens.is_basis B}

-- Morphism of presheaf of rings on basis.

structure morphism (F G : presheaf_of_rings_on_basis α HB) 
extends presheaf_on_basis.morphism 
F.to_presheaf_on_basis G.to_presheaf_on_basis :=
(ring_homs : ∀ {U} (BU : U ∈ B), is_ring_hom (map BU))

-- Isomorphic presheaves of rings on basis.

def are_isomorphic (F G : presheaf_of_rings_on_basis α HB) := 
∃ (fg : morphism F G) (gf : morphism G F),
    presheaf_on_basis.morphism.is_identity 
      (presheaf_on_basis.morphism.comp fg.to_morphism gf.to_morphism)
  ∧ presheaf_on_basis.morphism.is_identity 
      (presheaf_on_basis.morphism.comp gf.to_morphism fg.to_morphism)

end presheaf_of_rings_on_basis
