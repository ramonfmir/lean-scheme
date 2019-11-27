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

instance : has_coe_to_fun (presheaf_of_rings_on_basis α HB) :=
{ F := λ _, Π {U}, U ∈ B → Type*,
  coe := λ F, (presheaf_of_rings_on_basis.to_presheaf_on_basis F).F }

-- Morphism of presheaf of rings on basis.

structure morphism (F G : presheaf_of_rings_on_basis α HB) 
extends presheaf_on_basis.morphism 
F.to_presheaf_on_basis G.to_presheaf_on_basis :=
(ring_homs : ∀ {U} (BU : U ∈ B), is_ring_hom (map BU))

infix `⟶`:80 := morphism 

-- Isomorphic presheaves of rings on basis.

structure iso (F G : presheaf_of_rings_on_basis α HB) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor.to_morphism ⊚ inv.to_morphism = presheaf_on_basis.id F.to_presheaf_on_basis)
(inv_mor_id : inv.to_morphism ⊚ mor.to_morphism = presheaf_on_basis.id G.to_presheaf_on_basis)

end presheaf_of_rings_on_basis
