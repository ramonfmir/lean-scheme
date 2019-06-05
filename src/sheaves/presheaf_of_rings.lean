/-
  Presheaf of rings.

  https://stacks.math.columbia.edu/tag/006N
-/

import data.equiv.algebra
import topology.opens
import sheaves.presheaf

open topological_space

universes u v

-- Definition of a presheaf of rings.

structure presheaf_of_rings (α : Type u) [topological_space α] 
extends presheaf α :=
(Fring           : ∀ (U), comm_ring (F U))
(res_is_ring_hom : ∀ (U V) (HVU : V ⊆ U), is_ring_hom (res U V HVU))

instance (α : Type u) [topological_space α] : has_coe_to_fun (presheaf_of_rings α) :=
{ F := λ _, opens α → Type v,
  coe := λ F, (presheaf_of_rings.to_presheaf F).F }

attribute [instance] presheaf_of_rings.Fring
attribute [instance] presheaf_of_rings.res_is_ring_hom

namespace presheaf_of_rings

variables {α : Type u} {β : Type v} [topological_space α] [topological_space β]

-- Morphism of presheaf of rings.

structure morphism (F G : presheaf_of_rings α)
extends presheaf.morphism F.to_presheaf G.to_presheaf :=
(ring_homs : ∀ (U), is_ring_hom (map U))

infix `⟶`:80 := morphism 

def identity (F : presheaf_of_rings α) : F ⟶ F :=
{ ring_homs := λ U, is_ring_hom.id,
  ..presheaf.id F.to_presheaf }

-- Isomorphic presheaves of rings.

structure iso (F G : presheaf_of_rings α) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor.to_morphism ⊚ inv.to_morphism = presheaf.id F.to_presheaf)
(inv_mor_id : inv.to_morphism ⊚ mor.to_morphism = presheaf.id G.to_presheaf)

infix `≅`:80 := λ A B, nonempty (iso A B)

-- Equality lemma

lemma presheaf_of_rings_eq_of_subset_eq (F : presheaf_of_rings α) (U V : opens α) 
: U = V → ring_equiv (F U) (F V) :=
λ h, by rw h; by apply ring_equiv.refl

end presheaf_of_rings
