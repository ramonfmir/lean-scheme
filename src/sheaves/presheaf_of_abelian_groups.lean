/-
  Presheaf of abelian groups.

  https://stacks.math.columbia.edu/tag/006N
-/

import data.equiv.algebra
import topology.opens
import sheaves.presheaf

open topological_space

universes u

-- Definition of a presheaf of abelian groups.

structure presheaf_of_add_comm_groups (α : Type u) [topological_space α]
extends presheaf α :=
(Fadd_comm_group           : ∀ (U), add_comm_group (F U))
(res_is_add_group_hom : ∀ (U V) (HVU : V ⊆ U), is_add_group_hom (res U V HVU))

instance (α : Type u) [topological_space α] : has_coe_to_fun (presheaf_of_add_comm_groups α) :=
{ F := λ _, opens α → Type u,
  coe := λ F, (presheaf_of_add_comm_groups.to_presheaf F).F }

attribute [instance] presheaf_of_add_comm_groups.Fadd_comm_group
attribute [instance] presheaf_of_add_comm_groups.res_is_add_group_hom

namespace presheaf_of_add_comm_groups

variables {α : Type u} [topological_space α]

-- Morphism of presheaf of add comm groups

structure morphism (F G : presheaf_of_add_comm_groups α)
extends presheaf.morphism F.to_presheaf G.to_presheaf :=
(add_group_homs : ∀ (U), is_add_group_hom (map U))

infix `⟶`:80 := morphism

def identity (F : presheaf_of_add_comm_groups α) : F ⟶ F :=
{ add_group_homs := λ U, is_add_group_hom.id,
  ..presheaf.id F.to_presheaf }

-- Isomorphic presheaves of rings.

structure iso (F G : presheaf_of_add_comm_groups α) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor.to_morphism ⊚ inv.to_morphism = presheaf.id F.to_presheaf)
(inv_mor_id : inv.to_morphism ⊚ mor.to_morphism = presheaf.id G.to_presheaf)

infix `≅`:80 := λ A B, nonempty (iso A B)

-- Equality lemma

lemma presheaf_of_add_comm_groups_eq_of_subset_eq (F : presheaf_of_add_comm_groups α) (U V : opens α)
: U = V → (F U) ≃+ (F V) :=
--λ h, by rw h; by apply add_grouxp_equiv.refl -- TODO why does ring_equiv.refl work??
λ h, by rw h

end presheaf_of_add_comm_groups
