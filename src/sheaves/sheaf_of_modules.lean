/-
  Sheaf of modules.
-/

import data.equiv.algebra
import topology.opens
import sheaves.sheaf_of_abelian_groups
import sheaves.sheaf_of_rings
import algebra.module

open topological_space

universes u v

-- Definition of a sheaf of modules.

structure sheaf_of_modules {α : Type u} [topological_space α] (ℛ : sheaf_of_rings α) :=
(ℳ : sheaf_of_abelian_groups α)
[module : ∀ U, module (ℛ.F U) (ℳ.F U)]
(Fres : ∀ (U V) (HVU : V ⊆ U) (r : ℛ.F U) (m : ℳ.F U),
  ℳ.F.res _ _ HVU (r • m) = ℛ.F.res _ _ HVU r • ℳ.F.res _ _ HVU m)

attribute [instance] sheaf_of_modules.module

namespace sheaf_of_modules

instance (α : Type u) [topological_space α] (ℛ : sheaf_of_rings α) : has_coe_to_fun (sheaf_of_modules ℛ) :=
{ F := λ _, opens α → Type u,
  coe := λ F, F.ℳ.F.to_presheaf.F }

-- Morphism of presheaf of ℛ-modules

variables {α : Type u} [topological_space α] {ℛ : sheaf_of_rings α}

structure morphism (𝒜 ℬ : sheaf_of_modules ℛ) :=
(φ : presheaf_of_add_comm_groups.morphism 𝒜.ℳ.F ℬ.ℳ.F)
(is_module_hom : ∀ U, ∀ r : ℛ U, ∀ a : 𝒜 U, r • φ.map U a = φ.map U (r • a))

infix `⟶`:80 := morphism

def identity (𝒜 : sheaf_of_modules ℛ) : 𝒜 ⟶ 𝒜 :=
{ φ :=
  { map := λ U, id,
    commutes := begin rintros, refl end,
    add_group_homs := begin rintros, constructor end },
  is_module_hom := begin rintros, refl end }

-- Isomorphic presheaves of rings.

#exit

structure iso (𝒜 ℬ : sheaf_of_modules ℛ) :=
(mor : 𝒜 ⟶ ℬ)
(inv : ℬ ⟶ 𝒜)
(mor_inv_id : mor.to_morphism ⊚ inv.to_morphism = presheaf.id F.to_presheaf)
(inv_mor_id : inv.to_morphism ⊚ mor.to_morphism = presheaf.id G.to_presheaf)

infix `≅`:80 := λ A B, nonempty (iso A B)

-- Equality lemma

lemma presheaf_of_rings_eq_of_subset_eq (F : presheaf_of_rings α) (U V : opens α)
: U = V → ring_equiv (F U) (F V) :=
λ h, by rw h; by apply ring_equiv.refl

end presheaf_of_rings
