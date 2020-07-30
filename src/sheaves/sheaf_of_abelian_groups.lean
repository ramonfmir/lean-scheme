/-
  Sheaf of abelian groups.

-/

import sheaves.sheaf
import sheaves.presheaf_of_abelian_groups

universes u

-- A sheaf of rings is essentially a sheaf of types because we assume that the
-- category of commutative rings has limits (proved later). This is tag 0073.

structure sheaf_of_abelian_groups (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_add_comm_groups α)
(locality : locality F.to_presheaf)
(gluing   : gluing F.to_presheaf)

open topological_space

instance (α : Type u) [topological_space α] : has_coe_to_fun (sheaf_of_abelian_groups α) :=
{ F := λ _, opens α → Type u,
  coe := λ F, F.F.to_presheaf.F }

def is_sheaf_of_abelian_groups {α : Type u} [topological_space α] (F : presheaf_of_add_comm_groups α) :=
  locality F.to_presheaf
∧ gluing F.to_presheaf
