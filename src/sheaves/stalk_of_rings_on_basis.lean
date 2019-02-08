/-
    Stalk of rings on basis.

    https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import topology.basic
import sheaves.stalk_on_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

section stalk_of_rings_on_basis

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α )} {HB : opens.is_basis B}
variables (F : presheaf_of_rings_on_basis α HB) (x : α)

definition stalk_of_rings_on_basis := 
stalk_on_basis F.to_presheaf_on_basis x

--------------
-- tag 007N --
--------------

section stalk_is_ring

-- Zero.

private def stalk_of_rings_zero : stalk_of_rings_on_basis F x := 
⟦{U := ⟨set.univ, is_open_univ⟩, BU := sorry, Hx := trivial, s:= 0}⟧

instance ring_stalk_has_zero : has_zero (stalk_of_rings_on_basis F x) := 
{zero := stalk_of_rings_zero F x}

-- One.

private def stalk_of_rings_one : stalk_of_rings_on_basis F x := 
⟦{U := ⟨set.univ, is_open_univ⟩, BU := sorry, Hx := trivial, s:= 0}⟧

instance ring_stalk_has_one : has_one (stalk_of_rings_on_basis F x) := 
{one := stalk_of_rings_one F x}

-- Add.

private def stalk_of_rings_add_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := sorry, -- We need to assume standard basis?
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s + 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_add : has_add (stalk_of_rings_on_basis F x) := sorry

-- Sub.

private def stalk_sub_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s, ⟦{U := s.U, BU := s.BU, Hx := s.Hx, s := -s.s}⟧

instance stalk_of_rings_has_sub : has_sub (stalk_of_rings_on_basis F x) := sorry

-- Mul.

private def stalk_of_rings_mul_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := sorry, -- We need to assume standard basis?
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s * 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_mul : has_mul (stalk_of_rings_on_basis F x) := sorry

-- Assoc, comm, distr...

end stalk_is_ring

end stalk_of_rings_on_basis