/-
    Stalk of rings.

    https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import topology.basic
import ring_theory.localization
import linear_algebra.multivariate_polynomial
import sheaves.stalk
import sheaves.presheaf_of_rings
import sheaves.sheaf_of_rings

universes u v w

open topological_space

section stalk_of_rings

variables {α : Type u} [topological_space α] 
variables (F : presheaf_of_rings α) (x : α)

definition stalk_of_rings := stalk F.to_presheaf x

end stalk_of_rings

section property

parameters {α : Type u} [topological_space α] 
parameters (F : presheaf_of_rings α) (x : α)

-- Copy paste proof for standard basis...

-- One.

private def stalk_of_rings_one : stalk_of_rings F x := 
⟦{U := opens.univ, HxU := trivial, s:= 1}⟧

instance stalk_of_rings_has_one : has_one (stalk_of_rings F x) := 
{one := stalk_of_rings_one}

instance stalk_of_rings_is_ring : comm_ring (stalk_of_rings F x) := 
{   add := sorry,
    add_assoc := sorry,
    zero := sorry,
    zero_add := sorry,
    add_zero := sorry,
    neg := sorry,
    add_left_neg := sorry,
    add_comm := sorry,
    mul := sorry,
    mul_assoc := sorry,
    one := stalk_of_rings_one,
    one_mul := sorry,
    mul_one := sorry,
    left_distrib := sorry,
    right_distrib := sorry,
    mul_comm := sorry,
}

parameters (J : Type u) [decidable_eq J]
parameters (O : J → opens α) [Π j, decidable_eq (O j)]
parameters (HO : ∀ j, x ∈ O j)

variables (S : Type w) [comm_ring S] [decidable_eq S]
variables (G : Π j, F.F (O j) → S) [Π j, is_ring_hom (G j)]
variables (hg : ∀ j k (H : O j ⊆ O k) r, G j (F.res (O k) (O j) H r) = G k r)

def to_stalk (j : J) (s : F.F (O j)) : stalk_of_rings F x 
:= ⟦{U := O j, HxU := HO j, s := s}⟧

--set_option pp.all true

lemma to_stalk.is_ring_hom (j) : is_ring_hom (to_stalk j) :=
{ map_one :=
    begin
        simp [to_stalk],
        simp [has_one.one, monoid.one, ring.one, comm_ring.one, stalk_of_rings_one],
        existsi (O j),
        existsi (HO j),
        existsi (set.subset.refl _),
        have H : (O j) ⊆ opens.univ := λ x Hx, trivial,
        existsi H,
        simp,
        dsimp,
        erw (F.res_is_ring_hom (O j) (O j) (set.subset.refl _)).map_one,
        erw (F.res_is_ring_hom opens.univ (O j) H).map_one,
    end,
  map_add := sorry, 
  map_mul := sorry, }

#check eval₂

protected def to_stalk.rec (y : stalk_of_rings F x) : S :=
begin
    have f : stalk.elem F.to_presheaf x → S,
        rintros ⟨U, HxU, s⟩,
        have := F.res (U) (O j)
    apply quotient.lift_on' y,
end

end property

-- Locally ringed spaces

structure locally_ringed_space {X : Type u} [topological_space X] :=
(F       : presheaf_of_rings X)
(Fsheaf  : is_sheaf_of_rings F)
(Hstalks : ∀ x, is_local_ring (stalk_of_rings F x))
