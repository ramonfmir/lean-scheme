import topology.basic
import sheaves.presheaf_of_rings
import sheaves.stalk_of_rings
import sheaves.stalk_of_rings_is_ring

universes u w

open topological_space

variables {α : Type u} [topological_space α] 
variables (F : presheaf_of_rings α) (x : α)

section stalk_universal_property

variables (S : Type w) [comm_ring S] [decidable_eq S]
variables (G : Π U, F.F U → S) [HG : Π U, is_ring_hom (G U)]
variables (hg : ∀ U V (H : U ⊆ V) r, G U (F.res V U H r) = G V r)

def to_stalk (U : opens α) (HxU : x ∈ U) (s : F.F U) : stalk_of_rings F x 
:= ⟦{U := U, HxU := HxU, s := s}⟧

lemma to_stalk.is_ring_hom (U) (HxU) : is_ring_hom (to_stalk F x U HxU) :=
{ map_one := quotient.sound $
    begin
        use [U, HxU, (set.subset.refl _), (λ x Hx, trivial)],
        erw (F.res_is_ring_hom U U _).map_one,
        erw (F.res_is_ring_hom opens.univ U _).map_one,
    end,
  map_add := λ y z, quotient.sound $
    begin
        use [U, HxU, (set.subset.refl _), (λ x Hx, ⟨Hx, Hx⟩)],
        erw ←(F.res_is_ring_hom _ _ _).map_add,
        rw presheaf.Hcomp',
    end, 
  map_mul := λ y z, quotient.sound $
    begin
        use [U, HxU, (set.subset.refl _), (λ x Hx, ⟨Hx, Hx⟩)],
        erw ←(F.res_is_ring_hom _ _ _).map_mul,
        rw presheaf.Hcomp',
    end, }

include hg

protected def to_stalk.rec (y : stalk_of_rings F x) : S :=
begin
    apply quotient.lift_on' y (λ Us, G Us.1 Us.3),
    rintros ⟨U, HxU, s⟩ ⟨V, HxV, t⟩ ⟨W, HxW, HWU, HWV, Hres⟩,
    dsimp,
    rw ←hg W U HWU s,
    rw ←hg W V HWV t,
    rw Hres,
end

theorem to_stalk.rec_to_stalk (U HxU s) 
: to_stalk.rec F x S G hg (to_stalk F x U HxU s) = G U s := rfl

include HG

--set_option pp.all true

lemma to_stalk.rec_is_ring_hom : is_ring_hom (to_stalk.rec F x S G hg) :=
{ map_one := (HG opens.univ).map_one ▸ rfl,
  map_add := λ y z, quotient.induction_on₂' y z $ λ ⟨U, HxU, s⟩ ⟨V, HxV, t⟩,
    begin
        show G (U ∩ V) (_ + _) = G _ _ + G _ _,
        rw (HG (U ∩ V)).map_add,
        rw ←hg (U ∩ V) U (set.inter_subset_left _ _),
        rw ←hg (U ∩ V) V (set.inter_subset_right _ _),
    end,
  map_mul := λ y z, quotient.induction_on₂' y z $ λ ⟨U, HxU, s⟩ ⟨V, HxV, t⟩,
    begin
        show G (U ∩ V) (_ * _) = G _ _ * G _ _,
        rw (HG (U ∩ V)).map_mul,
        rw ←hg (U ∩ V) U (set.inter_subset_left _ _),
        rw ←hg (U ∩ V) V (set.inter_subset_right _ _),
    end }

end stalk_universal_property

-- Locally ringed spaces

structure locally_ringed_space {X : Type u} [topological_space X] :=
(F       : sheaf_of_rings X)
(Hstalks : ∀ x, is_local_ring (stalk_of_rings F.F x))
