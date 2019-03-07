import topology.basic
import topology.continuity
import ring_theory.localization
import sheaves.presheaf_of_rings
import sheaves.stalk_of_rings
import sheaves.stalk_of_rings_is_ring

universes u v w

open topological_space

section stalk_universal_property

variables {α : Type u} [topological_space α] 
variables (F : presheaf_of_rings α) (x : α)

variables (S : Type w) [comm_ring S] [decidable_eq S]
variables (G : Π U, F.F U → S) [HG : Π U, is_ring_hom (G U)]
variables (hg : ∀ U V (H : U ⊆ V) r, G U (F.res V U H r) = G V r)

def to_stalk (U : opens α) (HxU : x ∈ U) (s : F.F U) : stalk_of_rings F x 
:= ⟦{U := U, HxU := HxU, s := s}⟧

lemma to_stalk.is_ring_hom (U) (HxU) : is_ring_hom (to_stalk F x U HxU) :=
{ map_one := quotient.sound $ ⟨U, HxU, set.subset.refl _, λ x Hx, trivial,
    begin
        erw (F.res_is_ring_hom _ _ _).map_one, 
        erw (F.res_is_ring_hom _ _ _).map_one,
    end⟩,
  map_add := λ y z, quotient.sound $ ⟨U, HxU, set.subset.refl _, λ x Hx, ⟨Hx, Hx⟩,
    begin
        erw ←(F.res_is_ring_hom _ _ _).map_add,
        erw presheaf.Hcomp',
    end⟩, 
  map_mul := λ y z, quotient.sound $ ⟨U, HxU, set.subset.refl _, λ x Hx, ⟨Hx, Hx⟩,
    begin
        erw ←(F.res_is_ring_hom _ _ _).map_mul,
        erw presheaf.Hcomp',
    end⟩ }

include hg

protected def to_stalk.rec (y : stalk_of_rings F x) : S :=
quotient.lift_on' y (λ Us, G Us.1 Us.3) $ 
λ ⟨U, HxU, s⟩ ⟨V, HxV, t⟩ ⟨W, HxW, HWU, HWV, Hres⟩,
begin 
    dsimp,
    rw [←hg W U HWU s, ←hg W V HWV t, Hres],
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

-- Locally ringed spaces.

structure locally_ringed_space (X : Type u) [topological_space X] :=
(O       : sheaf_of_rings X)
(Hstalks : ∀ x, is_local_ring (stalk_of_rings O.F x))

-- Morphism of locally ringed spaces.

section fmap

variables {A : Type u} [topological_space A]
variables {B : Type v} [topological_space B] 
variables (f : A → B) (Hf : continuous f) 

def cts_inv : opens B → opens A := 
λ U, ⟨f ⁻¹' U.1, Hf U.1 U.2⟩ 

lemma cts_inv_mono : ∀ {V U}, V ⊆ U → cts_inv f Hf V ⊆ cts_inv f Hf U :=
λ V U HVU, set.preimage_mono HVU

structure fmap (F : presheaf A) (G : presheaf B) :=
(map      : ∀ (U), G U → F (cts_inv f Hf U))
(commutes : ∀ (U V) (HVU : V ⊆ U),
  (map V) ∘ (G.res U V HVU)
= (F.res (cts_inv f Hf U) (cts_inv f Hf V) (cts_inv_mono f Hf HVU)) ∘ (map U))

end fmap

section fmap_comp

variables {A : Type u} [topological_space A] {F : presheaf A}
variables {B : Type v} [topological_space B] {G : presheaf B}
variables {C : Type w} [topological_space C] {H : presheaf C}
variables {f : A → B} [Hf : continuous f] 
variables {g : B → C} [Hg : continuous g]

def fmap_comp (FG : fmap f Hf F G) (GH : fmap g Hg G H) 
: fmap (g ∘ f) (continuous.comp Hf Hg) F H :=
{ map := λ U, (FG.map (cts_inv g Hg U)) ∘ (GH.map U),
  commutes := 
  begin
    intros U V HVU,
    rw function.comp.assoc _ _ (H.res _ _ _),
    rw GH.commutes,
    rw ←function.comp.assoc _ _ (GH.map _),
    rw FG.commutes,
    refl,
  end, }

end fmap_comp

-- Morphism of locally ringed spaces.
-- TODO: Work on coercions.

structure morphism {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
(OX : locally_ringed_space X) (OY : locally_ringed_space Y) :=
(f  : X → Y)
(Hf : continuous f)
(fO : fmap f Hf OX.O.F.to_presheaf OY.O.F.to_presheaf)

namespace morphism

variables {A : Type u} [topological_space A]
variables {B : Type v} [topological_space B] 
variables {C : Type w} [topological_space C] 
variable {OA : locally_ringed_space A}
variable {OB : locally_ringed_space B}
variable {OC : locally_ringed_space C}

def comp (F : morphism OA OB) (G : morphism OB OC) : morphism OA OC :=
{ f := G.f ∘ F.f,
  Hf := continuous.comp F.Hf G.Hf,
  fO := @fmap_comp _ _ _ _ _ _ _ _ _ _ F.Hf _ G.Hf F.fO G.fO, }

infixl `⊚`:80 := comp

def is_identity (F : morphism OA OA) := F.f = id

def is_isomorphism (F : morphism OA OB) :=
  ∃ G : morphism OB OA, 
    is_identity (F ⊚ G)
  ∧ is_identity (G ⊚ F)

end morphism
