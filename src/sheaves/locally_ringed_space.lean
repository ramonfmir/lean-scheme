import topology.basic
import ring_theory.localization
import sheaves.presheaf_maps
import sheaves.presheaf_of_rings_maps
import sheaves.presheaf_of_rings
import sheaves.sheaf_of_rings
import sheaves.stalk_of_rings

universes u v w

open topological_space

-- Locally ringed spaces.

section locally_ringed_spaces

structure locally_ringed_space (X : Type u) [topological_space X] :=
(O       : sheaf_of_rings X)
(Hstalks : ∀ x, is_local_ring (stalk_of_rings O.F x))

-- Morphism of locally ringed spaces.

-- TODO: Work on coercions.

structure morphism {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
(OX : locally_ringed_space X) (OY : locally_ringed_space Y) :=
(f  : X → Y)
(Hf : continuous f)
(fO : presheaf.fmap Hf OX.O.F.to_presheaf OY.O.F.to_presheaf)

infix `⟶`:80 := morphism 

section morphism

variables {A : Type u} [topological_space A]
variables {B : Type v} [topological_space B] 
variables {C : Type w} [topological_space C] 
variable {OA : locally_ringed_space A}
variable {OB : locally_ringed_space B}
variable {OC : locally_ringed_space C}

def comp (F : morphism OA OB) (G : morphism OB OC) : morphism OA OC :=
{ f := G.f ∘ F.f,
  Hf := continuous.comp F.Hf G.Hf,
  fO := presheaf.fmap.comp F.fO G.fO, }

infixl `⊚`:80 := comp

def locally_ringed_space.id (OX : locally_ringed_space A) : morphism OX OX :=
{ f := id, 
  Hf := continuous_id,
  fO := presheaf.fmap.id OX.O.F, }

structure iso (OX : locally_ringed_space A) (OY : locally_ringed_space B) :=
(mor : OX ⟶ OY)
(inv : OY ⟶ OX)
(mor_inv_id : mor ⊚ inv = locally_ringed_space.id OX)
(inv_mor_id : inv ⊚ mor = locally_ringed_space.id OY)

infix `≅`:80 := iso

end morphism

end locally_ringed_spaces
