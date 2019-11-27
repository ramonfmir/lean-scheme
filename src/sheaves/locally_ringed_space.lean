/-
  Locally ringed spaces.

  https://stacks.math.columbia.edu/tag/01HA
-/

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
(Hstalks : ∀ x, local_ring (stalk_of_rings O.F x))

-- Morphism of locally ringed spaces.

structure morphism {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
(OX : locally_ringed_space X) (OY : locally_ringed_space Y) :=
(f       : X → Y)
(Hf      : continuous f)
(fO      : presheaf_of_rings.fmap Hf OX.O.F OY.O.F)
(Hstalks : ∀ x s, 
    is_unit (presheaf_of_rings.fmap.induced OX.O.F OY.O.F fO x s) → is_unit s)

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
  Hf := continuous.comp G.Hf F.Hf,
  fO := presheaf.fmap.comp F.fO G.fO,
  Hstalks :=
    begin
      intros x s H,
      apply G.Hstalks,
      apply F.Hstalks,
      convert H,
      unfold presheaf.fmap.comp,
      unfold presheaf_of_rings.fmap.induced,
      unfold presheaf.fmap.induced,
      dsimp,
      apply quotient.induction_on s,
      rintros ⟨U, HxU, s⟩; simp,
      use [opens.comap F.Hf (opens.comap G.Hf U), HxU]; dsimp,
      use [(λ x Hx, Hx), (λ x Hx, Hx)],
      refl,
    end }

infixl `⊚`:80 := comp

def locally_ringed_space.id (OX : locally_ringed_space A) : morphism OX OX :=
{ f := id, 
  Hf := continuous_id,
  fO := presheaf.fmap.id OX.O.F.to_presheaf,
  Hstalks := 
    begin
      intros x a,
      unfold presheaf.fmap.id,
      unfold presheaf_of_rings.fmap.induced,
      unfold presheaf.fmap.induced,
      dsimp,
      apply quotient.induction_on a,
      rintros ⟨U, HxU, s⟩; simp,
      intros H,
      have HU : opens.comap continuous_id U = U,
      { unfold opens.comap,
        apply subtype.eq; dsimp,
        refl, },
      convert H,
      { use HU.symm, },
      { dsimp only [subtype.coe_mk],
        have Hid := OX.O.F.to_presheaf.Hid' U s,
        rw ←Hid,
        congr,
        { exact HU.symm, },
        { exact Hid.symm, }, },
    end }

structure iso (OX : locally_ringed_space A) (OY : locally_ringed_space B) :=
(mor : OX ⟶ OY)
(inv : OY ⟶ OX)
(mor_inv_id : mor ⊚ inv = locally_ringed_space.id OX)
(inv_mor_id : inv ⊚ mor = locally_ringed_space.id OY)

infix `≅`:80 := λ OX OY, nonempty (iso OX OY)

end morphism

end locally_ringed_spaces
