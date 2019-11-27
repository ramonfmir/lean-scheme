/-
  Stalks of the structure sheaf are local rings.
-/

import ring_theory.ideals
import to_mathlib.localization.local_rings
import to_mathlib.localization.localization_of_iso
import to_mathlib.localization.localization_alt
import spectrum_of_a_ring.structure_presheaf_stalks
import spectrum_of_a_ring.structure_sheaf
import spectrum_of_a_ring.structure_presheaf_stalks
import sheaves.stalk_of_rings
import sheaves.sheaf_of_rings_on_standard_basis

universe u

open localization_alt

noncomputable theory

variables {R : Type u} [comm_ring R]
variables (P : Spec R)

def O := structure_sheaf R 

def O_P := stalk_of_rings O.F P 

-- We know it is a ring.

instance O_P.is_comm_ring : comm_ring (O_P P) :=
by simp [O_P]; by apply_instance

-- Now we use what we proved about the stalks on basis and the fact
-- that the extension doesn't change stalks to prove the property.

lemma structure_sheaf.stalk_local : local_ring (O_P P) :=
begin
  have Hbij := to_stalk_extension.bijective
    (D_fs_standard_basis R) 
    (structure_presheaf_on_basis R)
    P,
  haveI Hhom := to_stalk_extension.is_ring_hom
    (D_fs_standard_basis R) 
    (structure_presheaf_on_basis R)
    P,
  haveI Hhom2 := strucutre_presheaf_stalks.φP.is_ring_hom P,
  have Hloc := strucutre_presheaf_stalks.stalk_local.localization P,
  have Hloc' := is_localization_data.of_iso 
    (-P.1 : set R)
    (strucutre_presheaf_stalks.φ P)
    Hloc
    (to_stalk_extension _ _ P)
    Hbij
    Hhom,
  have : is_ring_hom (to_stalk_extension Bstd strucutre_presheaf_stalks.F P ∘ strucutre_presheaf_stalks.φ P),
    exact @is_ring_hom.comp _ _ _ _ 
      (strucutre_presheaf_stalks.φ P) _ _ _ 
      (to_stalk_extension _ _ P)
      Hhom,
  exact local_ring.of_is_localization_data_at_prime P.2 Hloc',
end
