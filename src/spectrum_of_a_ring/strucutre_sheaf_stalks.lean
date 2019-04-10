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

def ℱ := structure_sheaf R 

def ℱP := stalk_of_rings ℱ.F P 

--

instance ℱP.is_comm_ring : comm_ring (ℱP P) :=
by simp [ℱP]; by apply_instance

--

lemma structure_sheaf.stalk_local : is_local_ring (ℱP P) :=
begin
  have Hbij := to_stalk_extension.bijective
    (D_fs_standard_basis R) 
    (structure_presheaf_on_basis R)
    (λ U BU OC, structure_presheaf_on_basis_is_sheaf_on_basis BU OC)
    P,
  haveI Hhom := to_stalk_extension.is_ring_hom
    (D_fs_standard_basis R) 
    (structure_presheaf_on_basis R)
    (λ U BU OC, structure_presheaf_on_basis_is_sheaf_on_basis BU OC)
    P,
  haveI Hhom2 := strucutre_presheaf_stalks.φP.is_ring_hom P,
  have Hloc := strucutre_presheaf_stalks.stalk_local.localization P,
  have Hloc' := is_localization_data.of_iso 
    (-P.1 : set R)
    (strucutre_presheaf_stalks.φ P)
    Hloc
    (to_stalk_extension _ _ _ P)
    Hbij
    Hhom,
  have : is_ring_hom (to_stalk_extension Bstd strucutre_presheaf_stalks.F _ P ∘ strucutre_presheaf_stalks.φ P),
    apply is_ring_hom.comp (strucutre_presheaf_stalks.φ P) (to_stalk_extension _ _ _ P),
    exact Hhom,
  
  use is_local_ring.of_is_localization_data_at_prime P.2 Hloc',
end
