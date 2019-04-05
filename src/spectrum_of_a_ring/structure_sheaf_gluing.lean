import ring_theory.localization
import preliminaries.localisation
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_res_to_inter

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

section structure_presheaf

open topological_space
open classical
open localization
open localization_alt

-- Needed.

variables {R : Type u} [comm_ring R]
variables {U V W : opens (Spec R)} 
variables (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (BW : W ∈ D_fs R) 
variables (HVU : V ⊆ U) (HWU : W ⊆ U)

lemma structure_presheaf.res_to_inter.inverts_data
: inverts_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
begin
  sorry,
end

lemma structure_presheaf.res_to_inter.has_denom_data
: has_denom_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
begin
  sorry,
end

lemma structure_presheaf.res_to_inter.ker_le
: ker (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) 
≤ submonoid_ann (powers ((of (some BV)) * (of (some BW)))) :=
begin 
  sorry,
end

lemma structure_presheaf.res_to_inter.localization
: is_localization_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
{ inverts := structure_presheaf.res_to_inter.inverts_data BU BV BW HVU HWU,
  has_denom := structure_presheaf.res_to_inter.has_denom_data BU BV BW HVU HWU, 
  ker_le := structure_presheaf.res_to_inter.ker_le BU BV BW HVU HWU }

end structure_presheaf