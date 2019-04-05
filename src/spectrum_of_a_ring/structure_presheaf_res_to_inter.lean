import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_res
import spectrum_of_a_ring.structure_presheaf_res_to_inter_left

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

open topological_space
open classical
open localization
open localization_alt

section res_to_inter

-- We are given U and V in {D(f)} and V ⊆ U and we generalize the results that
-- we already proved in properties. We deduce that there's a map from
-- R[1/S(U)] to R[1/S(V ∩ W)].

variables {R : Type u} [comm_ring R]
variables {U V W : opens (Spec R)} 
variables (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (BW : W ∈ D_fs R)
variables (HVU : V ⊆ U) (HWU : W ⊆ U)

#check structure_presheaf_on_basis.res BU BV HVU -- loc  (powers (of (some BV))) 

include BU BV BW HVU HWU

-- V ⊆ U → S(U) ⊆ R[1/S(U ∩ V)]*.

def inverts_data.res_to_inter.of_basis_subset
: inverts_data 
    (S U) 
    (of : R → localization R (S (V ∩ W))) :=
begin
  intros s,
  rcases s with ⟨s, HsSU⟩,
  have HVWU : V ∩ W ⊆ U := set.subset.trans (set.inter_subset_left V W) HVU,
  have HSUSVW := S.rev_mono HVWU,
  have HsSVW := HSUSVW HsSU,
  use ⟦⟨1, ⟨s, HsSVW⟩⟩⟧,
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp,
end

-- The induced map is the restriction map in the structure presheaf.

def structure_presheaf_on_basis.res_to_inter
: localization R (S U) 
→ localization R (S (V ∩ W)) :=
is_localization_initial 
  (S U)
  (of : R → localization R (S U))
  (of.is_localization_data (S U))
  (of : R → localization R (S (V ∩ W)))
  (inverts_data.res_to_inter.of_basis_subset BU BV BW HVU HWU)

instance structure_presheaf_on_basis.res_inter.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
by simp [structure_presheaf_on_basis.res_to_inter]; by apply_instance

end res_to_inter

variables {R : Type u} [comm_ring R]
variables {U V W : opens (Spec R)} 
variables (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (BW : W ∈ D_fs R)
variables (HVU : V ⊆ U) (HWU : W ⊆ U)

lemma structure_presheaf_on_basis.res_to_inter_eq_left :
  structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU 
= structure_presheaf_on_basis.res_to_inter_left BV BW
∘ structure_presheaf_on_basis.res BU BV HVU :=
begin
  sorry,
end


-- lemma structure_presheaf_on_basis.res_to_inter_eq_right :
--   structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU 
-- = structure_presheaf_on_basis.res_to_inter_right BV BW
-- ∘ structure_presheaf_on_basis.res BU BW HWU :=
-- begin
--   sorry,
-- end

-- lemma structure_presheaf_on_basis.res_to_inter_eq_right' : ∀ a : R,
--   structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU a
-- = structure_presheaf_on_basis.res_to_inter_right BV BW
--   (structure_presheaf_on_basis.res BU BW HWU a):=
-- begin
--   sorry,
-- end