import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

open topological_space
open classical
open localization
open localization_alt

section res_to_inter_left

-- We are given U and V in {D(f)} and V ⊆ U and we generalize the results that
-- we already proved in properties. We deduce that there's a map from
-- R[1/S(V)] to R[1/S(U ∩ V)].

variables {R : Type u} [comm_ring R]
variables {U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R)

include BU BV

-- V ⊆ U → S(U) ⊆ R[1/S(U ∩ V)]*.

def inverts_data.res_inter_left.of_basis_subset
: inverts_data 
    (S U) 
    (of : R → localization R (S (U ∩ V))) :=
begin
  intros s,
  rcases s with ⟨s, HsSU⟩,
  have HUVU : U ∩ V ⊆ U := set.inter_subset_left U V,
  have HSUSUV := S.rev_mono HUVU,
  have HsSUV := HSUSUV HsSU,
  use ⟦⟨1, ⟨s, HsSUV⟩⟩⟧,
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp,
end

-- The induced map is the restriction map in the structure presheaf.

def structure_presheaf_on_basis.res_to_inter_left
: localization R (S U) 
→ localization R (S (U ∩ V)) :=
is_localization_initial 
  (S U)
  (of : R → localization R (S U))
  (of.is_localization_data (S U))
  (of : R → localization R (S (U ∩ V)))
  (inverts_data.res_inter_left.of_basis_subset BU BV)

instance structure_presheaf_on_basis.res_inter_left.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res_to_inter_left BU BV) :=
by simp [structure_presheaf_on_basis.res_to_inter_left]; by apply_instance

end res_to_inter_left

-- The maps coincide.

section res_to_inter_left_eq

variables {R : Type u} [comm_ring R]

lemma structure_presheaf_on_basis.res_inter_left_eq
: @sheaf_on_standard_basis.res_to_inter_left (Spec R) _ (D_fs R) _
    (D_fs_standard_basis R) 
    (structure_presheaf_on_basis R).to_presheaf_on_basis
  = @structure_presheaf_on_basis.res_to_inter_left R _ :=
begin
  apply funext, intro U,
  apply funext, intro V,
  apply funext, intro BU,
  apply funext, intro BV,
  have BUV := (D_fs_standard_basis R).2 BU BV,
  apply funext, intro x,
  -- x ∈ R[1/S(U ∩ V)].
  apply quotient.induction_on x,
  rintros ⟨a, b⟩,
  -- Destruct.
  simp [structure_presheaf_on_basis.res_to_inter_left, is_localization_initial],
  rcases ((of.is_localization_data (S U)).has_denom ⟦(a, b)⟧) with ⟨⟨q, p⟩, Hpq⟩,
  rcases inverts_data.res_inter_left.of_basis_subset BU BV q with ⟨w, Hw⟩,
  dsimp only [subtype.coe_mk] at *,
  revert Hw,
  -- Induction on w.
  apply quotient.induction_on w,
  rintros ⟨c, d⟩ Hw,
  apply quotient.sound,
  erw quotient.eq at Hpq,
  erw quotient.eq at Hw,
  rcases Hpq with ⟨t, ⟨Ht, Hpq⟩⟩; 
  simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at Hpq,
  rcases Hw with ⟨s, ⟨Hs, Hw⟩⟩; 
  simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at Hw,
  -- Kill it.
  have HUVU : U ∩ V ⊆ U := set.inter_subset_left U V,
  have HSUSUV := S.rev_mono HUVU,
  have HtSUV := HSUSUV Ht,
  use [s * t, is_submonoid.mul_mem Hs HtSUV],
  simp [-sub_eq_add_neg],
  rw sub_mul,
  rw sub_eq_zero,
  repeat { rw ←mul_assoc, },
  iterate 2 { rw [mul_assoc _ _ t, mul_comm _ t, ←mul_assoc] },
  erw Hpq,
  symmetry,
  iterate 1 { rw [mul_assoc _ _ s, mul_comm _ s, ←mul_assoc] },
  rw Hw,
  ring,
end

end res_to_inter_left_eq
