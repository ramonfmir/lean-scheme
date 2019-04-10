/-
  We show that R[1/S(D(f))] ≅ R[1/f]. Where S(U) := { r | U ⊆ D(r) }
-/

import to_mathlib.localization.localization_alt
import spectrum_of_a_ring.structure_presheaf

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

variables {R : Type u} [comm_ring R]

open topological_space
open classical
open localization
open localization_alt

section localization_property

-- Proof of the localization property. R[1/S(D(f))] ≃ R[1/f].

variables {U : opens (Spec R)} (BU : U ∈ D_fs R)

lemma structure_presheaf.inverts_data
: inverts_data 
    (powers (some BU)) 
    (of : R → localization R (S U)) :=
begin
  rintros ⟨s, Hs⟩,
  have HsS : s ∈ S (Spec.DO R (classical.some BU)) 
    := (is_submonoid.power_subset (S.f_mem (classical.some BU))) Hs,
  rw ←classical.some_spec BU at HsS,
  use [⟦⟨1, ⟨s, HsS⟩⟩⟧],
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp,
end

lemma structure_presheaf.has_denom_data
: has_denom_data 
    (powers (some BU)) 
    (of : R → localization R (S U)) :=
begin
  intros x,
  have Hx := quotient.exists_rep x,
  rcases (classical.indefinite_description _ Hx) with ⟨⟨p, q⟩, Hpq⟩,
  rcases q with ⟨q, Hq⟩,
  change U.val ⊆ Spec.D'(q) at Hq,
  rw classical.some_spec BU at Hq,
  have Hea := pow_eq.of_Dfs_subset Hq,
  rcases (classical.indefinite_description _ Hea) with ⟨a, He⟩,
  rcases (classical.indefinite_description _ He) with ⟨e, Hfe⟩,
  use [⟨⟨(classical.some BU)^e, ⟨e, rfl⟩⟩, a * p⟩],
  dsimp only [subtype.coe_mk],
  rw [Hfe, ←Hpq],
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  dsimp,
  ring,
end

lemma structure_presheaf.ker_le
: ker (of : R → localization R (S U)) ≤ submonoid_ann (powers (some BU)) :=
begin 
  intros x Hx,
  change localization.of x = 0 at Hx,
  erw quotient.eq at Hx,
  rcases Hx with ⟨s, ⟨Hs, Hx⟩⟩,
  simp at Hx,
  dsimp [S] at Hs,
  change U.val ⊆ Spec.D'(s) at Hs,
  rw classical.some_spec BU at Hs,
  have Hea := pow_eq.of_Dfs_subset Hs,
  rcases (classical.indefinite_description _ Hea) with ⟨a, He⟩,
  rcases (classical.indefinite_description _ He) with ⟨e, Hfe⟩,
  use [⟨x, ⟨(some BU)^e, ⟨e, rfl⟩⟩⟩],
  { dsimp only [subtype.coe_mk],
    rw [Hfe, mul_comm a, ←mul_assoc, Hx, zero_mul], },
  { refl, } 
end

lemma structure_presheaf.localization
: is_localization_data 
    (powers (some BU)) 
    (of : R → localization R (S U)) :=
{ inverts := structure_presheaf.inverts_data BU,
  has_denom := structure_presheaf.has_denom_data BU, 
  ker_le := structure_presheaf.ker_le BU }

end localization_property
