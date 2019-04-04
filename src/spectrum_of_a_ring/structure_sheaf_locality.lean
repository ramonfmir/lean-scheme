import ring_theory.localization
import preliminaries.localisation
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_restriction

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
variables {U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)

lemma structure_presheaf.res.inverts_data
: inverts_data 
    (powers (of (some BV))) 
    (structure_presheaf_on_basis.res BU BV H) :=
begin
  rintros ⟨s, Hs⟩,
  rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
  rw ←@is_semiring_hom.map_pow R _ _ _ of (@is_ring_hom.is_semiring_hom _ _ _ _ of of.is_ring_hom) _ _ at Hn,
  dsimp only [subtype.coe_mk],
  rw ←Hn,
  dsimp [structure_presheaf_on_basis.res],
  rw is_localization_initial_comp,
  have HgSV : some BV ∈ S V,
    intros x Hx,
    rw some_spec BV at Hx,
    exact Hx,
  have HgnSV : (some BV)^n ∈ S V := is_submonoid.pow_mem HgSV,
  --have HgnSU := S.mo
  --exact inverts_data.of_basis_subset BU BV H ⟨(some BV)^n, HgnSV⟩,
  sorry,
end

lemma structure_presheaf.res.has_denom_data
: has_denom_data 
    (powers (of (some BV))) 
    (structure_presheaf_on_basis.res BU BV H) :=
begin
  intros x,
  rcases (structure_presheaf.has_denom_data BV x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
  rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
  have HgSV : some BV ∈ S V,
    intros x Hx,
    rw some_spec BV at Hx,
    exact Hx,
  have HfnSU : (some BV)^n ∈ S V := is_submonoid.pow_mem HgSV,
  sorry,
end

lemma structure_presheaf.res.ker_le
: ker (structure_presheaf_on_basis.res BU BV H) ≤ submonoid_ann (powers (of (some BV))) :=
begin 
  intros x Hx,
  sorry,
end

lemma structure_presheaf.res.localization
: is_localization_data 
    (powers (of (some BV))) 
    (structure_presheaf_on_basis.res BU BV H) :=
{ inverts := structure_presheaf.res.inverts_data BU BV H,
  has_denom := structure_presheaf.res.has_denom_data BU BV H, 
  ker_le := structure_presheaf.res.ker_le BU BV H }

end structure_presheaf