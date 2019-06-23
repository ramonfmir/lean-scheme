/-
  First argument of the ring lemma. 
  
  We show that the map from R[1/f] to R[1/fᵢ] inverts fᵢ/1. 
-/

import ring_theory.localization
import to_mathlib.localization.localization_alt
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_res

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

section structure_presheaf

open topological_space
open classical
open localization
open localization_alt

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
  exact structure_presheaf.inverts_data BV ⟨(some BV)^n, ⟨n, rfl⟩⟩,
end

lemma structure_presheaf.res.has_denom_data
: has_denom_data 
    (powers (of (some BV))) 
    (structure_presheaf_on_basis.res BU BV H) :=
begin
  intros x,
  rcases (structure_presheaf.has_denom_data BV x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
  rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
  dsimp only [subtype.coe_mk] at Hpq,
  let p' : localization R (S U) := of p,
  let q' : localization R (S U) := (of ((some BV)^n)),
  have Hq' : q' ∈ powers ((of : R → localization R (S U)) (some BV)),
    dsimp [q'],
    rw is_semiring_hom.map_pow (of : R → localization R (S U)),
    exact ⟨n, rfl⟩,
  use ⟨⟨q', Hq'⟩, p'⟩,
  dsimp only [subtype.coe_mk, q', p', structure_presheaf_on_basis.res],
  iterate 2 { rw is_localization_initial_comp, },
  rw Hn,
  exact Hpq,
end

lemma structure_presheaf.res.ker_le
: ker (structure_presheaf_on_basis.res BU BV H) ≤ submonoid_ann (powers (of (some BV))) :=
begin 
  intros x Hx,
  change structure_presheaf_on_basis.res BU BV H x = 0 at Hx,
  rcases (structure_presheaf.has_denom_data BU x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
  rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
  dsimp only [subtype.coe_mk] at Hpq,
  have Hofp : structure_presheaf_on_basis.res BU BV H (of p) = 0,
    rw [←Hpq, is_ring_hom.map_mul (structure_presheaf_on_basis.res BU BV H), Hx, mul_zero],
  dsimp only [structure_presheaf_on_basis.res] at Hofp,
  rw is_localization_initial_comp at Hofp,
  have Hpker : p ∈ ker (of : R → localization R (S V)) := Hofp,
  have Hpann := (structure_presheaf.ker_le BV) Hpker,
  rcases Hpann with ⟨⟨⟨u, ⟨v, ⟨m, Hm⟩⟩⟩, Huv⟩, Hp⟩,
  dsimp only [subtype.coe_mk] at Huv,
  dsimp only [subtype.coe_mk] at Hp,
  rw [Hp, ←Hm] at Huv,
  rcases (indefinite_description _ (pow_eq.of_basis_subset BU BV H)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  rw mul_comm at Hea,
  dsimp only [submonoid_ann, set.range, ann_aux],
  let g' : localization R (S U) := (of (some BV))^(e * n + m),
  let Hg' : g' ∈ powers ((of : R → localization R (S U)) (some BV)),
    dsimp [g'],
    exact ⟨(e * n + m), rfl⟩,
  have Hxann : x * g' = 0,
    dsimp [g'],
    rw [←is_semiring_hom.map_pow (of : R → localization R (S U)), pow_add],
    rw [is_ring_hom.map_mul (of : R → localization R (S U)), pow_mul, Hea, mul_pow],
    rw [is_ring_hom.map_mul (of : R → localization R (S U))],
    rw [←mul_assoc, ←mul_assoc, Hn, mul_comm x, Hpq, mul_comm (of p), mul_assoc],
    rw [←is_ring_hom.map_mul (of : R → localization R (S U)), Huv],
    rw [is_ring_hom.map_zero (of : R → localization R (S U)), mul_zero],
  use ⟨⟨x, ⟨g', Hg'⟩⟩, Hxann⟩,
end

lemma structure_presheaf.res.localization
: is_localization_data 
    (powers (of (some BV))) 
    (structure_presheaf_on_basis.res BU BV H) :=
{ inverts := structure_presheaf.res.inverts_data BU BV H,
  has_denom := structure_presheaf.res.has_denom_data BU BV H, 
  ker_le := structure_presheaf.res.ker_le BU BV H }

end structure_presheaf
