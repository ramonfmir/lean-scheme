/-
  Relate restriction maps of the structure presheaf to the universal property
  of localization.
-/

import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

open topological_space
open classical
open localization
open localization_alt

section res

-- We are given U and V in {D(f)} and V ⊆ U and we generalize the results that
-- we already proved in properties. We deduce that there's a map from
-- R[1/S(V)] to R[1/S(U)].

variables {R : Type u} [comm_ring R]
variables {U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)

include H

-- V ⊆ U → D(g) ⊆ D(f). 

lemma Dfs_subset.of_basis_subset 
: Spec.DO R (some BV) ⊆ Spec.DO R (some BU) :=
begin
  rw [←some_spec BU, ←some_spec BV],
  exact H,
end

-- V ⊆ U → f ∈ R[1/g]*.

def inverts_data.of_basis_subset.aux
: inverts_data 
    (powers (some BU)) 
    (of : R → localization R (powers (some BV))) :=
begin
  intros s,
  have Hs := inverts.of_Dfs_subset (Dfs_subset.of_basis_subset BU BV H) s,
  rcases (indefinite_description _ Hs) with ⟨si, Hsi⟩,
  exact ⟨si, Hsi⟩,
end

-- V ⊆ U → ∃ a e, g^e = a * f.

def pow_eq.of_basis_subset
: ∃ (a : R) (e : ℕ), (some BV)^e = a * (some BU) :=
pow_eq.of_Dfs_subset (Dfs_subset.of_basis_subset BU BV H)

include BU BV

-- V ⊆ U → S(U) ⊆ R[1/S(V)]*.

def inverts_data.of_basis_subset
: inverts_data 
    (S U) 
    (of : R → localization R (S V)) :=
begin
  intros s,
  rcases s with ⟨s, Hs⟩,
  change U ⊆ Spec.DO R (s) at Hs,
  have HsV : s ∈ S V := set.subset.trans H Hs,
  use ⟦⟨1, ⟨s, HsV⟩⟩⟧,
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp,
end

-- The induced map is the restriction map in the structure presheaf.

def structure_presheaf_on_basis.res
: localization R (S U) 
→ localization R (S V) :=
is_localization_initial 
  (S U)
  (of : R → localization R (S U))
  (of.is_localization_data (S U))
  (of : R → localization R (S V))
  (inverts_data.of_basis_subset BU BV H)

-- Useful.

instance structure_presheaf_on_basis.res.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res BU BV H) :=
by simp [structure_presheaf_on_basis.res]; by apply_instance

end res

section res_eq

variables {R : Type u} [comm_ring R]

lemma structure_presheaf_on_basis.res_eq
: (structure_presheaf_on_basis R).res = @structure_presheaf_on_basis.res R _ :=
begin
  apply funext, intro U,
  apply funext, intro V,
  apply funext, intro BU,
  apply funext, intro BV,
  apply funext, intro HVU,
  apply funext, intro x,
  -- x ∈ R[1/S(U)].
  apply quotient.induction_on x,
  rintros ⟨a, b⟩,
  -- Destruct.
  simp [structure_presheaf_on_basis.res, is_localization_initial],
  rcases ((of.is_localization_data (S U)).has_denom ⟦(a, b)⟧) with ⟨⟨q, p⟩, Hpq⟩,
  rcases inverts_data.of_basis_subset BU BV HVU q with ⟨w, Hw⟩,
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
  replace Ht := (S.rev_mono HVU) Ht,
  use [s * t, is_submonoid.mul_mem Hs Ht],
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

lemma structure_presheaf_on_basis.res_comp
{U V W : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (BW : W ∈ D_fs R)
(HVU : V ⊆ U) (HWV : W ⊆ V)
: structure_presheaf_on_basis.res BU BW (set.subset.trans HWV HVU)
= structure_presheaf_on_basis.res BV BW HWV ∘ structure_presheaf_on_basis.res BU BV HVU :=
begin
  rw ←structure_presheaf_on_basis.res_eq,
  rw (structure_presheaf_on_basis R).Hcomp,
end

lemma structure_presheaf_on_basis.res_comp_of 
{U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)
: (of : R → localization R (S (V)))
= structure_presheaf_on_basis.res BU BV H ∘ (of : R → localization R (S (U))) :=
begin
  apply funext, intro x,
  simp [structure_presheaf_on_basis.res],
  rw is_localization_initial_comp,
end

lemma structure_presheaf_on_basis.res_comp_of' 
{U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)
: ∀ x, 
(of : R → localization R (S (V))) x
= structure_presheaf_on_basis.res BU BV H ((of : R → localization R (S (U))) x) :=
begin
  intros x,
  rw structure_presheaf_on_basis.res_comp_of BU BV H,
end

end res_eq
