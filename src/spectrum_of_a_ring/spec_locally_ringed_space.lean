import ring_theory.localization
import preliminaries.localisation

import spectrum_of_a_ring.properties

import sheaves.presheaf_of_rings_on_basis
import sheaves.sheaf_on_basis
import sheaves.locally_ringed_space
import spectrum_of_a_ring.spectrum
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.standard_basis

universe u

local attribute [instance] classical.prop_decidable

variables {R : Type u} [comm_ring R] {Hnz : (0 : R) ≠ 1}

-- Assume :
-- - φ : R → Rg
-- - D(g) ⊆ D(f)
-- To show: inverts (powers f) (φ g)

open localization_alt

def φ (f : R) : R → localization.away f :=  λ x, ⟦⟨x, 1⟩⟧

instance φ_ring_hom (g : R) : is_ring_hom (φ g) := 
{ map_one := rfl, 
  map_add := 
    begin
      intros x y,
      apply quotient.sound,
      simp,
    end,
  map_mul :=
    begin
      intros x y,
      apply quotient.sound,
      simp,
    end }

noncomputable lemma φ_is_localisation_data (g : R) : is_localization_data (powers g) (φ g) :=
{ inverts := 
    begin
      intros gn,
      use ⟦⟨1, gn⟩⟧,
      apply quotient.sound,
      use [1, ⟨0, rfl⟩],
      simp,
    end,
  has_denom := 
    begin
      intros x,
      have Hx := quotient.exists_rep x,
      rcases (classical.indefinite_description _ Hx) with ⟨⟨r, gn⟩, Heq⟩,
      use ⟨gn, r⟩,
      rw ←Heq,
      apply quotient.sound,
      use [1, ⟨0, rfl⟩],
      simp,
    end, 
  ker_le := 
    begin
      intros x Hx,
      replace Hx := quotient.exact Hx,
      rcases Hx with ⟨r, ⟨Hr, Hx⟩⟩,
      simp at Hx,
      use ⟨⟨x, ⟨r, Hr⟩⟩, Hx⟩,
    end, }

include Hnz

lemma localisation_inverts (f g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) 
: inverts (powers f) (φ g) :=
begin
  rintros ⟨fn, Hfn⟩,
  unfold Spec.D' at H,
  rw set.compl_subset_compl at H,
  unfold Spec.V' at H,
  -- Proof by contradiction.
  by_contra,
  rw not_exists at a,
  -- (φ (f)) is not a unit.
  -- Hence (φ (f)) ⊆ M, M maximal.
  -- M prime.
  -- 
end

-- Use this to get a map ψ : Rf → Rg by the universal property.

def structure_presheaf_on_basis : presheaf_of_rings_on_basis (Spec R) (D_fs_basis R) := 
{ -- F(D(f)) = R[1/f]
  F := λ U BU, localization.away (classical.some BU),
  res := 
    begin
      intros U V BU BV HVU x,
      cases (classical.indefinite_description _ BU) with f HU,
      cases (classical.indefinite_description _ BV) with g HV,
      replace HVU : V.val ⊆ U.val := HVU,
      rw HU at HVU,
      rw HV at HVU,
      unfold Spec.D' at HVU,
      rw set.compl_subset_compl at HVU,
      unfold Spec.V' at HVU,
      rcases (classical.indefinite_description _ (quotient.exists_rep x)) with ⟨⟨r, fn⟩, Heq⟩,
      sorry,
    end,
  Hid := sorry,
  Hcomp := sorry,
  Fring := sorry,
  res_is_ring_hom := sorry, }

-- def structure_presheaf : presheaf_of_rings (Spec R) :=
-- presheaf_on_basis_to_presheaf structure_presheaf_on_basis

def SpecR : locally_ringed_space (Spec R) :=
{ O := sorry, 
  Hstalks := sorry }
