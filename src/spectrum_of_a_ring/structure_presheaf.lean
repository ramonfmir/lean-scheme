import ring_theory.localization
import preliminaries.localisation
import preliminaries.localisation_tests.localization_of

import spectrum_of_a_ring.properties

import sheaves.presheaf_of_rings_on_basis
import sheaves.sheaf_of_rings_on_standard_basis
import sheaves.locally_ringed_space
import spectrum_of_a_ring.spectrum
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.standard_basis

universe u

open topological_space

local attribute [instance] classical.prop_decidable

noncomputable theory

variables {R : Type u} [comm_ring R]

open classical
open localization
open localization_alt

section maps

-- We are given U and V in {D(f)} and V ⊆ U.

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

def inverts_data.of_basis_subset
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

-- Map from R[1/f] to R[1/g].

def localization.map.of_Dfs_subset
: localization R (powers (some BU)) 
→ localization R (powers (some BV)) :=
is_localization_initial 
  (powers (classical.some BU))
  (of : R → localization R (powers (some BU)))
  (of.is_localization_data (powers (some BU)))
  (of : R → localization R (powers (some BV)))
  (inverts_data.of_basis_subset BU BV H)

end maps

section localization_S

-- Define S(U) so that R[1/f] ≃ R[1/S(D(f))].

def S (U : opens (Spec R)) : set R := { r : R | U ⊆ Spec.DO R (r) }

instance S.is_submonoid (U : opens (Spec R)) : is_submonoid (S U) :=
{ one_mem := λ ⟨P, PI⟩ HP, ((ideal.ne_top_iff_one P).1 PI.1),
  mul_mem := λ f g Hf Hg,
    begin
      show U.1 ⊆ Spec.D'(f*g),
      exact (Spec.D'.product_eq_inter f g).symm ▸ set.subset_inter Hf Hg,
    end, }

lemma S.rev_mono {U V : opens (Spec R)} (HVU : V ⊆ U) : S U ⊆ S V :=
λ x Hx, set.subset.trans HVU Hx

lemma S.f_mem (f : R) : f ∈ S (Spec.DO R (f)) := set.subset.refl _

-- Proof of the localization property.

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

end localization_S

section structure_presheaf

variable (R)

-- Structure presheaf on Spec(R) defined on the basis.

def structure_presheaf_on_basis : presheaf_of_rings_on_basis (Spec R) (D_fs_basis R) := 
{ F := λ U BU, localization R (S U),
  res := λ U V BU BV HVU,
    begin
      have H := S.rev_mono HVU,
      apply quotient.lift (λ (x : R × (S U)), ⟦(x.1, (⟨x.2.1, H x.2.2⟩ : (S V)))⟧),
      { rintros ⟨a1, b1, Hb1⟩ ⟨a2, b2, Hb2⟩ ⟨t, Ht, Habt⟩,
        simp,
        use [t, H Ht, Habt], },
    end,
  Hid := λ U BU, funext $ λ x, quotient.induction_on x $ λ a, by simp,
  Hcomp := λ U V W BU BV BW HWV HVU, funext $ λ x, quotient.induction_on x $ λ a, by simp,
  Fring := λ U BU, by apply_instance,
  res_is_ring_hom := λ U V BU BV HVU,
      { map_one := rfl,
        map_add := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl,
        map_mul := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl, }, }

variables {U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)

-- Map from R[1/g] to R[1/S(D(g))].

def structure_presheaf.map_to 
: localization R (powers (some BV))
→ localization R (S V) :=
is_localization_initial 
  (powers (some BV))
  (of : R → localization R (powers (some BV)))
  (of.is_localization_data (powers (some BV)))
  (of : R → (structure_presheaf_on_basis R).F BV)
  (structure_presheaf.inverts_data BV)

include BV H

-- V ⊆ U → f ∈ R[1/S(D(g))]*.

-- TODO: This is very ugly...

def structure_presheaf.inverts_data.of_basis_subset
: inverts_data 
    (powers (some BU)) 
    (of : R → localization R (S V)) :=
begin
  intros s,
  have sinv := inverts_data.of_basis_subset BU BV H s,
  rcases sinv with ⟨sinv, Hsinv⟩,
  use [structure_presheaf.map_to R BV sinv],
  rw ←is_localization_initial_comp 
    (powers (some BV))
    (of : R → localization R (powers (some BV)))
    (of.is_localization_data (powers (some BV)))
    (of : R → (structure_presheaf_on_basis R).F BV)
    (structure_presheaf.inverts_data BV),
  unfold structure_presheaf.map_to,
  rw ←is_ring_hom.map_mul 
    (is_localization_initial 
      (powers (some BV))
      (of : R → localization R (powers (some BV)))
      (of.is_localization_data (powers (some BV)))
      (of : R → (structure_presheaf_on_basis R).F BV)
      (structure_presheaf.inverts_data BV)),
  rw Hsinv,
  rw is_ring_hom.map_one
    (is_localization_initial 
      (powers (some BV))
      (of : R → localization R (powers (some BV)))
      (of.is_localization_data (powers (some BV)))
      (of : R → (structure_presheaf_on_basis R).F BV)
      (structure_presheaf.inverts_data BV)),
end

def structure_presheaf_on_basis.res
: (structure_presheaf_on_basis R).F BU 
→ (structure_presheaf_on_basis R).F BV :=
is_localization_initial 
  (powers (some BU))
  (of : R → (structure_presheaf_on_basis R).F BU)
  (structure_presheaf.localization BU)
  (of : R → (structure_presheaf_on_basis R).F BV)
  (structure_presheaf.inverts_data.of_basis_subset R BU BV H)

-- The restriction maps are actually the unique ring homomorphism coming from
-- the universal property.

lemma structure_presheaf_on_basis.res_eq
: (structure_presheaf_on_basis R).res BU BV H = structure_presheaf_on_basis.res R BU BV H :=
begin
  apply funext,
  intros x,
  apply quotient.induction_on x,
  rintros ⟨a, b⟩,
  simp [structure_presheaf_on_basis.res, is_localization_initial],
  rcases ((structure_presheaf.localization BU).has_denom ⟦(a, b)⟧) with ⟨⟨q, p⟩, Hpq⟩,
  dsimp at *,
  rcases structure_presheaf.inverts_data.of_basis_subset R BU BV H q with ⟨w, Hw⟩,
  revert Hw,
  apply quotient.induction_on w,
  rintros ⟨c, d⟩,
  intros Hw,
  apply quotient.sound,
  dsimp,
  erw quotient.eq at Hpq,
  rcases Hpq with ⟨t, ⟨Ht, Hpq⟩⟩,
  simp [-sub_eq_add_neg] at Hpq,
  erw quotient.eq at Hw,
  rcases Hw with ⟨s, ⟨Hs, Hw⟩⟩,
  simp [-sub_eq_add_neg] at Hw,

  rcases (pow_eq.of_basis_subset BU BV H) with ⟨a₁, ⟨e₁, Ha₁⟩⟩,

  have HDfDt : Spec.D'(some BU) ⊆ Spec.D'(t),
    change U ⊆ Spec.DO R (t) at Ht,
    rw some_spec BU at Ht,
    exact Ht,

  rcases (pow_eq.of_Dfs_subset HDfDt) with ⟨a₂, ⟨e₂, Ha₂⟩⟩,

  have Heq : t * a₂ * a₁ ^ e₂ = (some BV) ^ (e₁ * e₂),
    rw mul_comm at Ha₂,
    rw ←Ha₂,
    rw ←mul_pow,
    rw mul_comm at Ha₁,
    rw ←Ha₁,
    rw ←pow_mul,

  have HgS := S.f_mem (some BV),
  rw ←some_spec BV at HgS,

  have HtS : t * a₂ * a₁ ^ e₂ ∈ S V := Heq.symm ▸ is_submonoid.pow_mem HgS,

  use [s * (t * a₂ * a₁ ^ e₂), is_submonoid.mul_mem Hs HtS],
  simp [-sub_eq_add_neg],
  rw sub_mul,
  rw sub_mul at Hpq,
  rw sub_mul at Hw,
  rw sub_eq_zero,
  rw sub_eq_zero at Hpq,
  rw sub_eq_zero at Hw,
  repeat { rw ←mul_assoc },
  suffices Hsuff : ↑b * p * c * s * t = ↑d * a * s * t,
    erw Hsuff,
  
  iterate 2 { rw [mul_assoc _ _ t, mul_comm _ t, ←mul_assoc] },
  rw Hpq,

  symmetry,

  rw [mul_assoc _ _ s, mul_comm _ s, ←mul_assoc],
  rw Hw,

  ring,
end

end structure_presheaf
