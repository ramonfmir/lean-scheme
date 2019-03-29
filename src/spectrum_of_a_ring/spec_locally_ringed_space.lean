import ring_theory.localization
import preliminaries.localisation

import spectrum_of_a_ring.properties

import sheaves.presheaf_of_rings_on_basis
import sheaves.sheaf_of_rings_on_basis
import sheaves.locally_ringed_space
import spectrum_of_a_ring.spectrum
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.standard_basis

universe u

open topological_space

local attribute [instance] classical.prop_decidable

variables {R : Type u} [comm_ring R]

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

-- D(g) ⊆ D(f) → f ∈ R[1/g]*

lemma localisation_inverts (f g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) 
: inverts (powers f) (φ g) :=
begin
  rcases (φ_is_localisation_data g) with ⟨Hinv, Hden, Hker⟩,
  rintros ⟨fn, Hfn⟩,
  suffices Hsuff : ∃ si, φ g f * si = 1,
    rcases Hsuff with ⟨si, Hsi⟩,
    show ∃ si, φ g fn * si = 1,
    rcases Hfn with ⟨n, Hfn⟩,
    rw ←Hfn,
    clear Hfn,
    induction n with n Hn,
    { simp,
      rw (is_ring_hom.map_one (φ g)),
      use 1,
      ring, },
    { rw pow_succ,
      rw (is_ring_hom.map_mul (φ g)),
      rcases Hn with ⟨sin, Hn⟩,
      existsi (si * sin),
      rw ←mul_assoc,
      rw mul_assoc _ _ si,
      rw mul_comm _ si,
      rw ←mul_assoc,
      rw Hsi,
      rw one_mul,
      exact Hn, },
  unfold Spec.D' at H,
  rw set.compl_subset_compl at H,
  unfold Spec.V' at H,
  by_contra Hne,
  rw not_exists at Hne,
  have Hnu : ¬is_unit (φ g f),
    intros HC,
    simp [is_unit] at HC,
    rcases HC with ⟨u, HC⟩,
    apply (Hne u.inv),
    rw HC,
    exact u.3,
  let F : ideal (localization.away g) := ideal.span {(φ g f)},
  have HFnT : F ≠ ⊤,
    intros HC,
    rw ideal.span_singleton_eq_top at HC,
    exact (Hnu HC),
  rcases (ideal.exists_le_maximal F HFnT) with ⟨S, ⟨HMS, HFS⟩⟩,
  have HfF : φ g f ∈ F,
    suffices Hsuff : φ g f ∈ {φ g f},
      exact ideal.subset_span Hsuff,
    exact set.mem_singleton _,
  have HfM : φ g f ∈ S := HFS HfF,
  have PS := ideal.is_maximal.is_prime HMS,
  have PS' : ideal.is_prime (ideal.comap (φ g) S)
    := @ideal.is_prime.comap _ _ _ _ (φ g) _ _ PS,
  let S' : Spec R := ⟨ideal.comap (φ g) S, PS'⟩,
  have HfS' : f ∈ S'.val,
    rw ideal.mem_comap,
    exact HfM,
  replace HfS' : S' ∈ {P : Spec R | f ∈ P.val} := HfS',
  have HgS' : g ∈ ideal.comap (φ g) S := H HfS',
  rw ideal.mem_comap at HgS',
  rcases (Hinv ⟨g, ⟨1, by simp⟩⟩) with ⟨w, Hw⟩,
  have HC : φ g g * w ∈ S := ideal.mul_mem_right S HgS',
  erw Hw at HC,
  exact (@ideal.is_prime.one_not_mem _ _ S PS) HC,
end

-- Use this to get a map ψ : Rf → Rg by the universal property.

def S (U : opens (Spec R)) : set R := { r : R | U.1 ⊆ Spec.D'(r) }

instance S.is_submonoid (U : opens (Spec R)) : is_submonoid (S U) :=
{ one_mem := 
    begin
      intros x Hx,
      exact @ideal.is_prime.one_not_mem _ _ x.1 x.2,
    end, 
  mul_mem := 
    begin
      intros f g Hf Hg,
      show U.1 ⊆ Spec.D'(f*g),
      rw Spec.D'.product_eq_inter,
      exact set.subset_inter Hf Hg,
    end, }

lemma S.rev_mono {U V : opens (Spec R)} (HVU : V ⊆ U) : S U ⊆ S V :=
begin
  intros x Hx,
  apply set.subset.trans HVU Hx,
end

def structure_presheaf_on_basis : presheaf_of_rings_on_basis (Spec R) (D_fs_basis R) := 
{ -- F(D(f)) = R[1/S] ≅ R[1/f]
  F := λ U BU, localization R (S U),
  res := 
    begin
      intros U V BU BV HVU,
      have H := S.rev_mono HVU,
      apply quotient.lift (λ (x : R × (S U)), ⟦(x.1, (⟨x.2.1, H x.2.2⟩ : (S V)))⟧),
      { rintros ⟨a1, b1, Hb1⟩ ⟨a2, b2, Hb2⟩ ⟨t, Ht, Habt⟩,
        simp,
        simp at Habt,
        use [t, H Ht],
        exact Habt, },
    end,
  Hid := 
    begin
      intros U BU,
      simp,
      apply funext,
      intros x,
      simp,
      apply quotient.induction_on x,
      intros a,
      simp,
    end,
  Hcomp := 
    begin
      intros U V W BU BV BW HWV HVU,
      apply funext,
      intros x,
      simp,
      apply quotient.induction_on x,
      intros a,
      simp,
    end,
  Fring := 
    begin
      intros U BU,
      simp,
      apply_instance,
    end,
  res_is_ring_hom := 
    begin
      intros U V BU BV HVU,
      simp,
      exact 
      { map_one := 
          begin
            refl,
          end,
        map_add := 
          begin
            intros x y,
            apply quotient.induction_on₂ x y,
            rintros ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, 
            refl,
          end,
        map_mul := 
          begin
            intros x y,
            apply quotient.induction_on₂ x y,
            rintros ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, 
            refl,
          end, },
    end, }

def structure_presheaf : presheaf_of_rings (Spec R) :=
  presheaf_on_basis_to_presheaf structure_presheaf_on_basis

def SpecR : locally_ringed_space (Spec R) :=
{ O := sorry, 
  Hstalks := sorry }
