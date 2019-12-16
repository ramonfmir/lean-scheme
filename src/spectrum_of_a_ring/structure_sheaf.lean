/-
  The structure presheaf is a sheaf of rings.

  https://stacks.math.columbia.edu/tag/01HR
-/

import topology.basic
import to_mathlib.localization.localization_alt
import sheaves.sheaf_on_standard_basis
import spectrum_of_a_ring.induced_homeomorphism
import spectrum_of_a_ring.quasi_compact
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_sheaf_condition
import spectrum_of_a_ring.structure_sheaf_locality
import spectrum_of_a_ring.structure_sheaf_gluing

universes u v

local attribute [instance] classical.prop_decidable

variables {R : Type u} [comm_ring R]

open topological_space
open localization_alt
open localization
open classical

section structure_sheaf 

theorem structure_presheaf_on_basis_is_sheaf_on_standard_basis_cofinal_system
: sheaf_on_standard_basis.is_sheaf_on_standard_basis_cofinal_system
    (D_fs_standard_basis R)
    (structure_presheaf_on_basis R).to_presheaf_on_basis :=
begin
  intros U BU OC Hγ,
  let f := some BU,
  let Rf := localization R (S U),
  have HRf : is_localization_data (powers f) (localization.of : R → Rf) 
    := structure_presheaf.localization BU,
  let fi : OC.γ → R := λ i, classical.some (OC.BUis i),
  let Hfi : ∀ i, OC.Uis i = Spec.DO R (fi i) := λ i, classical.some_spec (OC.BUis i),
  let fi' : OC.γ → Rf := λ i, localization.of (fi i),
  let F : set Rf := set.range fi',
  -- Lemma: ⋃ D(gᵢ') = Spec Rf.
  have Hcov : ⋃₀ (Spec.D' '' F) = set.univ,
  { let φ : Spec Rf → Spec R := Zariski.induced localization.of,
    dsimp [F],
    apply set.eq_univ_of_univ_subset,
    rintros P HP,
    have H : φ P ∈ U,
      suffices : φ P ∈ Spec.DO R (f),
        rw some_spec BU,
        exact this,
      show φ P ∈ Spec.D'(f),
      rw ←phi_image_Df HRf,
      use P,
      split,
      { trivial, },
      { refl, },
    rw ←OC.Hcov at H,
    rcases H with ⟨UiS, ⟨⟨UiO, ⟨⟨i, Hi⟩, HUiO⟩⟩, HPUiS⟩⟩,
    use [φ ⁻¹' UiS],
    have Hin : φ ⁻¹' UiS ∈ Spec.D' '' set.range fi',
      rw [←HUiO, ←Hi, Hfi],
      dsimp only [Spec.DO],
      use [fi' i],
      split,
      { use [i], },
      { rw [←Zariski.induced.preimage_D localization.of _], },
    use [Hin],
    exact HPUiS, },
  -- We deduce: 1 ∈ <fi>
  have Hone : (1 : Rf) ∈ ideal.span F,
    erw [←ideal.eq_top_iff_one, ←Spec.V.empty_iff_ideal_top, ←Spec.V.set_eq_span],
    rw [Spec.D'.union F, ←set.compl_compl set.univ, set.compl_univ] at Hcov,
    apply set.ext,
    intros x,
    rw set.ext_iff at Hcov,
    replace Hcov := Hcov x,
    iterate 2 { rw set.mem_compl_iff at Hcov, },
    rw not_iff_not at Hcov,
    exact Hcov,
  -- α is injective.
  let αi := λ i, structure_presheaf_on_basis.res BU (OC.BUis i) (subset_covering i),
  let Rfi := λ i, localization R (S (OC.Uis i)),
  let α' := @α Rf _ _ Hγ Rfi _ αi _,
  have Hlocα : Π i, is_localization_data (powers (fi' i)) (αi i) 
    := λ i, structure_presheaf.res.localization BU (OC.BUis i) (subset_covering i),
  have Hsc₁ := @standard_covering₁ Rf _ _ Hγ fi' Rfi _ αi _ Hlocα Hone,
  -- ker β = im α.
  let Rfij := λ i j, localization R (S ((OC.Uis i) ∩ (OC.Uis j))),
  let βij 
    := λ i j, structure_presheaf_on_basis.res_to_inter BU (OC.BUis i) (OC.BUis j) (subset_covering i),
  have Hlocβ
    := λ i j, structure_presheaf.res_to_inter.localization BU (OC.BUis i) (OC.BUis j) (subset_covering i),
  let β' := @β Rf _ _ Hγ fi' Rfi _ αi _ Hlocα Rfij _ βij _ Hlocβ,
  have Hsc₂ := @standard_covering₂ Rf _ _ Hγ fi' Rfi _ αi _ Hlocα Rfij _ βij _ Hlocβ Hone,
  constructor,
  { -- Locality. 
    intros s t Hst,
    dsimp [structure_presheaf_on_basis, coe_fn, has_coe_to_fun.coe] at s,
    dsimp [structure_presheaf_on_basis, coe_fn, has_coe_to_fun.coe] at t,
    apply Hsc₁,
    dsimp [α, αi],
    apply funext,
    intros i,
    rw ←structure_presheaf_on_basis.res_eq,
    exact (Hst i), },
  { -- Gluing.
    intros s Hs,
    have Hβ : β' s = 0,
      simp [β', β, -sub_eq_add_neg, sub_eq_zero, β1, β2],
      apply funext, intro j,
      apply funext, intro k,
      have Hsjk := Hs j k,
      dsimp only [sheaf_on_standard_basis.res_to_inter_left] at Hsjk,
      dsimp only [sheaf_on_standard_basis.res_to_inter_right] at Hsjk,
      rw structure_presheaf_on_basis.res_eq at Hsjk,
      -- The restriction to the left is the unique localization map from R[1/fj] to R[1/fjfk].
      let β1 := structure_presheaf_on_basis.res_to_inter_right (OC.BUis j) (OC.BUis k),
      let Hβ1 := @inverts_powers1 Rf _ _ Hγ fi' Rfij _ βij _ Hlocβ j k,
      have Hcompβ1 : βij j k = β1 ∘ (αi k),
        dsimp only [βij, β1, αi],
        dsimp only [structure_presheaf_on_basis.res_to_inter_right],
        dsimp only [structure_presheaf_on_basis.res_to_inter],
        erw ←structure_presheaf_on_basis.res_comp,
        refl,
      have Huniqueβ1 
        := is_localization_unique.of_eq (powers (fi' k)) (αi k) (Hlocα k) β1 (s k) (βij j k) Hβ1 Hcompβ1,
      rw Huniqueβ1,
      -- The restriction to the right is the unique localization map from R[1/fk] to R[1/fjfk].
      let β2 := structure_presheaf_on_basis.res_to_inter_left (OC.BUis j) (OC.BUis k),
      let Hβ2 := @inverts_powers2 Rf _ _ Hγ fi' Rfij _ βij _ Hlocβ j k,
      have Hcompβ2 : βij j k = β2 ∘ (αi j),
        dsimp only [βij, β2, αi],
        dsimp only [structure_presheaf_on_basis.res_to_inter_left],
        dsimp only [structure_presheaf_on_basis.res_to_inter],
        erw ←structure_presheaf_on_basis.res_comp,
        refl,
      have Huniqueβ2 
        := is_localization_unique.of_eq (powers (fi' j)) (αi j) (Hlocα j) β2 (s j) (βij j k) Hβ2 Hcompβ2,
      rw Huniqueβ2,
      -- Now we have it in the desired form.
      exact Hsjk.symm,
    -- Use global section found.
    rcases ((Hsc₂ s).1 Hβ) with ⟨S, HS⟩,
    use S,
    intros i,
    replace HS := (congr_fun HS) i,
    dsimp [α, αi] at HS,
    rw structure_presheaf_on_basis.res_eq,
    exact HS, }
end

theorem structure_presheaf_on_basis_is_sheaf_on_basis 
: sheaf_on_standard_basis.is_sheaf_on_standard_basis 
    (D_fs_standard_basis R)
    (structure_presheaf_on_basis R).to_presheaf_on_basis :=
begin
  apply sheaf_on_standard_basis.cofinal_systems_coverings_standard_case,
  { apply structure_presheaf_on_basis_is_compact, },
  { apply structure_presheaf_on_basis_is_sheaf_on_standard_basis_cofinal_system, },  
end

-- Structure sheaf.

def structure_sheaf.presheaf (R : Type u) [comm_ring R] := 
presheaf_of_rings_extension
  (D_fs_standard_basis R) 
  (structure_presheaf_on_basis R)

theorem strucutre_presheaf_is_sheaf_of_rings (R : Type u) [comm_ring R] 
: is_sheaf_of_rings (structure_sheaf.presheaf R) :=
begin
  apply extension_is_sheaf_of_rings,
  intros U BU OC,
  exact structure_presheaf_on_basis_is_sheaf_on_basis BU OC,
end

def structure_sheaf (R : Type u) [comm_ring R] : sheaf_of_rings (Spec R) :=
{ F := structure_sheaf.presheaf R,
  locality := (strucutre_presheaf_is_sheaf_of_rings R).1,
  gluing := (strucutre_presheaf_is_sheaf_of_rings R).2, }

end structure_sheaf 
