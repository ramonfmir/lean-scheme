import preliminaries.localisation
import sheaves.sheaf_on_standard_basis
import spectrum_of_a_ring.induced_homeomorphism
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_sheaf_condition

universe u

local attribute [instance] classical.prop_decidable

variables {R : Type u} [comm_ring R]

open topological_space
open localization_alt
open sheaf_on_standard_basis

section structure_sheaf 

theorem structure_presheaf_on_basis_is_sheaf_on_basis 
: is_sheaf_on_standard_basis 
    (D_fs_standard_basis R)
    (structure_presheaf_on_basis R).to_presheaf_on_basis :=
begin
  intros U BU OC,
  have BU' := BU,
  rcases BU' with ⟨f, Hf⟩,

  -- TODO : We prove it for finite covers then extend it.
  have Hγ : fintype OC.γ := sorry,

  -- Lemma: D(f) is open.

  let Rf := localization R (S U),
  have HRf : is_localization (powers f) (localization.of : R → Rf) := sorry, -- Easy

  let g : OC.γ → R := λ i, classical.some (OC.BUis i),
  let Hg : ∀ i, OC.Uis i = Spec.DO R (g i) := λ i, classical.some_spec (OC.BUis i),
  let g' : OC.γ → Rf := λ i, localization.of (g i),
  
  -- Lemma: If ⋃ D(gᵢ) = D(f) then ⋃ D(gᵢ') = Spec Rf.
  have Hcov : (⋃ (λ i, Spec.D'(g' i))) = set.univ,
  { let φ : Spec Rf → Spec R := Zariski.induced localization.of,
    apply set.eq_univ_of_univ_subset,
    rintros P HP,
    have H : φ P ∈ U,
      suffices : φ P ∈ Spec.DO R (f),
        rw Hf,
        exact this,
      show φ P ∈ Spec.D'(f),
      rw ←phi_image_Df HRf,
      use P,
      split,
      { trivial, },
      { refl, },
    rw ←OC.Hcov at H,
    rcases H with ⟨UiS, ⟨⟨UiO, ⟨⟨i, Hi⟩, HUiO⟩⟩, HPUiS⟩⟩,
    use [φ ⁻¹' UiO.val, i],
    { simp,
      rw [←Hi, Hg],
      dsimp only [Spec.DO],
      rw [←Zariski.induced.preimage_D localization.of _], },
    { rw HUiO,
      exact HPUiS, }, },

  -- We want: 1 ∈ <fi>
  let F : set Rf := set.range g',
  replace Hcov : ⋃₀ (Spec.D' '' F) = set.univ := sorry, -- Easy
  rw (Spec.D'.union F) at Hcov,
  replace Hcov : Spec.V F = ∅ := sorry, -- Easy
  rw Spec.V.set_eq_span at Hcov,
  rw Spec.V.empty_iff_ideal_top at Hcov,
  rw ideal.eq_top_iff_one at Hcov,
  
  -- Now we can apply covering lemmas.

  let αi := λ i, structure_presheaf_on_basis.res R BU (OC.BUis i) (subset_covering i),
  let Rfis := λ i, localization R (S (OC.Uis i)),

  have := λ i, structure_presheaf.localization (OC.BUis i),

  have : Π i, is_localization_data (powers (g' i)) (αi i) := sorry,

  have Hsc₁ := 
    @standard_covering₁ Rf _ _ Hγ g' Rfis _ αi _ this Hcov,
    -- _ _ Hγ OC.Uis Rfis _ αi _ 
      --(λ i, structure_presheaf.localization (OC.BUis i)),

  constructor,
  { intros s t Hst,
    dunfold structure_presheaf_on_basis at s,
    dunfold structure_presheaf_on_basis at t,
    dsimp [coe_fn, has_coe_to_fun.coe] at s,
    dsimp [coe_fn, has_coe_to_fun.coe] at t,
    --dunfold structure_presheaf_on_basis at Hst,
    --have := localization.structure_presheaf_on_basis.res Rf,
    --erw localization.structure_presheaf_on_basis.res Rf at Hst,
    --dsimp at Hst,

    -- TODO unfold inside Hst....

    let α' := @α Rf _ _ Hγ Rfis _ αi _,

    suffices Hsuff : α' s = α' t,
      exact (Hsc₁ Hsuff),

    apply funext,
    intros i,
    dsimp [α'],
    simp [α, αi],

    replace Hst := Hst i,
    rw ←structure_presheaf_on_basis.res_eq R BU,
    exact Hst,

    -- have : (λ i, (k i) s) = (λ i, (k i) t_1),
    --   apply funext,
    --   intros i,
    --   replace Hst := Hst i,
    --   have : 
    --       ((structure_presheaf_on_basis R).to_presheaf_on_basis).res BU 
    --         (OC.BUis i) 
    --         (subset_covering i)
    --         s
    --     = ((structure_presheaf_on_basis R).to_presheaf_on_basis).res BU 
    --         (OC.BUis i) 
    --         (subset_covering i)
    --         t_1 := Hst,
        
    --   rw localization.structure_presheaf_on_basis.res' at Hst,
      --exact (Hst i),

    },
  { intros s,
    
    intros Hs,

   }
end

end structure_sheaf 
