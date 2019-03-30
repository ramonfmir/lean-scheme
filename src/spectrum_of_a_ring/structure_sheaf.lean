import preliminaries.localisation
import sheaves.sheaf_on_standard_basis
import spectrum_of_a_ring.induced_homeomorphism
import spectrum_of_a_ring.structure_presheaf

universe u

local attribute [instance] classical.prop_decidable

variables {R : Type u} [comm_ring R]

open topological_space
open localization_alt
open sheaf_on_standard_basis

section structure_sheaf 

def localization.of.away (f : R) 
: R → localization R (powers f) := localization.of

instance localization.of.away.is_ring_hom (f : R) 
: is_ring_hom (localization.of.away f) := localization.of.is_ring_hom  

lemma is_localisation.away (f : R) 
: is_localization (powers f) (localization.of.away f) :=
begin
  refine ⟨_, _, _⟩,
  { intros s,
    use ⟦⟨1, s⟩⟧,
    apply quotient.sound,
    use [1, ⟨0, rfl⟩],
    simp, },
  { intros x,
    apply quotient.induction_on x,
    rintros ⟨r, s⟩,
    use [⟨s, r⟩],
    apply quotient.sound,
    use [1, ⟨0, rfl⟩],
    simp, },
  { sorry, }
end

theorem structure_presheaf_on_basis_is_sheaf_on_basis 
: is_sheaf_on_standard_basis 
    (D_fs_standard_basis R)
    (structure_presheaf_on_basis R).to_presheaf_on_basis :=
begin
  intros U BU OC,
  rcases BU with ⟨f, Hf⟩,

  -- Lemma: D(f) is open.
  have HfO : is_open (Spec.D'(f)),
    use {f},
    simp [Spec.D', Spec.V', Spec.V],
  let U' : opens (Spec R) := ⟨Spec.D'(f), HfO⟩,
  have Hf' : U = U', 
    apply opens.ext,
    rw Hf,

  rw Hf' at OC,

  let Rf := localization.away f,
  let g : OC.γ → R := λ i, classical.some (OC.BUis i),
  let Hg : ∀ i, (OC.Uis i).val = Spec.D'(g i) := λ i, classical.some_spec (OC.BUis i),
  let g' : OC.γ → Rf := λ i, localization.of (g i),
  
  -- Lemma: If ⋃ D(gᵢ) = D(f) then ⋃ D(gᵢ') = Spec Rf.
  have Hcov : (⋃ (λ i, Spec.D'(g' i))) = set.univ,
  { let φ : Spec Rf → Spec R := Zariski.induced localization.of,
    apply set.eq_univ_of_univ_subset,
    rintros P HP,
    have H : φ P ∈ U',
      show φ P ∈ Spec.D'(f),
      rw ←phi_image_Df (is_localisation.away f),
      use P,
      split,
      { trivial, },
      { refl, },
    rw ←OC.Hcov at H,
    rcases H with ⟨UiS, ⟨⟨UiO, ⟨⟨i, Hi⟩, HUiO⟩⟩, HPUiS⟩⟩,
    use [φ ⁻¹' UiO.val, i],
    { simp,
      rw [←Hi, Hg, Zariski.induced.preimage_D _ _], },
    { rw HUiO,
      exact HPUiS, },
  },

  constructor,
  { intros s t Hst,
    dunfold structure_presheaf_on_basis at s,
    dunfold structure_presheaf_on_basis at t,
    dsimp at s,
    dsimp at t,
    sorry, },
  { sorry, }
end

end structure_sheaf 
