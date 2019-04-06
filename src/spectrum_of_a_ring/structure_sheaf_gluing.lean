import ring_theory.localization
import preliminaries.localisation
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_res
import spectrum_of_a_ring.structure_sheaf_locality

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
variables {U V W : opens (Spec R)} 
variables (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (BW : W ∈ D_fs R) 
variables (HVU : V ⊆ U) (HWU : W ⊆ U)

-------

def BVW : V ∩ W ∈ D_fs R := (D_fs_standard_basis R).2 BV BW
def HVWU : V ∩ W ⊆ U := set.subset.trans (set.inter_subset_left V W) HVU

def structure_presheaf_on_basis.res_to_inter 
: localization R (S U) → localization R (S (V ∩ W)) :=
structure_presheaf_on_basis.res BU (BVW BV BW) (HVWU HVU)

instance structure_presheaf_on_basis.res_to_inter.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
by simp [structure_presheaf_on_basis.res_to_inter, structure_presheaf_on_basis.res]; 
by apply_instance

-------

-- (f' g')^e = a * (fg)' 

include BU HVU

lemma pow_eq.fmulg : ∃ a : R, ∃ e : ℕ, ((some BV) * (some BW))^e = a * (some (BVW BV BW)) :=
begin
  let f := some BV,
  let g := some BW,
  let fg := some (BVW BV BW),
  -- D(f*g) ⊆ D(fg).
  have HDfg : Spec.D'(f*g) ⊆ Spec.D'(fg),
    rw Spec.D'.product_eq_inter,
    show Spec.DO R f ∩ Spec.DO R g ⊆ Spec.DO R fg,
    rw [←some_spec BV, ←some_spec BW, ←some_spec (BVW BV BW)],
    exact set.subset.refl _,
  -- Hence (f*g)^e = a * fg.
  exact pow_eq.of_Dfs_subset HDfg,
end

lemma pow_eq.fg : ∃ a : R, ∃ e : ℕ, (some (BVW BV BW))^e = a * ((some BV) * (some BW)) :=
begin
  let f := some BV,
  let g := some BW,
  let fg := some (BVW BV BW),
  -- D(fg) ⊆ D(f*g).
  have HDfg : Spec.D'(fg) ⊆ Spec.D'(f*g),
    rw Spec.D'.product_eq_inter,
    show Spec.DO R fg ⊆ Spec.DO R f ∩ Spec.DO R g,
    rw [←some_spec BV, ←some_spec BW, ←some_spec (BVW BV BW)],
    exact set.subset.refl _,
  -- Hence (f*g)^e = a * fg.
  exact pow_eq.of_Dfs_subset HDfg,
end

-------

lemma structure_presheaf.res_to_inter.inverts_data
: inverts_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
begin
  rcases (indefinite_description _ (pow_eq.fg BU BV BW HVU)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  clear Ha,
  -- Using structure_presheaf.res.inverts_data
  rintros ⟨s, Hs⟩,
  rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
  let fg := some (BVW BV BW),
  have Hans : s * (of a)^n ∈ powers ((of : R → localization R (S U)) fg),
    rw [←Hn,  ←mul_pow],
    iterate 2 { rw ←is_ring_hom.map_mul (of : R → localization R (S U)), },
    rw [mul_comm, ←Hea, is_semiring_hom.map_pow (of : R → localization R (S U)), ←pow_mul],
    exact ⟨e * n, rfl⟩,
  rcases (structure_presheaf.res.inverts_data BU (BVW BV BW) (HVWU HVU) ⟨s * (of a)^n, Hans⟩) with ⟨w, Hw⟩,
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)) at Hn,
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hn,
  dsimp [structure_presheaf_on_basis.res_to_inter],
  dsimp [structure_presheaf_on_basis.res] at *,
  rw [←Hn, is_localization_initial_comp],
  rw ←Hn at Hw,
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hw,
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)) at Hw,
  rw is_localization_initial_comp at Hw,
  use [(of (a^n)) * w],
  rw ←mul_assoc,
  rw ←is_ring_hom.map_mul (of : R → localization R (S (V ∩ W))),
  exact Hw,
  -- Setup.
  -- rintros ⟨s, Hs⟩,
  -- rcases (indefinite_description _ Hs) with ⟨m, Hsm⟩,
  -- rw ←is_ring_hom.map_mul (of : R → localization R (S U)) at Hsm,
  -- rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hsm,
  -- dsimp [structure_presheaf_on_basis.res_to_inter],
  -- dsimp [structure_presheaf_on_basis.res],
  -- rw [←Hsm, is_localization_initial_comp],
  -- -- Find inverse.
  -- let fg := some (BVW BV BW),
  -- have Hfgem : fg^(e*m) ∈ S (V ∩ W),
  --   apply @is_submonoid.pow_mem _ _ _,
  --   rw [some_spec (BVW BV BW)],
  --   exact set.subset.refl _,
  -- use [⟦⟨a^m, ⟨fg^(e*m), Hfgem⟩⟩⟧],
  -- -- Arithmetic.
  -- apply quotient.sound,
  -- use [1, is_submonoid.one_mem _],
  -- simp [-sub_eq_add_neg, sub_mul, sub_eq_zero],
  -- erw [pow_mul, Hea, mul_pow, mul_comm],
end

lemma structure_presheaf.res_to_inter.has_denom_data
: has_denom_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
begin
  rcases (indefinite_description _ (pow_eq.fg BU BV BW HVU)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  clear Ha,
  -- Using structure_presheaf.res.has_denom
  intros x,
  constructor,
  -- ( (f * g)^k, y ∈ R[1/S(U)] )
end

lemma structure_presheaf.res_to_inter.ker_le
: ker (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) 
≤ submonoid_ann (powers ((of (some BV)) * (of (some BW)))) :=
begin 
  sorry,
end

lemma structure_presheaf.res_to_inter.localization
: is_localization_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
{ inverts := structure_presheaf.res_to_inter.inverts_data BU BV BW HVU,
  has_denom := structure_presheaf.res_to_inter.has_denom_data BU BV BW HVU, 
  ker_le := structure_presheaf.res_to_inter.ker_le BU BV BW HVU }

end structure_presheaf