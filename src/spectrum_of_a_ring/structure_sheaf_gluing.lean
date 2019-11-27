/- 
  Second argument of the ring lemma.

  We show that the map R[1/fᵢ] → R[1/fᵢfⱼ] inverts fᵢ/1 * fⱼ/1.
-/

import ring_theory.localization
import to_mathlib.localization.localization_alt
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

variables {R : Type u} [comm_ring R]
variables {U V W : opens (Spec R)} 
variables (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (BW : W ∈ D_fs R) 
variables (HVU : V ⊆ U) (HWU : W ⊆ U)

def BVW : V ∩ W ∈ D_fs R := (D_fs_standard_basis R).2 BV BW
def HVWU : V ∩ W ⊆ U := set.subset.trans (set.inter_subset_left V W) HVU

def structure_presheaf_on_basis.res_to_inter 
: localization R (S U) → localization R (S (V ∩ W)) :=
structure_presheaf_on_basis.res BU (BVW BV BW) (HVWU HVU)

def structure_presheaf_on_basis.res_to_inter_left
: localization R (S V) → localization R (S (V ∩ W)) :=
structure_presheaf_on_basis.res BV (BVW BV BW) (set.inter_subset_left V W)

def structure_presheaf_on_basis.res_to_inter_right
: localization R (S W) → localization R (S (V ∩ W)) :=
structure_presheaf_on_basis.res BW (BVW BV BW) (set.inter_subset_right V W)

instance structure_presheaf_on_basis.res_to_inter.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
by simp [structure_presheaf_on_basis.res_to_inter, structure_presheaf_on_basis.res]; 
by apply_instance

instance structure_presheaf_on_basis.res_to_inter_to_inter_left.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res_to_inter_left BV BW) :=
by simp [structure_presheaf_on_basis.res_to_inter_left, structure_presheaf_on_basis.res]; 
by apply_instance

instance structure_presheaf_on_basis.res_to_inter_to_inter_right.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res_to_inter_right BV BW) :=
by simp [structure_presheaf_on_basis.res_to_inter_right, structure_presheaf_on_basis.res]; 
by apply_instance

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

lemma structure_presheaf.res_to_inter.inverts_data
: inverts_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
begin
  rcases (indefinite_description _ (pow_eq.fg BU BV BW HVU)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  clear Ha,
  let f := some BV,
  let g := some BW,
  let fg := some (BVW BV BW),
  -- Using structure_presheaf.res.inverts_data
  rintros ⟨s, Hs⟩,
  rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
  have Hans : s * (of (a^n)) ∈ powers ((of : R → localization R (S U)) fg),
    rw is_semiring_hom.map_pow (of : R → localization R (S U)),
    rw [←Hn,  ←mul_pow],
    iterate 2 { rw ←is_ring_hom.map_mul (of : R → localization R (S U)), },
    rw [mul_comm, ←Hea, is_semiring_hom.map_pow (of : R → localization R (S U)), ←pow_mul],
    exact ⟨e * n, rfl⟩,
  rcases (structure_presheaf.res.inverts_data BU (BVW BV BW) (HVWU HVU) ⟨s * (of (a^n)), Hans⟩) with ⟨w, Hw⟩,
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)) at Hn,
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hn,
  dsimp [structure_presheaf_on_basis.res_to_inter],
  dsimp only [subtype.coe_mk] at Hw,
  rw ←Hn,
  rw ←Hn at Hw,
  rw is_ring_hom.map_mul (structure_presheaf_on_basis.res BU (BVW BV BW) (HVWU HVU)) at Hw,
  use [(structure_presheaf_on_basis.res BU (BVW BV BW) (HVWU HVU) (of (a^n))) * w],
  rw ←mul_assoc,
  exact Hw,
end

lemma structure_presheaf.res_to_inter.has_denom_data
: has_denom_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
begin
  rcases (indefinite_description _ (pow_eq.fmulg BU BV BW HVU)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  clear Ha,
  let f := some BV,
  let g := some BW,
  let fg := some (BVW BV BW),
  -- Using structure_presheaf.res.has_denom
  -- This gives us ( fg^n, y ∈ R[1/S(U)] )
  -- We have (f*g)^(n*e) = (fg)^n * a^n 
  -- So let x = y * (of a)^n.
  intros x,
  rcases (structure_presheaf.res.has_denom_data BU (BVW BV BW) (HVWU HVU) x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
  dsimp only [subtype.coe_mk] at Hpq,
  rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
  use [⟨⟨(of f * of g)^(e * n), ⟨e * n, rfl⟩⟩, p * (of a)^n⟩],
  dsimp [structure_presheaf_on_basis.res_to_inter],
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)),
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
  rw [pow_mul, Hea],
  rw is_semiring_hom.map_pow (of : R → localization R (S U)),
  rw is_ring_hom.map_mul (of : R → localization R (S U)),
  rw [mul_pow, Hn, mul_comm p],
  iterate 2 { rw is_ring_hom.map_mul (structure_presheaf_on_basis.res BU (BVW BV BW) (HVWU HVU)), },
  rw [←Hpq, ←mul_assoc],
end

lemma structure_presheaf.res_to_inter.ker_le
: ker (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) 
≤ submonoid_ann (powers ((of (some BV)) * (of (some BW)))) :=
begin 
  rcases (indefinite_description _ (pow_eq.fmulg BU BV BW HVU)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  clear Ha,
  let f := some BV,
  let g := some BW,
  let fg := some (BVW BV BW),
  -- Using structure_presheaf.res.ker_le
  intros x Hx,
  dsimp [structure_presheaf_on_basis.res_to_inter] at Hx,
  replace Hx := (structure_presheaf.res.ker_le BU (BVW BV BW) (HVWU HVU)) Hx,
  rcases Hx with ⟨⟨⟨u, ⟨v, ⟨n, Hv⟩⟩⟩, Hxfgn⟩, Hx⟩,
  dsimp at Hx,
  dsimp at Hxfgn,
  rw [Hx, ←Hv] at Hxfgn; clear Hx; clear Hv,
  let fgne : localization R (S U) := (of f * of g)^(e * n),
  have Hfgne : fgne ∈ (powers (of f * of g) : set (localization R (S U))) := ⟨e * n, rfl⟩,
  have Hxfgne : x * fgne = 0,
    dsimp [fgne],
    rw ←is_ring_hom.map_mul (of : R → localization R (S U)),
    rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
    rw [pow_mul, Hea],
    rw is_semiring_hom.map_pow (of : R → localization R (S U)),
    rw is_ring_hom.map_mul (of : R → localization R (S U)),
    rw [mul_pow, mul_comm ((of a)^n), ←mul_assoc, Hxfgn, zero_mul],
  use ⟨⟨x, ⟨fgne, Hfgne⟩⟩, Hxfgne⟩,
end

lemma structure_presheaf.res_to_inter.localization
: is_localization_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU) :=
{ inverts := structure_presheaf.res_to_inter.inverts_data BU BV BW HVU,
  has_denom := structure_presheaf.res_to_inter.has_denom_data BU BV BW HVU, 
  ker_le := structure_presheaf.res_to_inter.ker_le BU BV BW HVU }

end structure_presheaf
