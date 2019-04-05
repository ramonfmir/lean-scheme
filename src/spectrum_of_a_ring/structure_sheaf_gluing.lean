import ring_theory.localization
import preliminaries.localisation
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_res_to_inter

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

-- TEST: Does it work for left just loc on the powers.

lemma structure_presheaf.res_to_inter_left.inverts'
: inverts_data
    (powers ((of (some BU)) * (of (some BV)))) 
    (structure_presheaf_on_basis.res_to_inter_left BU BV) :=
begin
  rintros ⟨s, Hs⟩,
  rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)) at Hn,
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hn,
  dsimp only [subtype.coe_mk, structure_presheaf_on_basis.res_to_inter_left],
  rw ←Hn,
  rw is_localization_initial_comp,

  have BUV := (D_fs_standard_basis R).2 BU BV,
  let f := some BU,
  let g := some BV,
  let fg := some BUV,
    have HDfg: Spec.D'(fg) ⊆ Spec.D'(f * g),
    rw Spec.D'.product_eq_inter,
    show Spec.DO R (fg) ⊆ Spec.DO R (f) ∩ Spec.DO R (g),
    rw [←some_spec BU, ←some_spec BV, ←some_spec BUV],
    exact set.subset.refl _,
  rcases (indefinite_description _ (pow_eq.of_Dfs_subset HDfg)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  have HfneSU : f^(n*e) ∈ S U,
    apply @is_submonoid.pow_mem _ _ _ _,
    rw some_spec BU,
    exact set.subset.refl _,
  have HfgSUV : fg^(e*n) ∈ S (U ∩ V),
    apply @is_submonoid.pow_mem _ _ _ _,
    rw some_spec BUV,
    exact set.subset.refl _,

  use ⟦⟨a^n, ⟨fg^(e*n), HfgSUV⟩⟩⟧,
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp [-sub_eq_add_neg, sub_mul, sub_eq_zero],
  rw pow_mul,
  rw Hea,
  rw mul_pow,
  ring,
end

lemma structure_presheaf.res_to_inter_left.has_denom'
: has_denom_data
    (powers ((of (some BU)) * (of (some BV)))) 
    (structure_presheaf_on_basis.res_to_inter_left BU BV) :=
begin
  intros x,
  have BUV := (D_fs_standard_basis R).2 BU BV,
  have HUVV : U ∩ V ⊆ V := set.inter_subset_right U V,
  let f := some BU,
  let g := some BV,
  let fg := some BUV,
  rcases (structure_presheaf.has_denom_data BUV x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
  rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
  dsimp only [subtype.coe_mk] at Hpq,

  have HDfg: Spec.D'(f * g) ⊆ Spec.D'(fg),
    rw Spec.D'.product_eq_inter,
    show Spec.DO R (f) ∩ Spec.DO R (g) ⊆ Spec.DO R (fg),
    rw [←some_spec BU, ←some_spec BV, ←some_spec BUV],
    exact set.subset.refl _,
  rcases (indefinite_description _ (pow_eq.of_Dfs_subset HDfg)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  have HfneSU : f^(n*e) ∈ S U,
    apply @is_submonoid.pow_mem _ _ _ _,
    rw some_spec BU,
    exact set.subset.refl _,

  use ⟨⟨(of f * of g)^(e*n), ⟨e*n, rfl⟩⟩, of (p*a^n)⟩,

  dsimp only [subtype.coe_mk, structure_presheaf_on_basis.res_to_inter_left],
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)),
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
  rw is_localization_initial_comp,
  rw is_localization_initial_comp,
  
  revert Hpq,
  apply quotient.induction_on x,
  rintros ⟨a', b'⟩ Hpq,
  erw quotient.eq at Hpq,
  rcases Hpq with ⟨t, ⟨Ht, Hpq⟩⟩,
  simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at Hpq,

  apply quotient.sound,
  use [t, Ht],

  simp [-sub_eq_add_neg, sub_mul, sub_eq_zero],
  repeat { rw ←mul_assoc },

  rw pow_mul,
  rw Hea,

  iterate 1 { rw [mul_assoc _ _ t, mul_comm _ t, ←mul_assoc] },
  rw Hpq,
  rw mul_pow,
  rw ←Hn,
  rw mul_comm,
  rw ←mul_assoc,
  rw ←mul_assoc,
end

lemma structure_presheaf.res_to_inter_left.ker_le'
: ker (structure_presheaf_on_basis.res_to_inter_left BU BV) 
≤ submonoid_ann (powers ((of (some BU)) * (of (some BV)))) :=
begin
  have BUV := (D_fs_standard_basis R).2 BU BV,
  let f := some BU,
  let g := some BV,
  let fg := some BUV,

  intros x Hx,
  change structure_presheaf_on_basis.res_to_inter_left BU BV x = 0 at Hx,
  rcases (structure_presheaf.has_denom_data BU x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
  rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
  dsimp only [subtype.coe_mk] at Hpq,
  have Hofp : structure_presheaf_on_basis.res_to_inter_left BU BV (of p) = 0,
    rw ←Hpq,
    rw is_ring_hom.map_mul (structure_presheaf_on_basis.res_to_inter_left BU BV),
    rw Hx,
    rw mul_zero,
  dsimp only [structure_presheaf_on_basis.res_to_inter_left] at Hofp,
  rw is_localization_initial_comp at Hofp,
  have Hpker : p ∈ ker (of : R → localization R (S (U ∩ V))) := Hofp,

  have Hpann := (structure_presheaf.ker_le BUV) Hpker,
  rcases Hpann with ⟨⟨⟨u, ⟨v, ⟨m, Hm⟩⟩⟩, Huv⟩, Hp⟩,
  dsimp only [subtype.coe_mk] at Huv,
  dsimp only [subtype.coe_mk] at Hp,
  rw [Hp, ←Hm] at Huv,

  have HDfg: Spec.D'(f * g) ⊆ Spec.D'(fg),
    rw Spec.D'.product_eq_inter,
    show Spec.DO R (f) ∩ Spec.DO R (g) ⊆ Spec.DO R (fg),
    rw [←some_spec BU, ←some_spec BV, ←some_spec BUV],
    exact set.subset.refl _,
  rcases (indefinite_description _ (pow_eq.of_Dfs_subset HDfg)) with ⟨a, Ha⟩,
  rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
  -- have HfneSU : f^(n*e) ∈ S U,
  --   apply @is_submonoid.pow_mem _ _ _ _,
  --   rw some_spec BU,
  --   exact set.subset.refl _,

  let g' : localization R (S U) := (of f * of g)^(e * m + n),
  have Hg' : g' ∈ powers (((of : R → localization R (S U)) f) * ((of : R → localization R (S U)) g)),
    dsimp [g'],
    exact ⟨(e * m + n), rfl⟩,

  have Hxann : x * g' = 0,
    dsimp [g'],
    rw ←is_ring_hom.map_mul (of : R → localization R (S U)),
    rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
    rw pow_add,
    rw pow_mul,
    rw Hea,
    rw mul_comm (_ ^ _),
    rw is_ring_hom.map_mul (of : R → localization R (S U)),
    rw is_semiring_hom.map_pow (of : R → localization R (S U)),
    rw ←mul_assoc,
    rw is_ring_hom.map_mul (of : R → localization R (S U)),
    rw mul_pow,
    rw ←mul_assoc,
    rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
    dsimp [f],
    rw Hn,
    rw mul_comm x,
    rw Hpq,
    rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
    rw ←is_ring_hom.map_mul (of : R → localization R (S U)),
    rw ←is_ring_hom.map_mul (of : R → localization R (S U)),
    rw mul_pow,
    rw ←mul_assoc,
    iterate 2 { rw [mul_assoc _ _ (fg ^ m), mul_comm _ (fg ^ m), ←mul_assoc] },
    dsimp [fg],
    rw Huv,
    rw zero_mul,
    rw zero_mul,
    rw is_ring_hom.map_zero (of : R → localization R (S U)),
    
  use ⟨⟨x, ⟨g', Hg'⟩⟩, Hxann⟩,
end

-- What we want?

-- lemma structure_presheaf.res_to_inter_left.inverts_data
-- : inverts_data 
--     (powers (of (some BV))) 
--     (structure_presheaf_on_basis.res_to_inter_left BU BV) :=
-- begin
--   rintros ⟨s, Hs⟩,
--   rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
--   rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hn,
--   dsimp only [subtype.coe_mk, structure_presheaf_on_basis.res_to_inter_left],
--   rw ←Hn,
--   rw is_localization_initial_comp,
--   let g := some BV,
--   have HgnSV : g^n ∈ S V,
--     apply @is_submonoid.pow_mem _ _ _ _,
--     rw some_spec BV,
--     exact set.subset.refl _,
--   have HUVV : U ∩ V ⊆ V := set.inter_subset_right U V,
--   have HSVSUV := S.rev_mono HUVV,
--   have HgnSUV := HSVSUV HgnSV,
--   use ⟦⟨1, ⟨g^n, HgnSUV⟩⟩⟧,
--   apply quotient.sound,
--   use [1, is_submonoid.one_mem _],
--   simp,
-- end

-- lemma structure_presheaf.res_to_inter_left.has_denom_data
-- : has_denom_data 
--     (powers (of (some BV))) 
--     (structure_presheaf_on_basis.res_to_inter_left BU BV) :=
-- begin
--   intros x,
--   have BUV := (D_fs_standard_basis R).2 BU BV,
--   have HUVV : U ∩ V ⊆ V := set.inter_subset_right U V,
--   let f := some BU,
--   let g := some BV,
--   let fg := some BUV,
--   rcases (structure_presheaf.has_denom_data BUV x) with ⟨⟨⟨q, Hq⟩, p⟩, Hpq⟩,
--   rcases (indefinite_description _ Hq) with ⟨n, Hn⟩,
--   dsimp only [subtype.coe_mk] at Hpq,

--   sorry,



--   -- have HDfg: Spec.D'(f * g) ⊆ Spec.D'(fg),
--   --   rw Spec.D'.product_eq_inter,
--   --   show Spec.DO R (f) ∩ Spec.DO R (g) ⊆ Spec.DO R (fg),
--   --   rw [←some_spec BU, ←some_spec BV, ←some_spec BUV],
--   --   exact set.subset.refl _,
--   -- rcases (indefinite_description _ (pow_eq.of_Dfs_subset HDfg)) with ⟨a, Ha⟩,
--   -- rcases (indefinite_description _ Ha) with ⟨e, Hea⟩,
--   -- have HfneSU : f^(n*e) ∈ S U,
--   --   apply @is_submonoid.pow_mem _ _ _ _,
--   --   rw some_spec BU,
--   --   exact set.subset.refl _,
  
--   -- use ⟨⟨(of g)^(n*e), ⟨n*e, rfl⟩⟩, ⟦⟨p*a^n, ⟨f^(n*e), HfneSU⟩⟩⟧⟩,

--   -- dsimp only [subtype.coe_mk, structure_presheaf_on_basis.res_to_inter_left],
--   -- rw ←is_semiring_hom.map_pow (of : R → localization R (S U)),
--   -- rw is_localization_initial_comp,
--   -- unfold is_localization_initial,
--   -- rcases (of.is_localization_data (S U)).has_denom ⟦(p * a ^ n, ⟨f ^ (n * e), HfneSU⟩)⟧ with ⟨⟨v, u⟩, Huv⟩,
--   -- dsimp only [subtype.coe_mk] at *,
--   -- rcases (inverts_data.res_inter_left.of_basis_subset BU BV v) with ⟨w, Hw⟩,
--   -- dsimp only [subtype.coe_mk] at *,

--   -- revert Hpq,
--   -- apply quotient.induction_on x,
--   -- rintros ⟨a', b'⟩ Hpq,
--   -- revert Hw,
--   -- apply quotient.induction_on w,
--   -- rintros ⟨c', d'⟩ Hw,

--   -- erw quotient.eq at Hpq,
--   -- dsimp only [subtype.coe_mk] at Hpq,
--   -- rcases Hpq with ⟨k1, ⟨Hk1, Hpq⟩⟩,
--   -- simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at Hpq,

--   -- erw quotient.eq at Huv,
--   -- dsimp only [subtype.coe_mk] at Huv,
--   -- rcases Huv with ⟨k2, ⟨Hk2, Huv⟩⟩,
--   -- simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at Huv,
--   -- replace Hk2 : k2 ∈ S (U ∩ V) := (S.rev_mono (set.inter_subset_left U V)) Hk2,

--   -- erw quotient.eq at Hw,
--   -- dsimp only [subtype.coe_mk] at Hw,
--   -- rcases Hw with ⟨k3, ⟨Hk3, Hw⟩⟩,
--   -- simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at Hw,


--   -- apply quotient.sound,
--   -- use [k1 * k2 * k3, is_submonoid.mul_mem (is_submonoid.mul_mem Hk1 Hk2) Hk3],
--   -- simp [-sub_eq_add_neg, sub_mul, sub_eq_zero],
--   -- repeat { rw ←mul_assoc, },
--   -- have := inverts_data.of_basis_subset.aux BV BUV HUVV q,
--   -- constructor,
-- end

-- lemma structure_presheaf.res_to_inter_left.ker_le
-- : ker (structure_presheaf_on_basis.res_to_inter_left BU BV) 
-- ≤ submonoid_ann (powers (of (some BV))) :=
-- begin 
--   sorry,
-- end

-- lemma structure_presheaf.res_to_inter_left.localization
-- : is_localization_data 
--     (powers (of (some BV))) 
--     (structure_presheaf_on_basis.res_to_inter_left BU BV) :=
-- { inverts := structure_presheaf.res_to_inter_left.inverts_data BU BV,
--   has_denom := structure_presheaf.res_to_inter_left.has_denom_data BU BV, 
--   ker_le := structure_presheaf.res_to_inter_left.ker_le BU BV }

-------

lemma structure_presheaf.res_to_inter.inverts_data
: inverts_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
begin
  rintros ⟨s, Hs⟩,
  rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
  have BVW := (D_fs_standard_basis R).2 BV BW,
  have HVWU : V ∩ W ⊆ U := set.subset.trans (set.inter_subset_left V W) HVU,
  have HSUSVW := S.rev_mono HVWU,
  have HDfg : (V ∩ W).val ⊆ Spec.D' ((some BV) * (some BW)),
    rw Spec.D'.product_eq_inter,
    show V ∩ W ⊆ Spec.DO R (some BV) ∩ Spec.DO R (some BW),
    rw [←some_spec BV, ←some_spec BW],
    apply set.subset.refl,
  rw ←is_ring_hom.map_mul (of : R → localization R (S U)) at Hn,
  rw ←is_semiring_hom.map_pow (of : R → localization R (S U)) at Hn,
  dsimp only [subtype.coe_mk, structure_presheaf_on_basis.res_to_inter],
  rw ←Hn,
  rw is_localization_initial_comp,
  --have Hinv := inverts_data.of_basis_subset BU BVW HVWU s,
  sorry,

  
  --have := structure_presheaf.inverts_data BVW s,
end

lemma structure_presheaf.res_to_inter.has_denom_data
: has_denom_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
begin
  sorry,
end

lemma structure_presheaf.res_to_inter.ker_le
: ker (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) 
≤ submonoid_ann (powers ((of (some BV)) * (of (some BW)))) :=
begin 
  sorry,
end

lemma structure_presheaf.res_to_inter.localization
: is_localization_data 
    (powers ((of (some BV)) * (of (some BW)))) 
    (structure_presheaf_on_basis.res_to_inter BU BV BW HVU HWU) :=
{ inverts := structure_presheaf.res_to_inter.inverts_data BU BV BW HVU HWU,
  has_denom := structure_presheaf.res_to_inter.has_denom_data BU BV BW HVU HWU, 
  ker_le := structure_presheaf.res_to_inter.ker_le BU BV BW HVU HWU }

end structure_presheaf