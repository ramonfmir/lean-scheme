import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization

universe u

local attribute [instance] classical.prop_decidable

noncomputable theory

open topological_space
open classical
open localization
open localization_alt

section localization_map

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

def inverts_data.of_basis_subset'
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

-- def localization.map.of_Dfs_subset
-- : localization R (powers (some BU)) 
-- → localization R (powers (some BV)) :=
-- is_localization_initial 
--   (powers (classical.some BU))
--   (of : R → localization R (powers (some BU)))
--   (of.is_localization_data (powers (some BU)))
--   (of : R → localization R (powers (some BV)))
--   (inverts_data.of_basis_subset BU BV H)

include BU BV

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

def structure_presheaf_on_basis.res
: localization R (S U) 
→ localization R (S V) :=
is_localization_initial 
  (S U)
  (of : R → localization R (S U))
  (of.is_localization_data (S U))
  (of : R → localization R (S V))
  (inverts_data.of_basis_subset BU BV H)

instance structure_presheaf_on_basis.res.is_ring_hom 
: is_ring_hom (structure_presheaf_on_basis.res BU BV H) :=
by simp [structure_presheaf_on_basis.res]; by apply_instance

end localization_map

section more_maps

variables {R : Type u} [comm_ring R]
variables {U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)

lemma structure_presheaf_on_basis.res_eq
: (structure_presheaf_on_basis R).res BU BV H = structure_presheaf_on_basis.res BU BV H :=
begin
  apply funext,
  intros x,
  apply quotient.induction_on x,
  rintros ⟨a, b⟩,
  simp [structure_presheaf_on_basis.res, is_localization_initial],
  rcases ((structure_presheaf.localization BU).has_denom ⟦(a, b)⟧) with ⟨⟨q, p⟩, Hpq⟩,
  -- Show that q is in S(U).
  --rcases inverts_data.of_basis_subset BU BV H q with ⟨w, Hw⟩,

end

-- The restriction maps are actually the unique ring homomorphism coming from
-- the universal property.

-- lemma structure_presheaf_on_basis.res_eq
-- : (structure_presheaf_on_basis R).res BU BV H = structure_presheaf_on_basis.res BU BV H :=
-- begin
--   apply funext,
--   intros x,
--   apply quotient.induction_on x,
--   rintros ⟨a, b⟩,
--   simp [structure_presheaf_on_basis.res, is_localization_initial],
--   rcases ((structure_presheaf.localization BU).has_denom ⟦(a, b)⟧) with ⟨⟨q, p⟩, Hpq⟩,
--   dsimp at *,
--   rcases structure_presheaf.inverts_data.of_basis_subset BU BV H q with ⟨w, Hw⟩,
--   revert Hw,
--   apply quotient.induction_on w,
--   rintros ⟨c, d⟩,
--   intros Hw,
--   apply quotient.sound,
--   dsimp,
--   erw quotient.eq at Hpq,
--   rcases Hpq with ⟨t, ⟨Ht, Hpq⟩⟩,
--   simp [-sub_eq_add_neg] at Hpq,
--   erw quotient.eq at Hw,
--   rcases Hw with ⟨s, ⟨Hs, Hw⟩⟩,
--   simp [-sub_eq_add_neg] at Hw,

--   rcases (pow_eq.of_basis_subset BU BV H) with ⟨a₁, ⟨e₁, Ha₁⟩⟩,

--   have HDfDt : Spec.D'(some BU) ⊆ Spec.D'(t),
--     change U ⊆ Spec.DO R (t) at Ht,
--     rw some_spec BU at Ht,
--     exact Ht,

--   rcases (pow_eq.of_Dfs_subset HDfDt) with ⟨a₂, ⟨e₂, Ha₂⟩⟩,

--   have Heq : t * a₂ * a₁ ^ e₂ = (some BV) ^ (e₁ * e₂),
--     rw mul_comm at Ha₂,
--     rw ←Ha₂,
--     rw ←mul_pow,
--     rw mul_comm at Ha₁,
--     rw ←Ha₁,
--     rw ←pow_mul,

--   have HgS := S.f_mem (some BV),
--   rw ←some_spec BV at HgS,

--   have HtS : t * a₂ * a₁ ^ e₂ ∈ S V := Heq.symm ▸ is_submonoid.pow_mem HgS,

--   use [s * (t * a₂ * a₁ ^ e₂), is_submonoid.mul_mem Hs HtS],
--   simp [-sub_eq_add_neg],
--   rw sub_mul,
--   rw sub_mul at Hpq,
--   rw sub_mul at Hw,
--   rw sub_eq_zero,
--   rw sub_eq_zero at Hpq,
--   rw sub_eq_zero at Hw,
--   repeat { rw ←mul_assoc },
--   suffices Hsuff : ↑b * p * c * s * t = ↑d * a * s * t,
--     erw Hsuff,
  
--   iterate 2 { rw [mul_assoc _ _ t, mul_comm _ t, ←mul_assoc] },
--   rw Hpq,

--   symmetry,

--   rw [mul_assoc _ _ s, mul_comm _ s, ←mul_assoc],
--   rw Hw,

--   ring,
-- end

end more_maps
