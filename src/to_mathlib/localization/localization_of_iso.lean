/-
  If f : A → B has the localization property for a multiplicative S and g : B → C
  is a bijective ring homomorphism, then (g ∘ f) has the localization property for S too.
-/

import algebra.ring
import to_mathlib.localization.localization_alt

universes u v w

noncomputable theory

open localization_alt

variables {A : Type u} {B : Type v} {C : Type w} [comm_ring A] [comm_ring B] [comm_ring C]
variables (S : set A) [is_submonoid S] (f : A → B) [is_ring_hom f] (Hloc : is_localization_data S f)
variables (g : B → C) (Hg₁ : function.bijective g) (Hg₂ : is_ring_hom g)

include Hloc Hg₁ Hg₂

lemma is_localization_data.of_iso.inverts_data : inverts_data S (g ∘ f) :=
begin
  rintros s,
  rcases (Hloc.inverts s) with ⟨w, Hw⟩,
  use (g w),
  rw [←is_ring_hom.map_mul g, Hw, is_ring_hom.map_one g],
end

lemma is_localization_data.of_iso.has_denom : has_denom S (g ∘ f) :=
begin
  intros x,
  rw function.bijective_iff_has_inverse at Hg₁,
  rcases Hg₁ with ⟨h, Hhleft, Hhright⟩,
  rcases (Hloc.has_denom (h x)) with ⟨pq, Hpq⟩,
  replace Hpq := congr_arg g Hpq,
  rw is_ring_hom.map_mul g at Hpq,
  rw Hhright at Hpq,
  use [pq, Hpq],
end

lemma is_localization_data.of_iso.has_denom_data : has_denom_data S (g ∘ f) :=
has_denom_some S (g ∘ f) (is_localization_data.of_iso.has_denom S f Hloc g Hg₁ Hg₂)

lemma is_localization_data.of_iso.ker_le : ker (g ∘ f) ≤ submonoid_ann S :=
begin
  intros x Hx,
  rw function.bijective_iff_has_inverse at Hg₁,
  rcases Hg₁ with ⟨h, Hhleft, Hhright⟩,
  change g (f x) = 0 at Hx,
  replace Hx := congr_arg h Hx,
  rw ←is_ring_hom.map_zero g at Hx,
  iterate 2 { rw Hhleft at Hx, },
  exact Hloc.ker_le Hx,
end

lemma is_localization_data.of_iso : is_localization_data S (g ∘ f) :=
{ inverts := is_localization_data.of_iso.inverts_data S f Hloc g Hg₁ Hg₂,
  has_denom := is_localization_data.of_iso.has_denom_data S f Hloc g Hg₁ Hg₂,
  ker_le := is_localization_data.of_iso.ker_le S f Hloc g Hg₁ Hg₂, }
