/-
  A concrete characterisation of the ideal map induced by a ring homomorphism
  with the localization property.
-/

import ring_theory.ideal_operations
import ring_theory.localization
import to_mathlib.localization.localization_alt

open localization_alt

universe u

section 

parameters {R : Type u} [comm_ring R] 
parameters {Rf : Type u} [comm_ring Rf] {h : R → Rf} [is_ring_hom h]
parameters {f : R} (HL : is_localization_data (powers f) h) 

include HL

lemma localization.zero (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : (0 : R) ∈ powers f)
: (ideal.map h I : ideal Rf) = ⊥ :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  apply ideal.ext,
  intros x,
  split,
  swap,
  { intros H,
    simp at H,
    rw H,
    rw ←is_ring_hom.map_zero h,
    apply ideal.mem_map_of_mem,
    simp, },
  { intros Hx,
    rcases (Hden x) with ⟨⟨a, b⟩, Hab⟩,
    simp at Hab,
    rcases (Hinv a) with ⟨w, Hw⟩,
    have Hall : ∀ (y : R), y ∈ submonoid_ann (powers f),
      intros y,
      simp [submonoid_ann, set.range, ann_aux],
      use [⟨y, ⟨0, Hfn⟩⟩],
      simp,
    have Htop : submonoid_ann (powers f) = ⊤,
      apply ideal.ext,
      intros x,
      split,
      { intros Hx,
        cases Hx,
        unfold ann_aux at Hx_w, },
      { intros Hx,
        exact (Hall x), },
    replace Hker := inverts_ker (powers f) h (inverts_of_data (powers f) h Hinv),
    unfold ker at Hker,
    rw Htop at Hker,
    have Hx : (1 : R) ∈ (⊤ : ideal R),
      trivial,
    replace Hx := Hker Hx,
    replace Hx : h 1 = 0 := Hx,
    rw (is_ring_hom.map_one h) at Hx,
    rw ←mul_one x,
    rw Hx,
    simp, },
end

-- Concrete ideal.

def localisation_map_ideal (I : ideal R) : ideal Rf :=
{ carrier := { x | ∃ (y ∈ h '' I) (r : Rf), x = y * r },
  zero :=
    begin
      use [h 0, 0],
      exact ⟨I.2, rfl⟩,
      use 1,
      rw mul_one,
      rw ←is_ring_hom.map_zero h,
    end,
  add := 
    begin
      intros x y Hx Hy,
      rcases Hx with ⟨a, ⟨Ha, ⟨r, Hx⟩⟩⟩,
      rcases Hy with ⟨b, ⟨Hb, ⟨t, Hy⟩⟩⟩,
      rcases Ha with ⟨v, ⟨Hv, Ha⟩⟩,
      rcases Hb with ⟨w, ⟨Hw, Hb⟩⟩,
      rw ←Ha at Hx,
      rw ←Hb at Hy,
      rw [Hx, Hy],
      rcases HL with ⟨Hinv, Hden, Hker⟩,
      rcases (Hden r) with ⟨⟨fn, l⟩, Hl⟩,
      rcases (Hinv fn) with ⟨hfninv, Hfn⟩,
      simp at Hl,
      rw mul_comm at Hfn,
      rcases (Hden t) with ⟨⟨fm, k⟩, Hk⟩,
      rcases (Hinv fm) with ⟨hfminv, Hfm⟩,
      simp at Hk,
      rw mul_comm at Hfm,
      -- Get rid of r.
      rw [←one_mul (_ + _), ←Hfn, mul_assoc, mul_add, mul_comm _ r, ←mul_assoc _ r _, Hl],
      -- Get rid of t.
      rw [←one_mul (_ * _), ←Hfm, mul_assoc, ←mul_assoc (h _) _ _, mul_comm (h _)],
      rw [mul_assoc _ (h _) _, mul_add, ←mul_assoc _ _ t, add_comm],
      rw [←mul_assoc (h fm) _ _, mul_comm (h fm), mul_assoc _ _ t, Hk],
      -- Rearrange.
      repeat { rw ←is_ring_hom.map_mul h, },
      rw [←mul_assoc _ _ v, mul_assoc ↑fn, mul_comm w, ←mul_assoc ↑fn], 
      rw [←is_ring_hom.map_add h, ←mul_assoc, mul_comm],
      -- Ready to prove it.
      have HyI : ↑fn * k * w + ↑fm * l * v ∈ ↑I,
        apply I.3,
        { apply I.4,
          exact Hw, },
        { apply I.4,
          exact Hv, },
      use [h (↑fn * k * w + ↑fm * l * v)],
      use [⟨↑fn * k * w + ↑fm * l * v, ⟨HyI, rfl⟩⟩],
      use [hfminv * hfninv],
    end,
  smul := 
    begin
      intros c x Hx,
      rcases Hx with ⟨a, ⟨Ha, ⟨r, Hx⟩⟩⟩,
      rcases Ha with ⟨v, ⟨Hv, Ha⟩⟩,
      rw [Hx, ←Ha],
      rw mul_comm _ r,
      unfold has_scalar.smul,
      rw [mul_comm r, mul_comm c, mul_assoc],
      use [h v, ⟨v, ⟨Hv, rfl⟩⟩, r * c],
    end, }

-- They coincide

lemma localisation_map_ideal.eq (I : ideal R) [PI : ideal.is_prime I] 
: ideal.map h I = localisation_map_ideal I :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  apply le_antisymm,
  { have Hgen : h '' I ⊆ localisation_map_ideal I,
      intros x Hx,
      use [x, Hx, 1],
      simp,
    replace Hgen := ideal.span_mono Hgen,
    rw ideal.span_eq at Hgen,
    exact Hgen, },
  { intros x Hx,
    rcases Hx with ⟨y, ⟨z, ⟨HzI, Hzy⟩⟩, ⟨r, Hr⟩⟩,
    rw [Hr, ←Hzy],
    exact ideal.mul_mem_right _ (ideal.mem_map_of_mem HzI), }
end

end
