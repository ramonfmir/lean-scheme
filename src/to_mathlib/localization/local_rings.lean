/-
  A ring with the localization property at a prime ideal is a local ring.
-/

import ring_theory.ideals
import ring_theory.localization
import to_mathlib.localization.localization_alt

universes u v

local attribute [instance] classical.prop_decidable 

open localization_alt

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables {f : α → β} [is_ring_hom f]
variables {P : ideal α} (HP : ideal.is_prime P) 
variables (Hloc : is_localization_data (-P : set α) f)

include Hloc

lemma local_ring.of_is_localization_data_at_prime : local_ring β :=
begin
  apply local_of_nonunits_ideal,
  { -- 0 ≠ 1.
    intros HC,
    rw ←is_ring_hom.map_one f at HC,
    have Hone : (1 : α) ∈ ker f := HC.symm,
    replace Hone := Hloc.ker_le Hone,
    rcases Hone with ⟨⟨⟨u, ⟨v, HvnP⟩⟩, Huv⟩, Heq⟩,
    dsimp at Huv,
    dsimp at Heq,
    rw Heq at Huv,
    have Hzero : (0 : α) ∈ P := ideal.zero_mem P,
    rw ←Huv at Hzero,
    cases (HP.2 Hzero) with Hone Hv,
    { apply HP.1,
      rw ideal.eq_top_iff_one,
      exact Hone, },
    { change v ∉ P at HvnP,
      exact (HvnP Hv), }, },
  { -- x and y nonunits then x + y is not a unit.
    intros x y Hx Hy HC,
    change ¬is_unit x at Hx,
    change ¬is_unit y at Hy,
    rcases is_unit_iff_exists_inv.1 HC with ⟨inv, Hinv⟩,
    rcases Hloc.has_denom x with ⟨⟨⟨q₁, Hq₁⟩, p₁⟩, Hp₁q₁⟩,
    rcases Hloc.has_denom y with ⟨⟨⟨q₂, Hq₂⟩, p₂⟩, Hp₂q₂⟩,
    rcases Hloc.has_denom inv with ⟨⟨⟨q₃, Hq₃⟩, p₃⟩, Hp₃q₃⟩,
    change q₁ ∉ P at Hq₁,
    change q₂ ∉ P at Hq₂,
    change q₃ ∉ P at Hq₃,
    change f q₁ * x = f p₁ at Hp₁q₁,
    change f q₂ * y = f p₂ at Hp₂q₂,
    change f q₃ * inv = f p₃ at Hp₃q₃,
    have Hp₁P : p₁ ∈ P,
      by_contra Hp₁,
      apply Hx,
      rcases (Hloc.inverts ⟨p₁, Hp₁⟩) with ⟨w₁, Hw₁⟩,
      change f p₁ * w₁ = 1 at Hw₁,
      apply is_unit_of_mul_one x (f q₁ * w₁),
      rw [←mul_assoc, mul_comm x, Hp₁q₁],
      exact Hw₁,
    have Hp₂P : p₂ ∈ P,
      by_contra Hp₂,
      apply Hy,
      rcases (Hloc.inverts ⟨p₂, Hp₂⟩) with ⟨w₂, Hw₂⟩,
      change f p₂ * w₂ = 1 at Hw₂,
      apply is_unit_of_mul_one y (f q₂ * w₂),
      rw [←mul_assoc, mul_comm y, Hp₂q₂],
      exact Hw₂,
    have Hp₃q₂p₁P : p₃ * q₂ * p₁ ∈ P := ideal.mul_mem_left P Hp₁P,
    have Hp₃q₁p₂P : p₃ * q₁ * p₂ ∈ P := ideal.mul_mem_left P Hp₂P,
    have Hmem := (ideal.neg_mem_iff P).2 (ideal.add_mem P Hp₃q₂p₁P Hp₃q₁p₂P),
    have Hq₁q₂q₃nP : q₁ * q₂ * q₃ ∉ P,
      intros HC,
      cases (HP.2 HC) with HC₁₂ HC₃,
      { cases (HP.2 HC₁₂) with HC₁ HC₂,
        { exact (Hq₁ HC₁), },
        { exact (Hq₂ HC₂), } },
      { exact (Hq₃ HC₃), },
    have Hzero : f (q₁ * q₂ * q₃ + -(p₃ * q₂ * p₁ + p₃ * q₁ * p₂)) = 0,
      rw [←sub_eq_add_neg, is_ring_hom.map_sub f, sub_eq_zero, is_ring_hom.map_add f],
      iterate 6 { rw is_ring_hom.map_mul f, },
      iterate 2 { rw mul_assoc (f p₃), },
      rw [←mul_add (f p₃), ←Hp₃q₃, mul_comm (f q₃ * inv), mul_comm (f q₃), ←mul_assoc _ inv], 
      rw [←Hp₁q₁, ←mul_assoc (f q₂), mul_comm (f q₂)], 
      rw [←Hp₂q₂, ←mul_assoc (f q₁)],
      rw [←mul_add (f q₁ * f q₂), mul_assoc _ (x + y) inv, Hinv, mul_one],
    rcases (Hloc.ker_le Hzero) with ⟨⟨⟨u, ⟨v, HvnP⟩⟩, Huv⟩, Helem⟩,
    change v ∉ P at HvnP,
    dsimp only [subtype.coe_mk] at Huv,
    dsimp only [subtype.coe_mk] at Helem,
    rw Helem at Huv; clear Helem,
    cases (HP.mem_or_mem_of_mul_eq_zero Huv) with Helem HvP,
    { rw ideal.add_mem_iff_left P Hmem at Helem,
      exact (Hq₁q₂q₃nP Helem), },
    { exact (HvnP HvP), } }
end
