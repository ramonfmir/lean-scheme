/-
  If f is a ring homomorphism and P a prime ideal, f⁻¹(I) is also prime.

  https://stacks.math.columbia.edu/tag/00BV
-/

import data.set
import ring_theory.ideals

open lattice

universes u v

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f]

section ideal_preimage

-- The preimage of an ideal is an ideal.

def ideal.preimage (f : α → β) [is_ring_hom f] : ideal β → ideal α :=
λ J,
{ carrier := set.preimage f J.1,
  zero := by simp; by exact (is_ring_hom.map_zero f).symm ▸ J.2,
  add := λ x y Hx Hy, 
    by simp; 
    by exact (@is_ring_hom.map_add α β _ _ f _ x y).symm ▸ (ideal.add_mem J Hx Hy),
  smul := λ c x Hx,
    by simp;
    by exact (@is_ring_hom.map_mul α β _ _ f _ c x).symm ▸ (ideal.mul_mem_left J Hx), }

-- Corresponds to the preimage of f as a function.

lemma ideal.preimage_eq (f : α → β) [is_ring_hom f] (I : ideal α) (J : ideal β) :
I = ideal.preimage f J ↔ I.1 = set.preimage f J.1 :=
⟨λ HI, by rw HI; trivial, λ Hx, ideal.ext $ (set.ext_iff _ _).1 Hx⟩

-- Prime ideals are preserved by preimages.

lemma ideal.is_prime.preimage (f : α → β) [is_ring_hom f] (I : ideal β) (PI : ideal.is_prime I)
: ideal.is_prime (ideal.preimage f I) :=
begin
  constructor,
  { intros HC,
    suffices Hsuff : I = ⊤, 
      exact PI.1 Hsuff,
    rw [ideal.eq_top_iff_one, ←(is_ring_hom.map_one f)],
    show 1 ∈ set.preimage f I,
    erw ←((ideal.preimage_eq f _ _).1 HC.symm),
    trivial, },
  { intros x y Hxy,
    have Hfxy : f (x * y) ∈ I := Hxy,
    rw (is_ring_hom.map_mul f) at Hfxy,
    have Hor := PI.2 Hfxy,
    cases Hor with Hx Hy,
    { left,
      exact Hx, },
    { right,
      exact Hy, }, }
end

end ideal_preimage
