/-
  Induced map from Spec(B) to Spec(A).

  https://stacks.math.columbia.edu/tag/00E2
-/

import topology.continuity
import algebra.ring
import spectrum_of_a_ring.zariski_topology

open lattice

universes u v

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f]

section preliminaries

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

end preliminaries

-- This is the core of this file.

-- Map given φ : A → B, we have Spec(φ) : Spec(B) → Spec(A) s.t. 𝔭′⟼φ−1(𝔭′).

@[reducible] def Zariski.induced : Spec β → Spec α :=
λ ⟨I, PI⟩, ⟨ideal.preimage f I, ideal.is_prime.preimage f I PI⟩

-- This induced map is continuous.

theorem Zariski.induced.continuous : continuous (Zariski.induced f) :=
begin 
  rintros U ⟨E, HE⟩,
  use [f '' E],
  apply set.ext,
  rintros ⟨I, PI⟩,
  split,
  { intros HI HC,
    suffices HfI : Zariski.induced f ⟨I, PI⟩ ∈ Spec.V E,
      rw HE at HfI,
      apply HfI,
      exact HC, 
    intros x Hx,
    simp [Zariski.induced] at *,
    show f x ∈ I,
    have HfE : f '' E ⊆ I := HI,
    have Hfx : f x ∈ f '' E := set.mem_image_of_mem f Hx,
    exact (HfE Hfx), },
  { rintros HI x ⟨y, ⟨Hy, Hfy⟩⟩,
    suffices HfI : Zariski.induced f ⟨I, PI⟩ ∈ Spec.V E, 
      rw ←Hfy,
      exact (HfI Hy),
    intros z Hz,
    simp [Zariski.induced] at *,
    replace HI : _ ∈ -U := HI,
    rw ←HE at HI,
    exact (HI Hz), }
end 
