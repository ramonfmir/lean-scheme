/-
  Induced map from Spec(B) to Spec(A).

  https://stacks.math.columbia.edu/tag/00E2
-/

import topology.basic
import ring_theory.ideal_operations
import spectrum_of_a_ring.zariski_topology

open lattice

universes u v

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f]

-- Given φ : A → B, we have Spec(φ) : Spec(B) → Spec(A), 𝔭′⟼φ⁻¹(𝔭′).

def Zariski.induced : Spec β → Spec α :=
λ ⟨P, HP⟩, ⟨ideal.comap f P, @ideal.is_prime.comap _ _ _ _ f _ P HP⟩

-- This induced map is continuous.

lemma Zariski.induced.continuous : continuous (Zariski.induced f) :=
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

theorem Zariski.induced.preimage_D (x : α) 
: Zariski.induced f ⁻¹' (Spec.D' x) = Spec.D' (f x) :=
set.ext $ λ ⟨P, HP⟩, 
by simp [Spec.D', Spec.V', Zariski.induced]
