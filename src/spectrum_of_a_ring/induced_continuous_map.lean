/-
Lemma 10.16.4. Suppose that φ:R→R′ is a ring homomorphism. The induced map
Spec(φ):Spec(R′)⟶Spec(R),𝔭′⟼φ−1(𝔭′)
is continuous for the Zariski topologies. In fact, for any element f∈R we have Spec(φ)−1(D(f))=D(φ(f)).

Proof. It is tag 00BV that 𝔭:=φ−1(𝔭′) is indeed a prime ideal of R. The last assertion of the lemma follows directly from the definitions, and implies the first. 
-/

import Kenny_comm_alg.Zariski analysis.topology.continuity

universes u v

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
variables (f : α → β) [is_ring_hom f]

def Zariski.induced : X β → X α :=
λ p, ⟨f ⁻¹' p.1, @@is_prime_ideal.hom_preimage _ _ f _ p.1 p.2⟩

instance zariski.open := Zariski α

theorem Zariski.induced.continuous : continuous (Zariski.induced f) :=
λ A ⟨E, ha⟩, ⟨f '' E, set.ext $ λ z,
⟨λ h hz, suffices (⟨f ⁻¹' z.val, _⟩ : X α) ∈ Spec.V E, by rw ha at this; exact this hz,
   λ x hx, h ⟨x, hx, rfl⟩,
 λ h x ⟨w, H, hw⟩, have (⟨f ⁻¹' z.val, _⟩ : X α) ∈ Spec.V E, by rw ha; exact h,
   by rw ← hw; exact this H⟩⟩

theorem Zariski.induced.preimage_D (x : α) : Zariski.induced f ⁻¹' (Spec.D' x) = Spec.D' (f x) :=
set.ext $ λ z, by simp [Spec.D', Zariski.induced, Spec.V']