/-
if R is a ring and S is a multiplicative subset of R then S−1R is the zero ring if and only if S contains 0, 

[proof omitted]
-/

import ring_theory.localization group_theory.submonoid

universe u

variables {α : Type u} [comm_ring α] (S : set α) [is_submonoid S]

theorem localization.subsingleton_iff_zero_mem : subsingleton (localization.loc α S) ↔ (0:α) ∈ S :=
⟨λ ⟨h⟩, let ⟨w, H, hw⟩ := quotient.exact (h 0 1) in by simp at hw; rwa hw at H,
 λ h, ⟨λ x y, quotient.induction_on₂ x y $ λ ⟨m₁, m₂, hm⟩ ⟨n₁, n₂, hn⟩, quotient.sound $ ⟨0, h, by simp⟩⟩⟩