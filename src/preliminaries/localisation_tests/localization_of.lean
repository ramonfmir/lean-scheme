import ring_theory.localization
import preliminaries.localisation

universe u 

open localization_alt

variables {α : Type u} [comm_ring α]
variables (S : set α) [is_submonoid S]

noncomputable lemma localization.of.is_localization_data 
: @is_localization_data α (localization α S) _ _ S _ (localization.of) _ :=
begin
  refine ⟨_, _, _⟩,
  { intros s,
    use [⟦⟨1, s⟩⟧],
    apply quotient.sound,
    use [1, is_submonoid.one_mem _],
    simp, },
  { intros x,
    have Hx := quotient.exists_rep x,
    rcases (classical.indefinite_description _ Hx) with ⟨⟨p, q⟩, Hpq⟩,
    use [⟨q, p⟩],
    rw ←Hpq,
    apply quotient.sound,
    use [1, is_submonoid.one_mem _],
    simp, },
  { intros x Hx,
    change localization.of x = 0 at Hx,
    erw quotient.eq at Hx,
    rcases Hx with ⟨s, ⟨Hs, Hx⟩⟩,
    simp at Hx,
    use [⟨⟨x, ⟨s, Hs⟩⟩, Hx⟩], }
end
