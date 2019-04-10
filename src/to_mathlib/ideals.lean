/-
  Basic constructions involving ideals.

  TODO : Check how much of this isn't actually somehwere in the mathlib.
-/

import ring_theory.ideal_operations

universes u v 

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) [is_ring_hom f]

def ideal.mk (I : set α) (J : ideal α) (H : I = J) : ideal α :=
{ carrier := I,
  zero := H.symm ▸ J.zero,
  add := H.symm ▸ J.add,
  smul := H.symm ▸ J.smul }

def ker : ideal α :=
ideal.mk {x | f x = 0} (ideal.comap f ⊥) $
set.ext $ λ x, by simp

-- If R is not the zero ring, then the zero ideal is not the whole ring.

lemma zero_ne_one_bot_ne_top : (0 : α) ≠ 1 → (⊥ : ideal α) ≠ ⊤ :=
begin
  intros Hzno,
  have Honz : (1 : α) ∉ ({0} : set α),
    intros HC,
    rw set.mem_singleton_iff at HC,
    exact Hzno HC.symm,
  intros HC,
  replace HC := (ideal.eq_top_iff_one ⊥).1 HC,
  exact (Honz HC),
end

-- Every nonzero ring has a maximal ideal.

lemma ideal.exists_maximal : (0 : α) ≠ 1 → ∃ S : ideal α, ideal.is_maximal S :=
begin
  intros Hzno,
  have HTnB : (⊥ : ideal α) ≠ ⊤ := zero_ne_one_bot_ne_top Hzno,
  rcases (ideal.exists_le_maximal ⊥ HTnB) with ⟨M, ⟨HM, HBM⟩⟩,
  exact ⟨M, HM⟩,
end
