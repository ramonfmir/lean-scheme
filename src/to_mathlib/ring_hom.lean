/-
  A ring homomorphism is injective iff the kernel is trivial.
-/

import algebra.ring
import ring_theory.ideal_operations
import linear_algebra.basic
import to_mathlib.ideals

universes u v

variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] (f : α → β) [is_ring_hom f] 

lemma is_ring_hom.trivial_ker_def 
: ker f = ⊥ ↔ (∀ {x}, f x = 0 → x = 0) :=
begin
  split,
  { intros Hker x Hx,
    replace Hx : x ∈ ker f := Hx,
    rw Hker at Hx,
    rw ←set.mem_singleton_iff,
    exact Hx, },
  { intros Hfx,
    apply ideal.ext,
    intros x,
    split,
    { intros Hx,
      replace Hx : f x = 0 := Hx,
      erw set.mem_singleton_iff,
      exact (Hfx Hx), },
    { intros Hx,
      erw set.mem_singleton_iff at Hx,
      rw Hx,
      exact is_ring_hom.map_zero f, } },
end

lemma is_ring_hom.inj_iff_trivial_ker
: (∀ {x}, f x = 0 → x = 0) ↔ function.injective f :=
begin
  split,
  { intros H x y Hxy,
    rw [←sub_eq_zero_iff_eq, ←is_ring_hom.map_sub f] at Hxy,
    exact sub_eq_zero_iff_eq.1 (H Hxy), },
  { intros Hinj,
    intros x Hx,
    have Hfx : f x = f 0 := (is_ring_hom.map_zero f).symm ▸ Hx,
    exact Hinj Hfx, }
end

lemma is_ring_hom.inj_iff_trivial_ker'
: ker f = ⊥ ↔ function.injective f :=
iff.trans (is_ring_hom.trivial_ker_def f) (is_ring_hom.inj_iff_trivial_ker f)
