/-
  Kenny's proof that Spec(A) is a topological space.
-/

import topology.basic
import ring_theory.ideals
import group_theory.submonoid
import spectrum_of_a_ring.spectrum
import spectrum_of_a_ring.properties

local attribute [instance] classical.prop_decidable

universe u

-- Useful. TODO: Move somewhere else.

lemma ideal.is_prime.one_not_mem 
{α : Type u} [comm_ring α] (S : ideal α) [P : ideal.is_prime S] : (1:α) ∉ S :=
(ideal.ne_top_iff_one S).1 P.1

def topological_space.of_closed {α : Type u} (T : set (set α))
  (H1 : ∅ ∈ T)
  (H2 : ∀ A ⊆ T, ⋂₀ A ∈ T)
  (H3 : ∀ A B ∈ T, A ∪ B ∈ T) :
  topological_space α :=
{ is_open := λ X, -X ∈ T,
  is_open_univ := by simp [H1],
  is_open_inter := λ s t hs ht, by simpa [set.compl_inter] using H3 (-s) (-t) hs ht,
  is_open_sUnion := λ s hs, 
    by rw set.compl_sUnion; exact H2 (set.compl '' s) 
    (λ z ⟨y, hy, hz⟩, by simpa [hz.symm] using hs y hy) }

instance ideal.has_inter {β : Type u} [comm_ring β] : has_inter (ideal β) :=
{ inter := λ I J, 
  { carrier := I.carrier ∩ J.carrier,
    zero := ⟨I.zero, J.zero⟩,
    add := λ x y ⟨HxI, HxJ⟩ ⟨HyI, HyJ⟩, ⟨I.add HxI HyI, J.add HxJ HyJ⟩,
    smul := λ c x ⟨HxI, HxJ⟩, ⟨I.smul c HxI, J.smul c HxJ⟩ } }

-- 

section spec_topological_space

parameters (α : Type u) [comm_ring α]

def closed_sets := @Spec.closed α _

-- Proof.

lemma Spec.H1 : ∅ ∈ closed_sets := 
⟨{(1:α)}, set.ext $ λ ⟨I, PI⟩, ⟨
  λ HI, false.elim $ @ideal.is_prime.one_not_mem _ _ I PI $ by simpa [Spec.V] using HI,
  λ HI, by cases HI⟩⟩

lemma Spec.H2 : ∀ A ⊆ closed_sets, ⋂₀ A ∈ closed_sets := 
λ A HA, ⟨(⋃₀ {E | ∃ S ∈ A, Spec.V E = S}), set.ext $ λ ⟨I, PI⟩, ⟨ 
  λ HI T HT, 
    begin
      rcases (HA HT) with ⟨S, HS⟩,
      rw ←HS,
      intros x Hx,
      apply HI,
      use [S, ⟨T, HT, HS⟩],
      exact Hx,
    end,
  λ HI x ⟨E, ⟨⟨S, HSA, HVES⟩, HxE⟩⟩, 
    begin
      have HIS := HI S HSA,
      rw ←HVES at HIS,
      exact (HIS HxE)
    end⟩⟩

lemma Spec.H3 : ∀ A B ∈ closed_sets, A ∪ B ∈ closed_sets :=
λ A B ⟨EA, HEA⟩ ⟨EB, HEB⟩, 
⟨(ideal.span EA ∩ ideal.span EB), set.ext $ λ ⟨I, PI⟩, ⟨
begin 
  intros HI,
  eapply or_iff_not_and_not.2; try { apply_instance },
  rintros ⟨HnIA, HnIB⟩,
  rw ←HEA at HnIA,
  rw ←HEB at HnIB,
  rcases not_forall.1 HnIA with ⟨x, Hx⟩,
  rcases not_forall.1 HnIB with ⟨y, Hy⟩,
  rcases not_imp.1 Hx with ⟨HxEA, HnxI⟩,
  rcases not_imp.1 Hy with ⟨HyEB, HnyI⟩,
  have HxyEA : x * y ∈ ideal.span EA,
    apply ideal.mul_mem_right _ _,
    exact ((@ideal.subset_span _ _ EA) _ HxEA),
  have HxyEB : x * y ∈ ideal.span EB,
    apply ideal.mul_mem_left _ _,
    exact ((@ideal.subset_span _ _ EB) _ HyEB),
  have HxyEAEB : x * y ∈ ideal.span EA ∩ ideal.span EB := ⟨HxyEA, HxyEB⟩,
  cases (ideal.is_prime.mem_or_mem PI (HI HxyEAEB)) with HCx HCy,
  { apply HnxI, 
    exact HCx, },
  { apply HnyI,
    exact HCy, }
end,
begin
  rintros HI x ⟨HxEA, HxEB⟩, 
  cases HI,
  { rw ←HEA at HI,
    rw Spec.V.set_eq_span at HI,
    exact HI HxEA, },
  { rw ←HEB at HI,
    rw Spec.V.set_eq_span at HI,
    exact HI HxEB, }
end⟩⟩

parameter (α)

instance zariski_topology : topological_space (Spec α) :=
topological_space.of_closed Spec.closed Spec.H1 Spec.H2 Spec.H3

section spec_t0_space

instance spec_t0 : t0_space (Spec α) :=
begin
  constructor,
  rintros ⟨I, PI⟩ ⟨J, PJ⟩ Hneq,
  simp at Hneq,
  have HIJneq : ¬ (I.carrier = J.carrier),
    intros H,
    have Hlift : ↑I = ↑J := H,
    apply Hneq,
    apply ideal.ext,
    unfold has_mem.mem,
    rw Hlift,
    simp,
  rw set.ext_iff at HIJneq,
  rw not_forall at HIJneq,
  rcases HIJneq with ⟨x, Hx⟩,
  use [Spec.D {x}],
  split,
  { use {x},
    simp [Spec.D], },
  { rw iff_def at Hx,
    rw not_and_distrib at Hx,
    repeat { rw not_imp at Hx, },
    cases Hx,
    { cases Hx with HxI HnxJ,
      right,
      split,
      { intros H,
        apply HnxJ,
        apply H,
        exact set.mem_singleton x, },
      { intros H,
        apply H,
        intros z Hz,
        rw set.mem_singleton_iff at Hz,
        rw Hz,
        exact HxI, } },
    { cases Hx with HxJ HnxI,
      left,
      split,
      { intros H,
        apply HnxI,
        apply H,
        exact set.mem_singleton x, },
      { intros H,
        apply H,
        intros z Hz,
        rw set.mem_singleton_iff at Hz,
        rw Hz,
        exact HxJ, } } }
end

end spec_t0_space

end spec_topological_space
