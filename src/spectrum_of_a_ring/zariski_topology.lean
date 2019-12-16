/-
  Kenny's proof that Spec(A) is a topological space.

  https://stacks.math.columbia.edu/tag/00E1
-/

import topology.basic
import topology.opens
import ring_theory.ideals
import group_theory.submonoid
import to_mathlib.topologcal_space
import spectrum_of_a_ring.spec
import spectrum_of_a_ring.properties

local attribute [instance] classical.prop_decidable

universe u

open topological_space

section spec_topological_space

parameters (α : Type u) [comm_ring α]

-- Proof.

lemma Spec.H1 : ∅ ∈ Spec.closeds α := 
⟨{(1:α)}, set.ext $ λ ⟨I, PI⟩, ⟨
  λ HI, false.elim $ ((ideal.ne_top_iff_one I).1 PI.1) $ by simpa [Spec.V] using HI,
  λ HI, by cases HI⟩⟩

lemma Spec.H2 : ∀ A ⊆ Spec.closeds α, ⋂₀ A ∈ Spec.closeds α := 
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

lemma Spec.H3 : ∀ A B ∈ Spec.closeds α, A ∪ B ∈ Spec.closeds α :=
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
  have HxyEAEB : x * y ∈ ideal.span EA ⊓ ideal.span EB := ⟨HxyEA, HxyEB⟩,
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
topological_space.of_closed (Spec.closeds α) Spec.H1 Spec.H2 Spec.H3

-- Useful.

lemma V_fs_closed : ∀ (f : α), is_closed (Spec.V' f) := λ f, 
⟨{f}, by simp [Spec.D', Spec.V', Spec.V]⟩

def Spec.VC : α → closeds (Spec α) := λ x, ⟨Spec.V' x, V_fs_closed x⟩

lemma D_fs_open : ∀ (f : α), is_open (Spec.D' f) := λ f, 
⟨{f}, by simp [Spec.D', Spec.V', Spec.V]⟩

def Spec.DO : α → opens (Spec α) := λ x, ⟨Spec.D' x, D_fs_open x⟩

def Spec.closed.univ : closeds (Spec α) := ⟨Spec.univ α, is_closed_univ⟩

def Spec.closed.empty : closeds (Spec α) := ⟨Spec.empty α, is_closed_empty⟩

def Spec.open.univ : topological_space.opens (Spec α) := ⟨Spec.univ α, is_open_univ⟩

def Spec.open.empty : opens (Spec α) := ⟨Spec.empty α, is_open_empty⟩

-- T0 space.

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
