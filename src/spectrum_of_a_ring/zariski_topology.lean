/-
  Kenny's proof that Spec(A) is a topological space.
-/

import topology.basic
import ring_theory.ideals
import group_theory.submonoid

noncomputable theory

local attribute [instance] classical.prop_decidable

universe u

-- Useful.

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

-- Definition.

def Spec := {P : ideal α // ideal.is_prime P}

def Spec.V : set α → set Spec := λ E, {P | E ⊆ P.val}

def Spec.V' : α → set Spec := λ f, {P | f ∈ P.val}

def Spec.D : set α → set Spec := λ E, -Spec.V(E)

def Spec.D' : α → set Spec := λ f, -Spec.V'(f)

def Spec.closed : set (set Spec) := {A | ∃ E, Spec.V E = A}

lemma Spec.V.set_eq_span (S : set α) : Spec.V S = Spec.V (ideal.span S) :=
set.ext $ λ ⟨I, PI⟩,
⟨λ HI x Hx,
  begin 
    have HxI := (ideal.span_mono HI) Hx, 
    rw ideal.span_eq at HxI,
    exact HxI,
  end,
 λ HI x Hx, HI (ideal.subset_span Hx)⟩

-- Proof.

lemma Spec.H1 : ∅ ∈ Spec.closed := 
⟨{(1:α)}, set.ext $ λ ⟨I, PI⟩, ⟨
  λ HI, false.elim $ @ideal.is_prime.one_not_mem _ _ I PI $ by simpa [Spec.V] using HI,
  λ HI, by cases HI⟩⟩

lemma Spec.H2 : ∀ A ⊆ Spec.closed, ⋂₀ A ∈ Spec.closed := 
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

lemma Spec.H3 : ∀ A B ∈ Spec.closed, A ∪ B ∈ Spec.closed :=
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

instance zariski_topology : topological_space Spec :=
topological_space.of_closed Spec.closed Spec.H1 Spec.H2 Spec.H3


end spec_topological_space
