/-
  Definition of Spec(R).

  https://stacks.math.columbia.edu/tag/00DZ
-/

import ring_theory.ideals

universe u

section spectrum

parameters (α : Type u) [comm_ring α]

def Spec := {P : ideal α // ideal.is_prime P}

parameter {α}

def Spec.V : set α → set Spec := λ E, {P | E ⊆ P.val}

def Spec.V' : α → set Spec := λ f, {P | f ∈ P.val}

def Spec.D : set α → set Spec := λ E, -Spec.V(E)

def Spec.D' : α → set Spec := λ f, -Spec.V'(f)

parameter (α)

def Spec.univ := @set.univ Spec

def Spec.empty := (∅ : set Spec)

def Spec.closed : set (set Spec) := {A | ∃ E, Spec.V E = A}

def Spec.open : set (set Spec) := {A | ∃ U, Spec.D U = A}

end spectrum
