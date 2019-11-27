/-
  Definition of Spec(R).

  https://stacks.math.columbia.edu/tag/00DZ
-/

import topology.opens
import ring_theory.ideals

universe u

variables (R : Type u) [comm_ring R]

-- Spec(R).

def Spec := {P : ideal R // ideal.is_prime P}

variable {R}

-- General definitions.

namespace Spec

def V : set R → set (Spec R) := λ E, {P | E ⊆ P.val}

def V' : R → set (Spec R) := λ f, {P | f ∈ P.val}

def D : set R → set (Spec R) := λ E, -V(E)

def D' : R → set (Spec R) := λ f, -V'(f)

variable (R)

def univ := @set.univ (Spec R)

def empty := (∅ : set (Spec R))

def opens : set (set (Spec R)) := {A | ∃ U, D U = A}

def closeds : set (set (Spec R)) := {A | ∃ E, Spec.V E = A}

end Spec
