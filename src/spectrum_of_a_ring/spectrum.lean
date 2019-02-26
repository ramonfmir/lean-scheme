import ring_theory.ideals

universe u

section spectrum

parameters (α : Type u) [comm_ring α]

-- Definition of Spec(R).

def Spec := {P : ideal α // ideal.is_prime P}

parameter {α}

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

 end spectrum
