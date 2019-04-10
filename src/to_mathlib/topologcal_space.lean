/-
  Defining a topological space by giving the closeds instead of the opens.
-/

import topology.basic

universe u

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
