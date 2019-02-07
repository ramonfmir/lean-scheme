import topology.basic

universes u

open topological_space
open lattice lattice.lattice

variables {α : Type u} [topological_space α]

-- A couple of useful tricks to work avoid using the lattice jargon when 
-- dealing with opens.

instance : has_inter (opens α) :=
{ inter := λ U V, inf U V }

instance : has_union (opens α) :=
{ union := λ U V, sup U V }

prefix `⋃` := supr

-- Some useful lemmas. Maybe versions of them are already somewhere.

lemma opens_supr_mem {γ : Type u} (X : γ → opens α) 
: ∀ x i, x ∈ (X i).val → x ∈ (⋃ X).val :=
λ x i Hx, let Xi := X i in 
begin
    unfold supr; simp,
    exact ⟨Xi.1, ⟨⟨Xi.2, i, by simp⟩, Hx⟩⟩,
end
