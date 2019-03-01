import topology.basic

universes u

open topological_space lattice lattice.lattice

section opens

variables {α : Type u} [topological_space α]

-- A couple of useful tricks to work avoid using the lattice jargon when 
-- dealing with opens.

instance : has_inter (opens α) :=
{ inter := λ U V, inf U V }

instance : has_union (opens α) :=
{ union := λ U V, sup U V }

prefix `⋃` := supr

-- Opens constants.

def opens.univ : opens α := ⟨set.univ, is_open_univ⟩

def opens.empty : opens α := ⟨∅, is_open_empty⟩

-- Some useful lemmas. Maybe versions of them are already somewhere.

lemma opens_supr_mem {γ : Type u} (X : γ → opens α) 
: ∀ i x, x ∈ (X i).val → x ∈ (⋃ X).val :=
λ i x Hx, let Xi := X i in 
begin
    unfold supr; simp,
    exact ⟨Xi.1, ⟨⟨Xi.2, i, by simp⟩, Hx⟩⟩,
end

lemma opens_supr_subset {γ : Type u} (X : γ → opens α) 
: ∀ i, X i ⊆ ⋃ X :=
λ i x, opens_supr_mem X i x

end opens
