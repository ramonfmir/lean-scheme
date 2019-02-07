import topology.basic
import preliminaries.opens

universes u 

open topological_space lattice
section covering

parameters {α : Type u} [topological_space α]

-- Open cover.

structure covering (U : opens α) := 
{γ    : Type u}
(Uis  : γ → opens α)
(Hcov : ⋃ Uis = U)

-- If ⋃ Ui = U then for all i, Ui ⊆ U.

lemma subset_cover {U : opens α} {OC : covering U} : 
∀ i, OC.Uis i ⊆ U := 
λ i x Hx, let Ui := OC.Uis i in OC.Hcov ▸ 
begin
    unfold supr, 
    simp,
    exact ⟨Ui.1, ⟨⟨Ui.2, i, by simp⟩, Hx⟩⟩,
end

end covering
