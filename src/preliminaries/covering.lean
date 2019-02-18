import topology.basic
import preliminaries.opens

universes u 

open topological_space lattice

section covering

variables {α : Type u} [topological_space α]

-- Open cover.

structure covering (U : opens α) := 
{γ    : Type u}
(Uis  : γ → opens α)
(Hcov : ⋃ Uis = U)

-- If ⋃ Ui = U then for all i, Ui ⊆ U.

lemma subset_covering {U : opens α} {OC : covering U} : 
∀ i, OC.Uis i ⊆ U := 
λ i x Hx, OC.Hcov ▸ opens_supr_mem OC.Uis i x Hx

end covering
