/-
  Same as covering but the Ui's are elements of the basis and such that Ui ∩ Uj
  (not necessarily in the basis) is covered by Uijk's all in the basis.
-/

import topology.basic
import to_mathlib.opens
import sheaves.covering.covering

universes u v

open topological_space lattice

section covering_on_basis

parameters {α : Type u} [topological_space α]
parameters {B : set (opens α)} [HB : opens.is_basis B]

-- Open cover for basis.

structure covering_basis (U : opens α) extends covering U :=
{Iij       : γ → γ → Type v }
(Uijks     : Π (i j), Iij i j → opens α)
(BUis      : ∀ i, Uis i ∈ B)
(BUijks    : ∀ i j k, Uijks i j k ∈ B)
(Hintercov : ∀ i j, ⋃ (Uijks i j) = Uis i ∩ Uis j)

-- If ⋃ Uijk = Ui ∩ Uj then for all k, Uijk ⊆ Ui ∩ Uj.

lemma subset_covering_basis {U : opens α} {OC : covering_basis U}
: ∀ i j k, OC.Uijks i j k ⊆ OC.Uis i ∩ OC.Uis j := 
λ i j k x, (OC.Hintercov i j) ▸ opens_supr_mem (OC.Uijks i j) k x

-- If ⋃ Uijk = Ui ∩ Uj then for all k, Uijk ⊆ Ui.

lemma subset_covering_basis_inter_left {U : opens α} {OC : covering_basis U}
: ∀ i j k, OC.Uijks i j k ⊆ OC.Uis i :=
λ i j k, set.subset.trans (subset_covering_basis i j k) (set.inter_subset_left _ _) 

-- If ⋃ Uijk = Ui ∩ Uj then for all k, Uijk ⊆ Uj.

lemma subset_covering_basis_inter_right {U : opens α} {OC : covering_basis U}
: ∀ i j k, OC.Uijks i j k ⊆ OC.Uis j :=
λ i j k, set.subset.trans (subset_covering_basis i j k) (set.inter_subset_right _ _) 

end covering_on_basis
