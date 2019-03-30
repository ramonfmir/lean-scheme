import topology.basic
import preliminaries.covering
import sheaves.presheaf_of_rings_maps
import sheaves.locally_ringed_space
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.structure_presheaf

open topological_space

universes u

open presheaf_of_rings

structure scheme (α : Type u) [topological_space α] :=
(carrier    : locally_ringed_space α)
(cov        : covering.univ α)
(Haffinecov : 
  ∀ i, ∃ (R) [comm_ring R] (fpU : pullback carrier.O.F),
      fpU.range = cov.Uis i
    ∧ fpU.carrier ≅ structure_presheaf R)
