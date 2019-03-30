import topology.basic
import sheaves.presheaf_of_rings_maps
import sheaves.locally_ringed_space
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.structure_presheaf

open topological_space

universes u

structure scheme (α : Type u) [topological_space α] :=
(carrier    : locally_ringed_space α)
(Haffinecov : 
  ∀ x, ∃ (U : opens α), 
      x ∈ U 
    ∧ ∃ (R) [comm_ring R] (fpU : presheaf_of_rings.pullback carrier.O.F),
      fpU.carrier ≅ structure_presheaf R)
