/-
  Definition of a scheme.

  https://stacks.math.columbia.edu/tag/01II
-/

import topology.basic
import sheaves.covering.covering
import sheaves.presheaf_of_rings_maps
import sheaves.locally_ringed_space
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.structure_sheaf

open topological_space

universes u v

open presheaf_of_rings

-- A scheme is a locally ringed space covered by affine schemes.

structure scheme (α : Type u) [topological_space α] :=
(carrier    : locally_ringed_space α)
(Haffinecov : ∃ (OC : covering.univ α), 
  ∀ i, ∃ (R : Type v) [comm_ring R] 
  (fpU : open_immersion_pullback (Spec R) carrier.O.F),
      fpU.range = OC.Uis i
    ∧ fpU.carrier ≅ structure_sheaf.presheaf R)
