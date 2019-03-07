import sheaves.locally_ringed_space

universe u 

structure scheme (X : Type u) [topological_space X] :=
(carrier : locally_ringed_space X)
(Hcov    : ∀ x, ∃ U, x ∈ U ∧ ∃ R, comm_ring R)
