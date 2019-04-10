import spectrum_of_a_ring.structure_sheaf
import spectrum_of_a_ring.strucutre_sheaf_stalks

universe u

variables (R : Type u) [comm_ring R]

def Spec.locally_ringeed_space : locally_ringed_space (Spec R) :=
{ O := structure_sheaf R, 
  Hstalks := λ P, structure_sheaf.stalk_local P, }
