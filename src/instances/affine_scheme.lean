/-
  An affine scheme is a scheme.
-/

import topology.opens
import spectrum_of_a_ring.spec_locally_ringed_space
import scheme

universe u 

noncomputable theory

open topological_space

variables (R : Type u) [comm_ring R]

-- Spec(R) is a locally ringed space and it covers itself.

def affine_scheme : scheme (Spec R) :=
{ carrier := Spec.locally_ringed_space R,
  Haffinecov := 
    begin
      existsi ({ 
        γ := punit,
        Uis := λ x, opens.univ,
        Hcov := opens.ext $ set.ext $ λ x, 
        ⟨λ Hx, trivial, λ Hx, ⟨set.univ, ⟨⟨opens.univ, ⟨⟨punit.star, rfl⟩, rfl⟩⟩, Hx⟩⟩⟩ }
        : covering.univ (Spec R)),
      intros i,
      use [R, by apply_instance], 
      use [presheaf_of_rings.pullback_id (structure_sheaf.presheaf R)],
      split,
      { dsimp [presheaf_of_rings.pullback_id],
        apply opens.ext; dsimp,
        rw set.image_id,
        refl, },
      { exact presheaf_of_rings.pullback_id.iso (structure_sheaf.presheaf R), }
    end }
