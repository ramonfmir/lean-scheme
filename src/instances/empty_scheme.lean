import scheme 
import spectrum_of_a_ring.properties

universe u 

open topological_space

local attribute [instance] classical.prop_decidable

-- The scheme Spec((0)). I could also just treat is an affine scheme.

variables (R : Type u) [comm_ring R] (HR : subsingleton R)

lemma Spec_empty : Spec R → false := 
λ x, Spec.empty_iff_zero_ring.2 HR x

include HR

variables (X : Type u) [topological_space X] (H : X → false)

@[reducible] def empty_presheaf : presheaf_of_rings (Spec R) :=
{ F := λ U, R,
  res := λ U V HUV, id,
  Hid := λ U, rfl,
  Hcomp := λ U V W HWV HVU, rfl,
  Fring := by apply_instance,
  res_is_ring_hom := by apply_instance, }

@[reducible] def empty_sheaf : sheaf_of_rings (Spec R) :=
{ F := empty_presheaf R HR, 
  locality := λ U OC s t Hs, subsingleton.elim s t,
  gluing := λ U OC si Hsi, ⟨0, λ i, by apply subsingleton.elim⟩ }

@[reducible] def empty_locally_ringed_space : locally_ringed_space (Spec R) :=
{ O := empty_sheaf R HR, 
  Hstalks := λ x, false.elim (Spec_empty R HR x), }

def empty_scheme : scheme (Spec R) :=
{ carrier := empty_locally_ringed_space R HR, 
  cov := {
    γ := Spec R,
    Uis := λ x, false.elim (Spec_empty R HR x),
    Hcov := opens.ext $ set.ext $ λ x, false.elim (Spec_empty R HR x), }, 
  Haffinecov := λ i, false.elim (Spec_empty R HR i), }
