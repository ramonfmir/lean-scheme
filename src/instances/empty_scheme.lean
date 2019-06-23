import scheme 
import spectrum_of_a_ring.properties
import algebra.punit_instances

universe u 

open topological_space

local attribute [instance] classical.prop_decidable

@[reducible] def empty_presheaf : presheaf_of_rings empty :=
{ F := λ U, punit,
  res := λ U V HUV, id,
  Hid := λ U, rfl,
  Hcomp := λ U V W HWV HVU, rfl,
  Fring := by apply_instance,
  res_is_ring_hom := by apply_instance, }

@[reducible] def empty_sheaf : sheaf_of_rings empty :=
{ F := empty_presheaf, 
  locality := λ U OC s t Hs, subsingleton.elim s t,
  gluing := λ U OC si Hsi, ⟨0, λ i, by apply subsingleton.elim⟩ }

@[reducible] def empty_locally_ringed_space : locally_ringed_space empty :=
{ O := empty_sheaf, 
  Hstalks := λ x, empty.elim x, }

def empty_scheme : scheme empty :=
{ carrier := empty_locally_ringed_space, 
  Haffinecov := 
    begin 
      existsi ({ 
        γ := empty,
        Uis := λ x, empty.elim x,
        Hcov := opens.ext $ set.ext $ λ x, empty.elim x, } 
        : covering.univ empty),
      intros i,
      eapply empty.elim i,
    end }
