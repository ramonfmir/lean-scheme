import scheme 
import spectrum_of_a_ring.properties

universe u 

open topological_space

local attribute [instance] classical.prop_decidable

-- The scheme Spec((0)).

variables (R : Type u) [comm_ring R] [subsingleton R]

@[reducible] def empty_presheaf : presheaf_of_rings (Spec R) :=
{ F := λ U, R,
  res := λ U V HUV, id,
  Hid := λ U, rfl,
  Hcomp := λ U V W HWV HVU, rfl,
  Fring := by apply_instance,
  res_is_ring_hom := by apply_instance, }

@[reducible] def empty_sheaf : sheaf_of_rings (Spec R) :=
{ F := empty_presheaf R, 
  locality := λ U OC s t Hs, subsingleton.elim s t,
  gluing := λ U OC si Hsi, ⟨0, λ i, by apply subsingleton.elim⟩ }

@[reducible] def empty_locally_ringed_space : locally_ringed_space (Spec R) :=
{ O := empty_sheaf R, 
  Hstalks := λ x, false.elim (Spec.empty_iff_zero_ring.2 (by apply_instance) x), }

open presheaf_of_rings

-- def empty_pullback : @pullback (Spec R) _ (Spec R) _ (empty_presheaf R) :=
-- { φ := id,
--   Hcts := continuous_id,
--   Hφ := λ U, 
--     begin
--       use {0},
--       apply set.ext,
--       intros x,
--       exact false.elim (Spec.empty_iff_zero_ring.2 (by apply_instance) x),
--     end }

-- def empty_scheme : scheme (Spec R) :=
-- { carrier := empty_locally_ringed_space R, 
--   cov := {
--     Uis := λ x, x,
--     Hcov := opens.ext $ set.ext $ 
--       λ x, false.elim (Spec.empty_iff_zero_ring.2 (by apply_instance) x), }, 
--   Haffinecov := 
--     begin
--       intros i,
--       sorry,
--     end, }
