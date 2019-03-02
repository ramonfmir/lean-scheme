/-
  Standard opens form basis.

  https://stacks.math.columbia.edu/tag/04PM
-/

import topology.basic
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.properties

universe u 

local attribute [instance] classical.prop_decidable

variables (R : Type u) [comm_ring R]

definition D_fs := {U : set (Spec R) | ∃ f : R, U = Spec.D'(f)}

lemma D_fs_basis : 
  topological_space.is_topological_basis (D_fs R) := 
begin
  refine topological_space.is_topological_basis_of_open_of_nhds _ _,
  { intros U HU,
    cases HU with f HUf,
    use {f},
    rw HUf,
    erw set.compl_compl,
    simp [Spec.V', Spec.V], },
  { intros x U HxU OU,
    cases OU with E HVE,
    have HDE : U = -Spec.V E := by simp [HVE],
    have HDE' := HDE,
    rw set.ext_iff at HDE,
    replace HDE := HDE x,
    rw iff_true_left HxU at HDE,
    simp [Spec.V, has_subset.subset, set.subset] at HDE,
    rw not_forall at HDE,
    cases HDE with f Hf,
    rw not_imp at Hf,
    cases Hf with HfE Hfx,
    use Spec.D' f,
    split,
    { existsi f,
      refl, },
    { split,
      { exact Hfx, },
      { intros y Hy,
        rw HDE',
        intro HyE,
        simp [Spec.D'] at Hy,
        apply Hy,
        exact HyE HfE, } } }
end

lemma D_fs_standard_basis : 
∀ {U V}, U ∈ (D_fs R) → V ∈ (D_fs R) → U ∩ V ∈ (D_fs R) :=
begin
  intros U V HU HV,
  cases HU with fU HU,
  cases HV with fV HV,
  rw [HU, HV],
  rw ←Spec.D'.product_eq_inter,
  use [fU * fV],
end
