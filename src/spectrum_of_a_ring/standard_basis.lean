/-
  Standard opens form basis.

  https://stacks.math.columbia.edu/tag/04PM
-/

import topology.basic
import preliminaries.opens
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.properties

universe u 

open topological_space

local attribute [instance] classical.prop_decidable

section standard_basis

parameters (R : Type u) [comm_ring R]

definition D_fs := {U : opens (Spec R) | ∃ f : R, U.1 = Spec.D'(f)}

lemma D_fs_basis : opens.is_basis D_fs := 
begin
  refine topological_space.is_topological_basis_of_open_of_nhds _ _,
  { intros U HU,
    rcases HU with ⟨OU, HOU, HOUval⟩,
    rw ←HOUval,
    exact OU.2, },
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
    have HDfDfs : Spec.D' f ∈ subtype.val '' D_fs,
      simp,
      use [D_fs_open R f, f],
    use HDfDfs,
    split,
    { exact Hfx, },
    { intros y Hy,
      rw HDE',
      intro HyE,
      simp [Spec.D'] at Hy,
      apply Hy,
      exact HyE HfE, } }
end

lemma D_fs_standard_basis : 
∀ {U V}, U ∈ D_fs → V ∈ D_fs → U ∩ V ∈ D_fs :=
begin
  intros U V HU HV,
  cases HU with fU HU,
  cases HV with fV HV,
  use [fU * fV],
  simp [opens.inter],
  rw [HU, HV, ←Spec.D'.product_eq_inter],
end

end standard_basis
