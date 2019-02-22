/-
This is a section.
It contains 00DZ, 00E0, 00E1 and 00E2 and 00E3 and 00E4 and 00E5 and 00E6 and 00E7 and 00E8 and 04PM

It also contains the following useful claim, just under Lemma 10.16.2 (tag 00E0):

The sets D(f) are open and form a basis for this topology (on Spec(R))

-/

import topology.basic
import spectrum_of_a_ring.zariski_topology

universe u 

local attribute [instance] classical.prop_decidable

variables (R : Type u) [comm_ring R]

definition standard_basis  
:= {U : set (Spec R) | ∃ f : R, U = Spec.D'(f)}

lemma D_f_form_basis : 
  topological_space.is_topological_basis (standard_basis R) := 
begin
  refine topological_space.is_topological_basis_of_open_of_nhds _ _,
  { intros U HU,
    cases HU with f HUf,
    use {f},
    rw HUf,
    erw set.compl_compl,
    simp [Spec.V', Spec.V],
  },
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
