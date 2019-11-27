import ring_theory.localization
import to_mathlib.localization.localization_alt
import to_mathlib.localization.localization_of
import spectrum_of_a_ring.properties
import sheaves.presheaf_of_rings_on_basis
import sheaves.sheaf_of_rings_on_standard_basis
import sheaves.locally_ringed_space
import spectrum_of_a_ring.spec
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.standard_basis

universe u

local attribute [instance] classical.prop_decidable


variables {R : Type u} [comm_ring R]

open topological_space
open classical
open localization
open localization_alt

-- Define S(U) so that R[1/f] ≃ R[1/S(D(f))].

open Spec

def S (U : opens (Spec R)) : set R := { r : R | U.1 ⊆ D'(r) }

instance S.is_submonoid (U : opens (Spec R)) : is_submonoid (S U) :=
{ one_mem := λ ⟨P, PI⟩ HP, ((ideal.ne_top_iff_one P).1 PI.1),
  mul_mem := λ f g Hf Hg,
    begin
      show U.1 ⊆ Spec.D'(f*g),
      exact (Spec.D'.product_eq_inter f g).symm ▸ set.subset_inter Hf Hg,
    end, }

lemma S.rev_mono {U V : opens (Spec R)} (HVU : V ⊆ U) : S U ⊆ S V :=
λ x Hx, set.subset.trans HVU Hx

lemma S.f_mem (f : R) : f ∈ S (Spec.DO R (f)) := set.subset.refl _

lemma S.inter_subset_Sinter (U V : opens (Spec R)) : (S U) ∩ (S V) ⊆ S (U ∩ V) :=
begin
  rintros x ⟨HxU, HxV⟩,
  change U ⊆ Spec.DO R (x) at HxU,
  change V ⊆ Spec.DO R (x) at HxV,
  have H := set.inter_subset_inter HxU HxV,
  rw set.inter_self at H,
  exact H,
end

-- Structure presheaf on Spec(R) defined on the basis by the rule ℱ(U) = R[1/S(U)].

variable (R)

def structure_presheaf_on_basis : presheaf_of_rings_on_basis (Spec R) (D_fs_basis R) := 
{ F := λ U BU, localization R (S U),
  res := λ U V BU BV HVU,
    begin
      have H := S.rev_mono HVU,
      apply quotient.lift (λ (x : R × (S U)), ⟦(x.1, (⟨x.2.1, H x.2.2⟩ : S V))⟧),
      { rintros ⟨a1, b1, Hb1⟩ ⟨a2, b2, Hb2⟩ ⟨t, Ht, Habt⟩; simp,
        use [t, H Ht, Habt], },
    end,
  Hid := λ U BU, funext $ λ x, quotient.induction_on x $ λ a, by simp,
  Hcomp := λ U V W BU BV BW HWV HVU, funext $ λ x, quotient.induction_on x $ λ a, by simp,
  Fring := λ U BU, by apply_instance,
  res_is_ring_hom := λ U V BU BV HVU,
      { map_one := rfl,
        map_add := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl,
        map_mul := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl, }, }
