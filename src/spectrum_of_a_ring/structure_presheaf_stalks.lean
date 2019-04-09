import ring_theory.ideals
import ring_theory.localization
import preliminaries.localisation
import sheaves.stalk_of_rings_on_standard_basis
import spectrum_of_a_ring.structure_presheaf
import spectrum_of_a_ring.structure_presheaf_localization
import spectrum_of_a_ring.structure_presheaf_res

universe u

variables {R : Type u} [comm_ring R]
variables (P : Spec R)

open localization localization_alt stalk_of_rings_on_standard_basis
open classical

def Bstd := D_fs_standard_basis R

def F := structure_presheaf_on_basis R

def FP := stalk_of_rings_on_standard_basis Bstd F P

def φ : R → FP P := λ x, 
⟦{ U := opens.univ,
   BU := (D_fs_standard_basis R).1,
   Hx := set.mem_univ P,
   s := (of : R → localization R (S (opens.univ))) x, }⟧

-----

instance FP.is_comm_ring : comm_ring (FP P) :=
by simp [FP]; by apply_instance

instance prime.is_submonoid : is_submonoid (-P.1 : set R) :=
{ one_mem := P.1.ne_top_iff_one.1 P.2.1,
  mul_mem := λ x y hnx hny hxy, or.cases_on (P.2.2 hxy) hnx hny }

instance φP.is_ring_hom : is_ring_hom (φ P) :=
{ map_one := rfl,
  map_mul := λ x y, 
    begin
      apply quotient.sound,
      use [opens.univ, (D_fs_standard_basis R).1, set.mem_univ P],
      use [set.subset.refl _, (λ x Hx, ⟨Hx, Hx⟩)],
      rw (F.res_is_ring_hom _ _ _).map_mul,
      rw ←presheaf_on_basis.Hcomp',
      rw ←presheaf_on_basis.Hcomp',
      rw of.is_ring_hom.map_mul,
      rw (F.res_is_ring_hom _ _ _).map_mul,
    end,
  map_add := λ x y,
    begin
      apply quotient.sound,
      use [opens.univ, (D_fs_standard_basis R).1, set.mem_univ P],
      use [set.subset.refl _, (λ x Hx, ⟨Hx, Hx⟩)],
      rw (F.res_is_ring_hom _ _ _).map_add,
      rw ←presheaf_on_basis.Hcomp',
      rw ←presheaf_on_basis.Hcomp',
      rw of.is_ring_hom.map_add,
      rw (F.res_is_ring_hom _ _ _).map_add,
    end, }

-----

lemma stalk_local.inverts : inverts_data (-P.1 : set R) (φ P) :=
begin
  rintros ⟨s, Hs⟩,
  change s ∉ P.val at Hs,
  let BDs := D_fs.mem R s, 
  have HsS : s ∈ S (Spec.DO R s) := S.f_mem s,
  let sinv : FP P := 
    ⟦{ U := Spec.DO R s,
       BU := BDs,
       Hx := Hs,
       s := ⟦⟨1, ⟨s, HsS⟩⟩⟧, }⟧,
  use sinv,
  apply quotient.sound,
  use [Spec.DO R s, BDs, Hs, (λ x Hx, ⟨trivial, Hx⟩), set.subset_univ _],
  simp,
  erw (F.res_is_ring_hom _ _ _).map_mul,
  erw (F.res_is_ring_hom _ _ _).map_one,
  iterate 2 { rw ←presheaf_on_basis.Hcomp', },
  erw presheaf_on_basis.Hid',
  erw structure_presheaf_on_basis.res_eq,
  erw ←structure_presheaf_on_basis.res_comp_of',
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp,
end

lemma stalk_local.has_denom : has_denom_data (-P.1 : set R) (φ P) :=
begin
  sorry,
end

lemma stalk_local.ker_le : ker (φ P) ≤ submonoid_ann (-P.1 : set R) :=
begin
  sorry,
end

lemma stalk_local : is_localization_data (-P.1 : set R) (φ P) :=
{ inverts := stalk_local.inverts P, 
  has_denom := stalk_local.has_denom P, 
  ker_le := stalk_local.ker_le P, }

