import sheaves.locally_ringed_space
import instances.affine_scheme

universes u v w

section opens_comap

open topological_space lattice lattice.lattice

variables {α : Type u} [topological_space α]
variables {β : Type v} [topological_space β]
variables {f : α → β} (Hf : continuous f) 

@[mono] theorem opens.comap_mono' (U V : opens β) (HUV : U ≤ V) : opens.comap Hf U ≤ opens.comap Hf V := 
set.preimage_mono HUV

@[simp] lemma opens.comap_top : opens.comap Hf ⊤ = ⊤ := 
opens.ext set.preimage_univ

end opens_comap

instance presheaf_of_rings.comm_ring {α : Type u} [topological_space α]
  (f : presheaf_of_rings α) (U : topological_space.opens α) : comm_ring (f U) := f.Fring U

instance sheaf_of_rings.comm_ring {α : Type u} [topological_space α]
  (f : sheaf_of_rings α) (U : topological_space.opens α) : comm_ring (f U) := f.F.Fring U

attribute [instance] to_stalk.is_ring_hom
attribute [instance] locally_ringed_space.Hstalks
attribute [irreducible] sheaf_on_standard_basis.is_sheaf_on_standard_basis

def to_Spec_top (R : Type v) [comm_ring R] : R → (Spec.locally_ringed_space R).O ⊤ :=
to_presheaf_of_rings_extension (D_fs_standard_basis R) (structure_presheaf_on_basis R) (D_fs_standard_basis R).1 ∘ localization.of

instance (R : Type v) [comm_ring R] : is_ring_hom (to_Spec_top R) :=
@@is_ring_hom.comp _ _ _ _ _ _ $ to_presheaf_of_rings_extension.is_ring_hom _ _ structure_presheaf_on_basis_is_sheaf_on_basis _

instance is_maximal_nonunits_ideal {R : Type v} [comm_ring R] (h : is_local_ring R) : (nonunits_ideal h).is_maximal :=
ideal.is_maximal_iff.2 ⟨one_not_mem_nonunits, λ J x hJ hx hxJ, J.eq_top_iff_one.1 $ J.eq_top_of_is_unit_mem hxJ $
  classical.by_contradiction $ hx ∘ mem_nonunits_iff.2⟩

namespace locally_ringed_space

variables {X : Type u} [topological_space X] (OX : locally_ringed_space X)

def D (f : OX.O ⊤) : set X := { x | is_unit (to_stalk OX.O.F x ⊤ trivial f) }

theorem is_open_D (f : OX.O ⊤) : is_open (OX.D f) :=
begin
  refine is_open_iff_forall_mem_open.2 (λ x hxf, _),
  cases is_unit_iff_exists_inv.1 hxf with y hxy,
  refine quotient.induction_on y (λ g hfg, _) hxy,
  cases g with U hxU g, rcases quotient.exact hfg with ⟨V, hxV, HVU', HVtop, hfgV⟩,
  exact ⟨V, λ y hyV, is_unit_iff_exists_inv.2 ⟨to_stalk ((OX.O).F) y U (HVU' hyV).2 g, quotient.sound ⟨V, hyV, HVU', HVtop, hfgV⟩⟩, V.2, hxV⟩
end

end locally_ringed_space

/- https://stacks.math.columbia.edu/tag/01I1 -/
def mor_to_hom {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type v) [comm_ring R]
  (f : morphism OX (Spec.locally_ringed_space R)) :
  (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤ :=
cast (congr_arg OX.O.F $ opens.comap_top f.Hf) ∘ f.fO.map ⊤

def induced {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type v) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f]
  (x : X) : Spec R :=
⟨ideal.comap (to_stalk OX.O.F x ⊤ trivial ∘ f ∘ to_Spec_top R) (nonunits_ideal $ OX.Hstalks x),
@ideal.is_prime.comap _ _ _ _ _ _ _ $ (is_maximal_nonunits_ideal _).is_prime⟩

@[simp] lemma Spec.DO.val (R : Type v) [comm_ring R] (f : R) : (Spec.DO R f).val = Spec.D' f :=
congr_fun (Spec.DO.val_eq_D' R) f

@[simp] lemma induced_preimage_D' {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type v) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f] (g : R) :
  induced OX R f ⁻¹' Spec.D' g = OX.D (f $ to_Spec_top R g) :=
set.ext $ λ x, classical.not_not

/- https://stacks.math.columbia.edu/tag/01I1 -/
def hom_to_mor {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type v) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f] :
  morphism OX (Spec.locally_ringed_space R) :=
{ f := induced OX R f,
  Hf := λ U HU, let ⟨Us, HUs, HUUs⟩ := topological_space.sUnion_basis_of_is_open (D_fs_basis R) HU in
        by rw [HUUs, set.preimage_sUnion]; exact is_open_Union (λ S, is_open_Union $ λ HSUs,
        let ⟨p, ⟨g, hp⟩, hpS⟩ := HUs HSUs in by rw [← hpS, hp, Spec.DO.val, induced_preimage_D']; exact OX.is_open_D _),
  fO :=
  { map := λ U f, sorry,
    commutes := sorry } }
