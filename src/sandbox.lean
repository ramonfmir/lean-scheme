import sheaves.locally_ringed_space
import instances.affine_scheme

universes u v w

theorem is_unit.map {α : Type u} [monoid α] {β : Type v} [monoid β]
  (f : α → β) [is_monoid_hom f] {x : α} (hx : is_unit x) : is_unit (f x) :=
let ⟨y, hxy⟩ := hx in ⟨y.map f, by rw [units.coe_map, hxy]⟩

theorem is_unit.map' {α : Type u} [monoid α] {β : Type v} [monoid β] {y : β}
  (f : α → β) [is_monoid_hom f] (x : α) (hx : is_unit x) (hxy : f x = y) : is_unit y :=
hxy ▸ hx.map f

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

namespace topological_space

namespace opens

variables {X : Type u} [topological_space X] {B : set (opens X)} (HB : is_basis B)

def covering_of_is_basis (U : opens X) : covering U :=
⟨λ V : { V : opens X // V ∈ B ∧ V ⊆ U }, V,
opens.ext $ set.subset.antisymm (set.sUnion_subset $ λ s ⟨t, ⟨V, hVt⟩, hts⟩, hts ▸ hVt ▸ V.2.2) $
let ⟨S, HSB, HUS⟩ := is_basis_iff_cover.1 HB U in HUS.symm ▸ set.sUnion_subset (λ s ⟨V, HVS, HVs⟩, HVs ▸ set.subset_sUnion_of_mem
  ⟨V, ⟨⟨V, HSB HVS, set.subset_sUnion_of_mem ⟨V, HVS, rfl⟩⟩, rfl⟩, rfl⟩)⟩

variables (B)
def of_is_basis (U : opens X) (i : U) : opens X :=
⟨@classical.epsilon (opens X) ⟨⊥⟩ (λ V, i.1 ∈ V ∧ V ∈ B ∧ V ⊆ U), subtype.property _⟩
variables {B}

theorem of_is_basis_spec {U : opens X} {i : U} : i.1 ∈ of_is_basis B U i ∧ of_is_basis B U i ∈ B ∧ of_is_basis B U i ⊆ U :=
have ∀ i : U, ∃ V : opens X, i.1 ∈ V ∧ V ∈ B ∧ V ⊆ U,
from let ⟨S, HSB, HUS⟩ := is_basis_iff_cover.1 HB U in HUS.symm ▸ λ i,
  let ⟨t, ⟨V, HVS, rfl⟩, hiV⟩ := set.mem_sUnion.1 i.2 in ⟨V, hiV, HSB HVS, set.subset_sUnion_of_mem ⟨V, HVS, rfl⟩⟩,
by rw [of_is_basis, subtype.coe_eta]; exact classical.epsilon_spec (this i)

theorem mem_of_is_basis {U : opens X} {i : U} : i.1 ∈ of_is_basis B U i :=
(of_is_basis_spec HB).1

theorem of_is_basis_mem_basis {U : opens X} {i : U} : of_is_basis B U i ∈ B:=
(of_is_basis_spec HB).2.1

theorem of_is_basis_subset {U : opens X} {i : U} : of_is_basis B U i ⊆ U :=
(of_is_basis_spec HB).2.2

def covering_of_is_basis' (U : opens X) : covering U :=
⟨λ i : U, of_is_basis B U i,
opens.ext $ set.subset.antisymm (set.sUnion_subset $ λ s ⟨t, ⟨i, hit⟩, hts⟩, hts ▸ hit ▸ (of_is_basis_subset HB)) $
λ i hiu, set.mem_sUnion.2 ⟨of_is_basis B U ⟨i, hiu⟩, set.mem_image_of_mem _ $ set.mem_range_self _, mem_of_is_basis HB⟩⟩

def covering_of_opens (U : opens X) (f : Π i : U, opens X) (hf : ∀ i : U, i.1 ∈ f i) : covering U :=
⟨λ i, f i ∩ U,
opens.ext $ set.subset.antisymm (set.sUnion_subset $ λ s ⟨t, ⟨i, hit⟩, hts⟩, hts ▸ hit ▸ set.inter_subset_right (f i) U) $
λ i hiu, set.mem_sUnion.2 ⟨f ⟨i, hiu⟩ ∩ U, set.mem_image_of_mem _ $ set.mem_range_self _, hf ⟨i, hiu⟩, hiu⟩⟩

def covering_comap {Y : Type u} [topological_space Y] {f : X → Y} (Hf : continuous f)
  (V : opens Y) (OC : covering V) : covering (opens.comap Hf V) :=
{ γ := OC.γ,
  Uis := λ i, opens.comap Hf (OC.Uis i),
  Hcov := opens.ext $ set.subset.antisymm (set.sUnion_subset $ λ t ⟨U, ⟨V, hVU⟩, hUt⟩, hUt ▸ hVU ▸ set.preimage_mono (subset_covering V)) $
    λ i hi, let ⟨V, ⟨U, ⟨j, hjU⟩, hUV⟩, hfiV⟩ := set.mem_sUnion.1 (((set.ext_iff _ _).1 (congr_arg subtype.val OC.Hcov) (f i)).2 hi) in
    set.mem_sUnion.2 ⟨f ⁻¹' V, ⟨opens.comap Hf ⟨V, hUV ▸ U.2⟩, ⟨j, congr_arg (opens.comap Hf) $ hjU.trans $ by exact subtype.eq hUV⟩, rfl⟩, hfiV⟩ }

def covering_res (U V : opens X) (HVU : V ⊆ U) (OC : covering U) : covering V :=
{ γ := OC.γ,
  Uis := λ i : OC.γ, OC.Uis i ∩ V,
  Hcov := opens.ext $ set.subset.antisymm (set.sUnion_subset $ λ t ⟨W, ⟨i, hiVW⟩, hWt⟩, hWt ▸ hiVW ▸ set.inter_subset_right _ _) $
    λ x hxV, let ⟨t, ⟨W, ⟨i, hiW⟩, HWt⟩, hxt⟩ := set.mem_sUnion.1 (((set.ext_iff _ _).1 (congr_arg subtype.val OC.Hcov) x).2 (HVU hxV)) in
    set.mem_sUnion.2 ⟨t ∩ V, ⟨(W ∩ V : opens X), ⟨i, hiW ▸ rfl⟩, HWt ▸ rfl⟩, hxt, hxV⟩ }

namespace is_basis

variables {Y : Type w} [topological_space Y] {f : Y → X} (hf : continuous f)

/-lemma comap : is_basis (opens.comap hf '' B) :=
is_basis_iff_nbhd.2 $ λ U y hyU, let _ := is_basis_iff_nbhd.1 HB in _-/

end is_basis

end opens

end topological_space

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

def D' (f : OX.O ⊤) : set X := { x | is_unit (to_stalk OX.O.F x ⊤ trivial f) }

theorem is_open_D' (f : OX.O ⊤) : is_open (OX.D' f) :=
begin
  refine is_open_iff_forall_mem_open.2 (λ x hxf, _),
  cases is_unit_iff_exists_inv.1 hxf with y hxy,
  refine quotient.induction_on y (λ g hfg, _) hxy,
  cases g with U hxU g, rcases quotient.exact hfg with ⟨V, hxV, HVU', HVtop, hfgV⟩,
  exact ⟨V, λ y hyV, is_unit_iff_exists_inv.2 ⟨to_stalk ((OX.O).F) y U (HVU' hyV).2 g, quotient.sound ⟨V, hyV, HVU', HVtop, hfgV⟩⟩, V.2, hxV⟩
end

def D (f : OX.O ⊤) : topological_space.opens X :=
⟨OX.D' f, OX.is_open_D' f⟩

theorem is_unit_res_D (f : OX.O ⊤) : is_unit (OX.O.F.res ⊤ (OX.D f) (set.subset_univ _) f) :=
begin
  rw is_unit_iff_exists_inv,
  have : ∀ i : OX.D f, ∃ U : topological_space.opens X, ∃ H : i.1 ∈ U, ∃ g : OX.O U, OX.O.F.res ⊤ U (set.subset_univ U.1) f * g = 1,
  { refine λ ⟨i, hi⟩, exists.elim (is_unit_iff_exists_inv.1 hi) (λ gq, quotient.induction_on gq $
      λ ⟨U, hiU, g⟩ H, let ⟨V, hiV, HVU, HVtop, hfgV⟩ := quotient.exact H in
      ⟨V, hiV, OX.O.F.res U V (λ j hjv, (HVU hjv).2) g,
      begin
        dsimp only at hfgV,
        rw is_ring_hom.map_mul (OX.O.F.res (⊤ ∩ U) V HVU) at hfgV,
        rw [← presheaf.Hcomp', ← presheaf.Hcomp'] at hfgV,
        convert hfgV.trans (is_ring_hom.map_one (OX.O.F.res ⊤ V HVtop))
      end⟩), },
  choose U hu g hg,
  have, refine OX.O.gluing (topological_space.opens.covering_of_opens (OX.D f) U hu) _ _,
  { exact (λ i, OX.O.F.res _ _ (set.inter_subset_left _ _) (g i)) },
  { intros j k, dsimp only [res_to_inter_left, res_to_inter_right, topological_space.opens.covering_of_opens],
    iterate 2 { rw ← presheaf.Hcomp' },
    have hj : (U j ∩ D OX f) ∩ (U k ∩ D OX f) ⊆ U j :=
      set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_left _ _),
    have : set.subset.trans (res_to_inter_left._proof_1 (U j ∩ D OX f) (U k ∩ D OX f))
      (set.inter_subset_left ((U j).val) ((D OX f).val)) = hj := rfl, rw this at *, clear this,
    have hk : (U j ∩ D OX f) ∩ (U k ∩ D OX f) ⊆ U k :=
      set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_left _ _),
    have : set.subset.trans (res_to_inter_right._proof_1 (U j ∩ D OX f) (U k ∩ D OX f))
      (set.inter_subset_left ((U k).val) ((D OX f).val)) = hk := rfl, rw this at *, clear this,
    have := congr_arg (OX.O.F.res (U k) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) hk) (hg k),
    rw [is_ring_hom.map_mul (OX.O.F.res (U k) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) hk)] at this,
    rw [is_ring_hom.map_one (OX.O.F.res (U k) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) hk)] at this,
    rw [← presheaf.Hcomp', presheaf.Hcomp' _ ⊤ (U j) _ hj (set.subset_univ _)] at this,
    rw [← mul_one (OX.O.F.res (U j) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) _ (g j)), ← this],
    rw [← mul_assoc, ← is_ring_hom.map_mul (OX.O.F.res (U j) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) hj)],
    rw [mul_comm (g j), hg j, is_ring_hom.map_one (OX.O.F.res (U j) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) hj), one_mul] },
  cases this with S hS, use S, apply OX.O.locality (topological_space.opens.covering_of_opens (D OX f) U hu),
  intros i, specialize hS i,
  rw [is_ring_hom.map_mul (OX.O.F.res (D OX f) ((topological_space.opens.covering_of_opens (D OX f) U hu).Uis i) (subset_covering i))],
  rw [hS, ← presheaf.Hcomp', presheaf.Hcomp' _ ⊤ (U i) ((topological_space.opens.covering_of_opens (D OX f) U hu).Uis i)
        (set.inter_subset_left ((U i).val) ((D OX f).val)) (set.subset_univ _)],
  rw [← is_ring_hom.map_mul (OX.O.F.res (U i) ((topological_space.opens.covering_of_opens (D OX f) U hu).Uis i)
        ((set.inter_subset_left ((U i).val) ((D OX f).val))))],
  rw [hg, is_ring_hom.map_one (OX.O.F.res (U i) ((topological_space.opens.covering_of_opens (D OX f) U hu).Uis i)
        ((set.inter_subset_left ((U i).val) ((D OX f).val))))],
  rw [is_ring_hom.map_one (OX.O.F.res (D OX f) ((topological_space.opens.covering_of_opens (D OX f) U hu).Uis i) (subset_covering i))]
end

end locally_ringed_space

namespace sheaf_of_rings

open topological_space
variables {X : Type u} [topological_space X]
variables {B : set (opens X)} {HB : opens.is_basis B} (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)
variables (O : sheaf_of_rings X)
include HB
set_option pp.universes true

@[extensionality] theorem ext (U : opens X) (f g : O U) (hfg : ∀ x ∈ U, to_stalk O.F x U H f = to_stalk O.F x U H g) : f = g :=
begin
  have := λ x : U, quotient.exact (hfg x.1 x.2), choose C hc1 hc2 hc3 hc4,
  refine O.locality (opens.covering_of_opens U C hc1) f g (λ i, _),
  calc  O.F.res U (C i ∩ U) _ f
      = O.F.res (C i) (C i ∩ U) (set.inter_subset_left _ _) (O.F.res U (C i) _ f) : presheaf.Hcomp' _ _ _ _ _ _ _
  ... = O.F.res (C i) (C i ∩ U) _ (O.F.res U (C i) _ g) : congr_arg _ (hc4 i)
  ... = O.F.res U (C i ∩ U) _ g : (presheaf.Hcomp' _ _ _ _ _ _ _).symm
end

theorem is_sheaf_on_standard_basis_presheaf_of_rings_to_presheaf_of_rings_on_basis :
  sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd (presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB).to_presheaf_on_basis :=
begin
  dsimp only [sheaf_on_standard_basis.is_sheaf_on_standard_basis],
  intros U HUB OC, exact ⟨O.locality OC.to_covering, O.gluing OC.to_covering⟩
end

noncomputable def of_extension_basis (U : opens X) (HUB : U ∈ B)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U) : O U :=
classical.some $ to_presheaf_of_rings_extension.surjective Bstd (presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)
  (is_sheaf_on_standard_basis_presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O) HUB f

noncomputable def of_extension.aux1 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) : opens X :=
classical.some $ f.2 i.1 i.2

theorem of_extension.aux2 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  of_extension.aux1 Bstd U f i ∈ B :=
classical.some $ classical.some_spec $ f.2 i.1 i.2

theorem of_extension.aux3 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  i.1 ∈ of_extension.aux1 Bstd U f i :=
classical.some $ classical.some_spec $ classical.some_spec $ f.2 i.1 i.2

noncomputable def of_extension.aux4 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  F.to_presheaf_on_basis (of_extension.aux2 Bstd U f i) :=
classical.some $ classical.some_spec $ classical.some_spec $ classical.some_spec $ f.2 i.1 i.2

theorem of_extension.aux5 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  ∀ (y : X) (H : y ∈ U ∩ of_extension.aux1 Bstd U f i),
    f.1 y = λ (_x : y ∈ U), ⟦{U := of_extension.aux1 Bstd U f i, BU := _, Hx := H.2, s := of_extension.aux4 Bstd U f i}⟧ :=
classical.some_spec $ classical.some_spec $ classical.some_spec $ classical.some_spec $ f.2 i.1 i.2

theorem of_extension.aux6 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U)
  (y : X) (hyU : y ∈ U) (hyi : y ∈ of_extension.aux1 Bstd U f i) :
  ⟦quotient.out (f.1 y hyU)⟧ = ⟦{U := of_extension.aux1 Bstd U f i, BU := _, Hx := hyi, s := of_extension.aux4 Bstd U f i}⟧ :=
by rw [of_extension.aux5 Bstd U f i y ⟨hyU, hyi⟩, quotient.out_eq]

theorem of_extension.aux7 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U)
  (y : X) (hyU : y ∈ U) (hyi : y ∈ of_extension.aux1 Bstd U f i) :
  quotient.out (f.1 y hyU) ≈ {U := of_extension.aux1 Bstd U f i, BU := _, Hx := hyi, s := of_extension.aux4 Bstd U f i} :=
quotient.exact $ of_extension.aux6 Bstd U f i y hyU hyi

lemma of_extension.aux8 (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U) :
  ∃ f' : O U, ∀ i : U,
    O.F.res U ((opens.covering_of_opens U (of_extension.aux1 Bstd U f) (of_extension.aux3 Bstd U f)).Uis i)
      (subset_covering i)
      f' =
    O.F.res (of_extension.aux1 Bstd U f i) _ (set.inter_subset_left _ _)
      (of_extension.aux4 Bstd U f i) :=
begin
  refine quotient.induction_on
    (quotient.choice (λ i:U, (f.1 i.1 i.2 : stalk_on_basis ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd (O.F)).to_presheaf_on_basis) i.1)))
    (λ f', _),
  have, refine (O.gluing (opens.covering_of_opens U (of_extension.aux1 Bstd U f) (of_extension.aux3 Bstd U f)) _ _),
  { exact (λ i, O.F.res _ _ (set.inter_subset_left _ _) $ of_extension.aux4 Bstd U f i) },
  { have := of_extension.aux7 Bstd U f, choose g hg1 hg2 hg3 hg4 hg5,
    refine (λ j k : U, O.locality (opens.covering_of_opens _
        (λ i, g j i.1 i.2.1.2 i.2.1.1 ∩ g k i.1 i.2.2.2 i.2.2.1)
        (λ i, ⟨hg2 _ _ _ _, hg2 _ _ _ _⟩)) _ _ _),
    intros i, dsimp only [opens.covering_of_opens, res_to_inter_left, res_to_inter_right],
    iterate 4 { rw ← presheaf.Hcomp' },
    have hg5j := hg5 j i.1 i.2.1.2 i.2.1.1, have hg5k := hg5 k i.1 i.2.2.2 i.2.2.1,
    dsimp only [presheaf_of_rings_to_presheaf_of_rings_on_basis] at hg5j hg5k,
    rw [O.F.to_presheaf.Hcomp' (of_extension.aux1 Bstd U f j) (g j i.1 i.2.1.2 i.2.1.1), ← hg5j],
    rw [O.F.to_presheaf.Hcomp' (of_extension.aux1 Bstd U f k) (g k i.1 i.2.2.2 i.2.2.1), ← hg5k],
    iterate 2 { rw ← presheaf.Hcomp' },
    { exact set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_right _ _) },
    { exact set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_left _ _) } },
  exact this
end

noncomputable def of_extension (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U) : O U :=
classical.some $ of_extension.aux8 Bstd O U f

lemma of_extension_spec' (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U) :
  ∀ i : U,
    O.F.res U ((opens.covering_of_opens U (of_extension.aux1 Bstd U f) (of_extension.aux3 Bstd U f)).Uis i)
      (subset_covering i)
      (of_extension Bstd O U f) =
    O.F.res (of_extension.aux1 Bstd U f i) _ (set.inter_subset_left _ _)
      (of_extension.aux4 Bstd U f i) :=
classical.some_spec $ of_extension.aux8 Bstd O U f

lemma of_extension_spec (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U)
  (x : X) (hxU : x ∈ U) :
  ∃ (V : opens X) (HVB : V ∈ B) (hxV : x ∈ V) (HVU : V ⊆ U), f.1 x hxU = ⟦⟨V, HVB, hxV, O.F.res U V HVU (of_extension Bstd O U f)⟩⟧ :=
begin
  have hx : x ∈ of_extension.aux1 Bstd U f ⟨x, hxU⟩ ∩ U := ⟨of_extension.aux3 Bstd U f ⟨x, hxU⟩, hxU⟩,
  rcases opens.is_basis_iff_nbhd.1 HB hx with ⟨V, HVB, hxV, HV⟩,
  refine ⟨V, HVB, hxV, set.subset.trans HV (set.inter_subset_right _ _), _⟩,
  rw [congr_fun (of_extension.aux5 Bstd U f ⟨x, hxU⟩ x ⟨hxU, of_extension.aux3 Bstd U f ⟨x, hxU⟩⟩) hxU],
  refine quotient.sound ⟨V, HVB, hxV, set.subset.trans HV (set.inter_subset_left _ _), set.subset.refl _, _⟩,
  dsimp only [presheaf_of_rings_to_presheaf_of_rings_on_basis], rw [← presheaf.Hcomp'],
  calc  O.F.res (of_extension.aux1 Bstd U f ⟨x, hxU⟩) V _ (of_extension.aux4 Bstd U f ⟨x, hxU⟩)
      = O.F.res ((opens.covering_of_opens U (of_extension.aux1 Bstd U f) _).Uis ⟨x, hxU⟩) V _
          (O.F.res (of_extension.aux1 Bstd U f ⟨x, hxU⟩)
            ((opens.covering_of_opens U (of_extension.aux1 Bstd U f) _).Uis ⟨x, hxU⟩) _
            (of_extension.aux4 Bstd U f ⟨x, hxU⟩)) : presheaf.Hcomp' _ _ _ _ _ _ _
  ... = O.F.res ((opens.covering_of_opens U (of_extension.aux1 Bstd U f) _).Uis ⟨x, hxU⟩) V HV
          (O.F.res U ((opens.covering_of_opens U (of_extension.aux1 Bstd U f) _).Uis ⟨x, hxU⟩) _
            (of_extension Bstd O U f)) : congr_arg _ (of_extension_spec' Bstd O U f ⟨x, hxU⟩).symm
  ... = O.F.res U V _ (of_extension Bstd O U f) : (presheaf.Hcomp' _ _ _ _ _ _ _).symm
end

theorem of_extension_res (U V : opens X) (HVU : V ⊆ U)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U) :
  of_extension Bstd O V (presheaf.res _ U V HVU f) = O.F.res U V HVU (of_extension Bstd O U f) :=
begin
  ext, { exact HB }, intros x hxV, apply quotient.sound,
  rcases of_extension_spec Bstd O U f x (HVU hxV) with ⟨W1, HWB1, hxW1, HWU1, hw1⟩,
  rcases of_extension_spec Bstd O V (presheaf.res _ U V HVU f) x hxV with ⟨W2, HWB2, hxW2, HWV2, hw2⟩,
  rcases quotient.exact (hw1.symm.trans hw2) with ⟨W3, HWB3, hxW3, HW31, HW32, hw3⟩,
  refine ⟨W3, hxW3, set.subset.trans HW32 HWV2, set.subset.trans HW32 HWV2, _⟩,
  change O.F.res W1 W3 HW31 (O.F.res U W1 HWU1 (of_extension Bstd O U f)) =
    O.F.res W2 W3 HW32 (O.F.res V W2 HWV2 (of_extension Bstd O V $ presheaf.res _ U V HVU f)) at hw3,
  change O.F.res V W3 _ (of_extension Bstd O V $ presheaf.res _ U V HVU f) =
    (O.F.res V W3 _ (O.F.res U V HVU (of_extension Bstd O U f))),
  rw [← presheaf.Hcomp', ← presheaf.Hcomp'] at hw3, rw [← presheaf.Hcomp'], exact hw3.symm
end

end sheaf_of_rings

namespace sheaf_of_rings

variables {α : Type u} [topological_space α]
variables {β : Type u} [topological_space β]

variables {f : α → β} (Hf : continuous f) 

def pushforward (O : sheaf_of_rings α) : sheaf_of_rings β :=
{ F := O.F.pushforward Hf,
  locality := λ U OC s t H, O.locality (topological_space.opens.covering_comap Hf U OC) _ _ (λ i, by convert H i),
  gluing := λ U OC s H, by convert O.gluing (topological_space.opens.covering_comap Hf U OC) s H }

end sheaf_of_rings

section tag01I1

variables {X : Type u} [topological_space X] (OX : locally_ringed_space X)
variables (R : Type v) [comm_ring R]

/- https://stacks.math.columbia.edu/tag/01I1 -/
def mor_to_hom (f : morphism OX (Spec.locally_ringed_space R)) :
  (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤ :=
cast (congr_arg OX.O.F $ opens.comap_top f.Hf) ∘ f.fO.map ⊤

variables (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f]

def induced (x : X) : Spec R :=
⟨ideal.comap (to_stalk OX.O.F x ⊤ trivial ∘ f ∘ to_Spec_top R) (nonunits_ideal $ OX.Hstalks x),
@ideal.is_prime.comap _ _ _ _ _ _ _ $ (is_maximal_nonunits_ideal _).is_prime⟩

@[simp] lemma Spec.DO.val (g : R) : (Spec.DO R g).val = Spec.D' g :=
congr_fun (Spec.DO.val_eq_D' R) g

@[simp] lemma induced_preimage_D' (g : R) :
  induced OX R f ⁻¹' Spec.D' g = OX.D (f $ to_Spec_top R g) :=
set.ext $ λ x, classical.not_not

lemma induced_continuous : continuous (induced OX R f) :=
λ U HU, let ⟨Us, HUs, HUUs⟩ := topological_space.sUnion_basis_of_is_open (D_fs_basis R) HU in
by rw [HUUs, set.preimage_sUnion]; exact is_open_Union (λ S, is_open_Union $ λ HSUs,
let ⟨p, ⟨g, hp⟩, hpS⟩ := HUs HSUs in by rw [← hpS, hp, Spec.DO.val, induced_preimage_D']; exact OX.is_open_D' _)

@[simp] lemma comap_induced_DO (g : R) :
  opens.comap (induced_continuous OX R f) (Spec.DO R g) = OX.D (f $ to_Spec_top R g) :=
topological_space.opens.ext $ induced_preimage_D' OX R f g

noncomputable def induced_basis (U : topological_space.opens $ Spec R) (HUB : U ∈ D_fs R) :
  (structure_presheaf_on_basis R).F HUB → OX.O (opens.comap (induced_continuous OX R f) U) :=
localization.lift (OX.O.F.res ⊤ _ (set.subset_univ _) ∘ f ∘ to_Spec_top R) $ λ r hrSU,
is_unit.map'
  (OX.O.F.res
    (opens.comap (induced_continuous OX R f) (Spec.DO R r))
    (opens.comap (induced_continuous OX R f) U)
    (set.preimage_mono hrSU))
  (OX.O.F.res ⊤ _ (set.subset_univ _) (f $ to_Spec_top R r))
  (by rw comap_induced_DO; exact locally_ringed_space.is_unit_res_D _ _)
  (presheaf.Hcomp' _ _ _ _ _ _ _).symm

noncomputable def induced_stalk_elem (p : Spec R)
  (s : stalk_on_basis.elem (structure_presheaf_on_basis R).to_presheaf_on_basis p) :
  stalk_on_basis.elem
    (presheaf_of_rings_to_presheaf_of_rings_on_basis
      (D_fs_standard_basis R) (presheaf_of_rings.pushforward (induced_continuous OX R f) OX.O.F) :
        presheaf_of_rings_on_basis (Spec R) (D_fs_basis R)).to_presheaf_on_basis
    p :=
⟨s.1, s.2, s.3, induced_basis OX R f s.1 s.2 s.4⟩

noncomputable def induced_stalk (p : Spec R) :
  stalk_on_basis (structure_presheaf_on_basis R).to_presheaf_on_basis p →
  stalk_on_basis
    (presheaf_of_rings_to_presheaf_of_rings_on_basis
      (D_fs_standard_basis R) (presheaf_of_rings.pushforward (induced_continuous OX R f) OX.O.F) :
        presheaf_of_rings_on_basis (Spec R) (D_fs_basis R)).to_presheaf_on_basis
    p :=
quotient.lift (λ s, ⟦induced_stalk_elem OX R f p s⟧) $ begin
  rintros s1 s2 ⟨U, HUB, hpU, hUs1, hUs2, hs⟩,
  refine quotient.sound ⟨U, HUB, hpU, hUs1, hUs2, _⟩,
  cases s1 with U1 HUB1 Hx1 s1, cases s2 with U2 HUB2 Hx2 s2,
  dsimp only at hUs1 hUs2, dsimp only [induced_stalk_elem, induced_basis],
  revert hs,
  refine localization.induction_on s1 (λ r1 s1, localization.induction_on s2 (λ r2 s2, _)),
  intros hs, rcases quotient.exact hs with ⟨t, htSU, ht⟩, simp only [subtype.coe_mk] at ht,
  dsimp only [induced_stalk_elem, induced_basis, localization.lift, localization.lift'_mk, function.comp_apply,
    presheaf_of_rings_to_presheaf_of_rings_on_basis, presheaf_of_rings.pushforward, presheaf.pushforward],
  rw [is_ring_hom.map_mul (OX.O.F.res (opens.comap (induced_continuous OX R f) U1)
      (opens.comap (induced_continuous OX R f) U)
      (opens.comap_mono (induced_continuous OX R f) U U1 hUs1))],
  rw [is_ring_hom.map_mul (OX.O.F.res (opens.comap (induced_continuous OX R f) U2)
      (opens.comap (induced_continuous OX R f) U)
      (opens.comap_mono (induced_continuous OX R f) U U2 hUs2))],
  generalize : localization.lift._proof_1 _ _ _ = hu1,
  generalize : localization.lift._proof_1 _ _ _ = hu2,
  dsimp only [function.comp_apply] at hu1 hu2,
  have := classical.some_spec hu2, revert this,
  have := classical.some_spec hu1, revert this,
  cases classical.some hu1 with v1 i1 hvi1 hiv1,
  cases classical.some hu2 with v2 i2 hvi2 hiv2,
  rintros h1 h2, change _ = v1 at h1, subst h1, change _ = v2 at h2, subst h2,
  change _ * OX.O.F.res _ _ _ i1 = _ * OX.O.F.res _ _ _ i2,
  replace ht := congr_arg (λ x, OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _) (f (to_Spec_top R x))) ht,
  dsimp only at ht,
  rw [is_ring_hom.map_mul (to_Spec_top R)] at ht,
  rw [is_ring_hom.map_sub (to_Spec_top R)] at ht,
  rw [is_ring_hom.map_mul (to_Spec_top R)] at ht,
  rw [is_ring_hom.map_mul (to_Spec_top R)] at ht,
  rw [is_ring_hom.map_zero (to_Spec_top R)] at ht,
  rw [is_ring_hom.map_mul f] at ht,
  rw [is_ring_hom.map_sub f] at ht,
  rw [is_ring_hom.map_mul f] at ht,
  rw [is_ring_hom.map_mul f] at ht,
  rw [is_ring_hom.map_zero f] at ht,
  rw [is_ring_hom.map_mul (OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _))] at ht,
  rw [is_ring_hom.map_sub (OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _))] at ht,
  rw [is_ring_hom.map_mul (OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _))] at ht,
  rw [is_ring_hom.map_mul (OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _))] at ht,
  change _ = OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _) 0 at ht,
  rw [is_ring_hom.map_zero (OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U) (set.subset_univ _))] at ht,
  have := OX.is_unit_res_D (f (to_Spec_top R t)), rw ← comap_induced_DO at this,
  replace this := this.map (OX.O.F.res
    (opens.comap (induced_continuous OX R f) (Spec.DO R t))
    (opens.comap (induced_continuous OX R f) U)
    (opens.comap_mono _ _ _ htSU)),
  rw ← presheaf.Hcomp' at this,
  cases this with u hut,
  change (((OX.O).F).to_presheaf).res ⊤ (opens.comap (induced_continuous OX R f) U)
        (set.subset_univ ((opens.comap (induced_continuous OX R f) U).val))
        (f (to_Spec_top R t)) = _ at hut,
  rw hut at ht, replace ht := congr_arg (λ z : OX.O (opens.comap (induced_continuous OX R f) U), z * (↑(u⁻¹ : units (OX.O (opens.comap (induced_continuous OX R f) U))) : OX.O _)) ht,
  dsimp only at ht, change _ = (0 : OX.O (opens.comap (induced_continuous OX R f) U)) * _ at ht,
  rw [mul_assoc, zero_mul, units.mul_inv, mul_one, sub_eq_zero_iff_eq] at ht,
  rw [← presheaf.Hcomp', presheaf.Hcomp' _ ⊤ (opens.comap (induced_continuous OX R f) U2) (opens.comap (induced_continuous OX R f) U)
      (opens.comap_mono _ _ _ hUs2) (set.subset_univ _)],
  rw [← mul_one (OX.O.F.res ⊤ (opens.comap (induced_continuous OX R f) U2) (set.subset_univ _) (f (to_Spec_top R r1)))],
  change (OX.O.F.res _ _ _ (_ * (1 : OX.O (opens.comap _ U2)))) * _ = _,
  rw [← hvi2, ← mul_assoc, mul_comm (OX.O.F.res _ _ _ (f _))],
  rw [is_ring_hom.map_mul (OX.O.F.res (opens.comap (induced_continuous OX R f) U2) (opens.comap (induced_continuous OX R f) U) (opens.comap_mono _ _ _ hUs2))],
  rw [is_ring_hom.map_mul (OX.O.F.res (opens.comap (induced_continuous OX R f) U2) (opens.comap (induced_continuous OX R f) U) (opens.comap_mono _ _ _ hUs2))],
  rw [← presheaf.Hcomp', ← presheaf.Hcomp', show set.subset.trans (opens.comap_mono (induced_continuous OX R f) U U2 hUs2)
        (induced_basis._proof_1 OX R f U2) = set.subset_univ _, from rfl, ← ht],
  rw [mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc],
  replace hiv1 := congr_arg (OX.O.F.res (opens.comap (induced_continuous OX R f) U1) (opens.comap (induced_continuous OX R f) U) (opens.comap_mono _ _ _ hUs1)) hiv1,
  rw [is_ring_hom.map_mul (OX.O.F.res (opens.comap (induced_continuous OX R f) U1) (opens.comap (induced_continuous OX R f) U) (opens.comap_mono _ _ _ hUs1))] at hiv1,
  change _ = OX.O.F.res (opens.comap (induced_continuous OX R f) U1) (opens.comap (induced_continuous OX R f) U) (opens.comap_mono _ _ _ hUs1) 1 at hiv1,
  rw [is_ring_hom.map_one (OX.O.F.res (opens.comap (induced_continuous OX R f) U1) (opens.comap (induced_continuous OX R f) U) (opens.comap_mono _ _ _ hUs1))] at hiv1,
  rw [← presheaf.Hcomp', show set.subset.trans (opens.comap_mono (induced_continuous OX R f) U U1 hUs1) (induced_basis._proof_1 OX R f U1) = set.subset_univ _, from rfl] at hiv1,
  rw [hiv1, mul_one, ← presheaf.Hcomp'], refl
end

--set_option pp.proofs true
/- https://stacks.math.columbia.edu/tag/01I1 -/
noncomputable def hom_to_mor {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type u) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f] :
  morphism OX (Spec.locally_ringed_space R) :=
{ f := induced OX R f,
  Hf := induced_continuous OX R f,
  fO :=
  { map := λ U s, (sheaf_of_rings.of_extension
      (D_fs_standard_basis R) _ _
      (⟨λ x hxU, induced_stalk OX R f x (s.1 x hxU),
        λ x hxU, let ⟨V, HVB, hxV, s1, hs1⟩ := s.2 x hxU in
          ⟨V, HVB, hxV, induced_basis OX R f V HVB s1, λ g hg, funext $ λ hgU, by rw hs1 g hg; refl⟩⟩ :
          ((presheaf_of_rings_to_presheaf_of_rings_on_basis
            (D_fs_standard_basis R)
            (OX.O.pushforward (induced_continuous OX R f)).F :
        presheaf_of_rings_on_basis _ (D_fs_basis R))ᵣₑₓₜ _) U) :
      OX.O.pushforward (induced_continuous OX R f) U),
    commutes := λ U V HVU, funext $ λ s, begin
      dsimp only [function.comp_apply],
      change _ = (sheaf_of_rings.pushforward _ (OX.O)).F.res _ _ _ _,
      rw ← sheaf_of_rings.of_extension_res, refl
    end } }

end tag01I1
