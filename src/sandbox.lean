import sheaves.locally_ringed_space
import instances.affine_scheme

universes u v w

def opens.indefinite_description {α : Type u} [topological_space α] (p : topological_space.opens α → Prop) (hp : ∃ U, p U) : {U // p U} :=
⟨⟨↑(classical.some hp), subtype.property _⟩, by rw subtype.coe_eta; exact classical.some_spec hp⟩

def opens.some {α : Type u} [topological_space α] {p : topological_space.opens α → Prop} (hp : ∃ U, p U) : topological_space.opens α :=
(opens.indefinite_description p hp).1

theorem opens.some_spec {α : Type u} [topological_space α] {p : topological_space.opens α → Prop} (hp : ∃ U, p U) : p (opens.some hp) :=
(opens.indefinite_description p hp).2

section presheaf_of_rings

variables {α : Type u} [topological_space α]
variables (F : presheaf_of_rings α)
variables (U V : topological_space.opens α) (HVU : V ⊆ U)
variables (x y : F U)

@[simp] lemma res_add : F.res U V HVU (x + y) = F.res U V HVU x + F.res U V HVU y := is_ring_hom.map_add _
@[simp] lemma res_zero : F.res U V HVU 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma res_neg : F.res U V HVU (-x) = -F.res U V HVU x := is_ring_hom.map_neg _
@[simp] lemma res_sub : F.res U V HVU (x - y) = F.res U V HVU x - F.res U V HVU y := is_ring_hom.map_sub _
@[simp] lemma res_mul : F.res U V HVU (x * y) = F.res U V HVU x * F.res U V HVU y := is_ring_hom.map_mul _
@[simp] lemma res_one : F.res U V HVU 1 = 1 := is_ring_hom.map_one _

end presheaf_of_rings

section presheaf_of_rings_on_basis

variables {α : Type u} [topological_space α] {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B)
variables (F : presheaf_of_rings_on_basis α HB)
variables (U V : topological_space.opens α) (HUB : U ∈ B) (HVB : V ∈ B) (HVU : V ⊆ U)
variables (x y : F.F HUB)

@[simp] lemma bres_add : F.res HUB HVB HVU (x + y) = F.res HUB HVB HVU x + F.res HUB HVB HVU y := is_ring_hom.map_add _
@[simp] lemma bres_zero : F.res HUB HVB HVU 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma bres_neg : F.res HUB HVB HVU (-x) = -F.res HUB HVB HVU x := is_ring_hom.map_neg _
@[simp] lemma bres_sub : F.res HUB HVB HVU (x - y) = F.res HUB HVB HVU x - F.res HUB HVB HVU y := is_ring_hom.map_sub _
@[simp] lemma bres_mul : F.res HUB HVB HVU (x * y) = F.res HUB HVB HVU x * F.res HUB HVB HVU y := is_ring_hom.map_mul _
@[simp] lemma bres_one : F.res HUB HVB HVU 1 = 1 := is_ring_hom.map_one _

end presheaf_of_rings_on_basis

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
        rw [res_mul, ← presheaf.Hcomp', ← presheaf.Hcomp'] at hfgV,
        convert hfgV.trans (res_one _ _ _ _)
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
    rw [res_mul, res_one] at this,
    rw [← presheaf.Hcomp', presheaf.Hcomp' _ ⊤ (U j) _ hj (set.subset_univ _)] at this,
    rw [← mul_one (OX.O.F.res (U j) ((U j ∩ D OX f) ∩ (U k ∩ D OX f)) _ (g j)), ← this],
    rw [← mul_assoc, ← res_mul, mul_comm (g j), hg j, res_one, one_mul] },
  cases this with S hS, use S, apply OX.O.locality (topological_space.opens.covering_of_opens (D OX f) U hu),
  intros i, specialize hS i,
  rw [res_mul, hS, ← presheaf.Hcomp'],
  rw [presheaf.Hcomp' _ ⊤ (U i) ((topological_space.opens.covering_of_opens (D OX f) U hu).Uis i)
        (set.inter_subset_left ((U i).val) ((D OX f).val)) (set.subset_univ _)],
  rw [← res_mul, hg, res_one, res_one]
end

end locally_ringed_space

namespace sheaf_of_rings

open topological_space
variables {X : Type u} [topological_space X]
variables {B : set (opens X)} (HB : opens.is_basis B) (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)
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
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U) : O U :=
classical.some $ to_presheaf_of_rings_extension.surjective Bstd (presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)
  (is_sheaf_on_standard_basis_presheaf_of_rings_to_presheaf_of_rings_on_basis HB Bstd O) HUB f

def of_extension.aux1 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) : opens X :=
opens.some $ f.2 i.1 i.2

theorem of_extension.aux2 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  of_extension.aux1 HB Bstd U f i ∈ B :=
classical.some $ opens.some_spec $ f.2 i.1 i.2

theorem of_extension.aux3 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  i.1 ∈ of_extension.aux1 HB Bstd U f i :=
classical.some $ classical.some_spec $ opens.some_spec $ f.2 i.1 i.2

noncomputable def of_extension.aux4 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  F.to_presheaf_on_basis (of_extension.aux2 HB Bstd U f i) :=
classical.some $ classical.some_spec $ classical.some_spec $ opens.some_spec $ f.2 i.1 i.2

theorem of_extension.aux5 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U) :
  ∀ (y : X) (H : y ∈ U ∩ of_extension.aux1 HB Bstd U f i),
    f.1 y = λ (_x : y ∈ U), ⟦{U := of_extension.aux1 HB Bstd U f i, BU := _, Hx := H.2, s := of_extension.aux4 HB Bstd U f i}⟧ :=
classical.some_spec $ classical.some_spec $ classical.some_spec $ opens.some_spec $ f.2 i.1 i.2

theorem of_extension.aux6 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U)
  (y : X) (hyU : y ∈ U) (hyi : y ∈ of_extension.aux1 HB Bstd U f i) :
  ⟦quotient.out (f.1 y hyU)⟧ = ⟦{U := of_extension.aux1 HB Bstd U f i, BU := _, Hx := hyi, s := of_extension.aux4 HB Bstd U f i}⟧ :=
by rw [of_extension.aux5 HB Bstd U f i y ⟨hyU, hyi⟩, quotient.out_eq]

theorem of_extension.aux7 {F : presheaf_of_rings_on_basis X HB} (U : opens X) (f : (F ᵣₑₓₜ Bstd) U) (i : U)
  (y : X) (hyU : y ∈ U) (hyi : y ∈ of_extension.aux1 HB Bstd U f i) :
  quotient.out (f.1 y hyU) ≈ {U := of_extension.aux1 HB Bstd U f i, BU := _, Hx := hyi, s := of_extension.aux4 HB Bstd U f i} :=
quotient.exact $ of_extension.aux6 HB Bstd U f i y hyU hyi

lemma of_extension.aux8 (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U) :
  ∃ f' : O U, ∀ i : U,
    O.F.res U ((opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) (of_extension.aux3 HB Bstd U f)).Uis i)
      (subset_covering i)
      f' =
    O.F.res (of_extension.aux1 HB Bstd U f i) _ (set.inter_subset_left _ _)
      (of_extension.aux4 HB Bstd U f i) :=
begin
  refine quotient.induction_on
    (quotient.choice (λ i:U, (f.1 i.1 i.2 : stalk_on_basis ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd (O.F)).to_presheaf_on_basis) i.1)))
    (λ f', _),
  have, refine (O.gluing (opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) (of_extension.aux3 HB Bstd U f)) _ _),
  { exact (λ i, O.F.res _ _ (set.inter_subset_left _ _) $ of_extension.aux4 HB Bstd U f i) },
  { have := of_extension.aux7 HB Bstd U f, choose g hg1 hg2 hg3 hg4 hg5,
    refine (λ j k : U, O.locality (opens.covering_of_opens _
        (λ i, g j i.1 i.2.1.2 i.2.1.1 ∩ g k i.1 i.2.2.2 i.2.2.1)
        (λ i, ⟨hg2 _ _ _ _, hg2 _ _ _ _⟩)) _ _ _),
    intros i, dsimp only [opens.covering_of_opens, res_to_inter_left, res_to_inter_right],
    iterate 4 { rw ← presheaf.Hcomp' },
    have hg5j := hg5 j i.1 i.2.1.2 i.2.1.1, have hg5k := hg5 k i.1 i.2.2.2 i.2.2.1,
    dsimp only [presheaf_of_rings_to_presheaf_of_rings_on_basis] at hg5j hg5k,
    rw [O.F.to_presheaf.Hcomp' (of_extension.aux1 HB Bstd U f j) (g j i.1 i.2.1.2 i.2.1.1), ← hg5j],
    rw [O.F.to_presheaf.Hcomp' (of_extension.aux1 HB Bstd U f k) (g k i.1 i.2.2.2 i.2.2.1), ← hg5k],
    iterate 2 { rw ← presheaf.Hcomp' },
    { exact set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_right _ _) },
    { exact set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_left _ _) } },
  exact this
end

noncomputable def of_extension (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U) : O U :=
classical.some $ of_extension.aux8 HB Bstd O U f

lemma of_extension_spec' (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U) :
  ∀ i : U,
    O.F.res U ((opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) (of_extension.aux3 HB Bstd U f)).Uis i)
      (subset_covering i)
      (of_extension HB Bstd O U f) =
    O.F.res (of_extension.aux1 HB Bstd U f i) _ (set.inter_subset_left _ _)
      (of_extension.aux4 HB Bstd U f i) :=
classical.some_spec $ of_extension.aux8 HB Bstd O U f

lemma of_extension_spec (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U)
  (x : X) (hxU : x ∈ U) :
  ∃ (V : opens X) (HVB : V ∈ B) (hxV : x ∈ V) (HVU : V ⊆ U), f.1 x hxU = ⟦⟨V, HVB, hxV, O.F.res U V HVU (of_extension HB Bstd O U f)⟩⟧ :=
begin
  have hx : x ∈ of_extension.aux1 HB Bstd U f ⟨x, hxU⟩ ∩ U := ⟨of_extension.aux3 HB Bstd U f ⟨x, hxU⟩, hxU⟩,
  rcases opens.is_basis_iff_nbhd.1 HB hx with ⟨V, HVB, hxV, HV⟩,
  refine ⟨V, HVB, hxV, set.subset.trans HV (set.inter_subset_right _ _), _⟩,
  rw [congr_fun (of_extension.aux5 HB Bstd U f ⟨x, hxU⟩ x ⟨hxU, of_extension.aux3 HB Bstd U f ⟨x, hxU⟩⟩) hxU],
  refine quotient.sound ⟨V, HVB, hxV, set.subset.trans HV (set.inter_subset_left _ _), set.subset.refl _, _⟩,
  dsimp only [presheaf_of_rings_to_presheaf_of_rings_on_basis], rw [← presheaf.Hcomp'],
  calc  O.F.res (of_extension.aux1 HB Bstd U f ⟨x, hxU⟩) V _ (of_extension.aux4 HB Bstd U f ⟨x, hxU⟩)
      = O.F.res ((opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) _).Uis ⟨x, hxU⟩) V _
          (O.F.res (of_extension.aux1 HB Bstd U f ⟨x, hxU⟩)
            ((opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) _).Uis ⟨x, hxU⟩) _
            (of_extension.aux4 HB Bstd U f ⟨x, hxU⟩)) : presheaf.Hcomp' _ _ _ _ _ _ _
  ... = O.F.res ((opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) _).Uis ⟨x, hxU⟩) V HV
          (O.F.res U ((opens.covering_of_opens U (of_extension.aux1 HB Bstd U f) _).Uis ⟨x, hxU⟩) _
            (of_extension HB Bstd O U f)) : congr_arg _ (of_extension_spec' HB Bstd O U f ⟨x, hxU⟩).symm
  ... = O.F.res U V _ (of_extension HB Bstd O U f) : (presheaf.Hcomp' _ _ _ _ _ _ _).symm
end

theorem of_extension_res (U V : opens X) (HVU : V ⊆ U)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U) :
  of_extension HB Bstd O V (presheaf.res _ U V HVU f) = O.F.res U V HVU (of_extension HB Bstd O U f) :=
begin
  ext, { exact HB }, intros x hxV, apply quotient.sound,
  rcases of_extension_spec HB Bstd O U f x (HVU hxV) with ⟨W1, HWB1, hxW1, HWU1, hw1⟩,
  rcases of_extension_spec HB Bstd O V (presheaf.res _ U V HVU f) x hxV with ⟨W2, HWB2, hxW2, HWV2, hw2⟩,
  rcases quotient.exact (hw1.symm.trans hw2) with ⟨W3, HWB3, hxW3, HW31, HW32, hw3⟩,
  refine ⟨W3, hxW3, set.subset.trans HW32 HWV2, set.subset.trans HW32 HWV2, _⟩,
  change O.F.res W1 W3 HW31 (O.F.res U W1 HWU1 (of_extension HB Bstd O U f)) =
    O.F.res W2 W3 HW32 (O.F.res V W2 HWV2 (of_extension HB Bstd O V $ presheaf.res _ U V HVU f)) at hw3,
  change O.F.res V W3 _ (of_extension HB Bstd O V $ presheaf.res _ U V HVU f) =
    (O.F.res V W3 _ (O.F.res U V HVU (of_extension HB Bstd O U f))),
  rw [← presheaf.Hcomp', ← presheaf.Hcomp'] at hw3, rw [← presheaf.Hcomp'], exact hw3.symm
end
set_option pp.proofs true

def to_extension (U : opens X) (f : O U) :
  ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F : presheaf_of_rings_on_basis X HB)ᵣₑₓₜ Bstd) U :=
{ val := λ x hxU, ⟦{ U := opens.some (opens.is_basis_iff_nbhd.1 HB hxU),
    BU := classical.some $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hxU),
    Hx := (classical.some_spec $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hxU)).1,
    s := O.F.res _ _ (classical.some_spec $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hxU)).2 f }⟧,
  property := λ x hxU, ⟨opens.some (opens.is_basis_iff_nbhd.1 HB hxU),
    classical.some $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hxU),
    (classical.some_spec $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hxU)).1,
    O.F.res _ _ (classical.some_spec $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hxU)).2 f,
    λ y hy, funext $ λ hyU, have y ∈ opens.some (opens.is_basis_iff_nbhd.1 HB hxU) ∩ opens.some (opens.is_basis_iff_nbhd.1 HB hyU),
      from ⟨hy.2, (classical.some_spec $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB hyU)).1⟩,
      let ⟨V, HVB, hyV, HV⟩ := opens.is_basis_iff_nbhd.1 HB this in quotient.sound $
      ⟨V, HVB, hyV, set.subset.trans HV (set.inter_subset_right _ _),
        set.subset.trans HV (set.inter_subset_left _ _),
        show O.F.res _ _ _ (O.F.res _ _ _ _) = O.F.res _ _ _ (O.F.res _ _ _ _),
        by rw [← presheaf.Hcomp', ← presheaf.Hcomp']⟩⟩ }

theorem of_to_extension (U : opens X) (f : O U) :
  of_extension HB Bstd O U (to_extension HB Bstd O U f) = f :=
begin
  ext, { exact HB }, intros x hxU,
  rcases of_extension_spec HB Bstd O U (to_extension HB Bstd O U f) x hxU with ⟨V, HVB, hsV, HVU, hv⟩,
  rcases quotient.exact hv with ⟨W, HWB, hxW, HW1, HW2, hw⟩,
  refine quotient.sound ⟨W, hxW, set.subset.trans HW2 HVU, set.subset.trans HW2 HVU, _⟩,
  change O.F.res _ _ _ (O.F.res _ _ _ _) = O.F.res _ _ _ (O.F.res _ _ _ _) at hw,
  rw [← presheaf.Hcomp', ← presheaf.Hcomp'] at hw, exact hw.symm
end

theorem to_of_extension (U : opens X)
  (f : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U) :
  to_extension HB Bstd O U (of_extension HB Bstd O U f) = f :=
subtype.eq $ funext $ λ x, funext $ λ hxU, eq.symm $ let ⟨V, HVB, hxV, HVU, hv⟩ := of_extension_spec HB Bstd O U f x hxU in
have x ∈ V ∩ classical.some (to_extension._proof_1 HB U x hxU) := ⟨hxV, to_extension._proof_3 HB U x hxU⟩,
let ⟨W, HWB, hxW, HWV⟩ := opens.is_basis_iff_nbhd.1 HB this in
hv.trans $ quotient.sound ⟨W, HWB, hxW, set.subset.trans HWV (set.inter_subset_left _ _), set.subset.trans HWV (set.inter_subset_right _ _),
show O.F.res _ _ _ (O.F.res _ _ _ _) = O.F.res _ _ _ (O.F.res _ _ _ _),
by rw [← presheaf.Hcomp', ← presheaf.Hcomp']⟩

instance is_ring_hom_to_extension (U : opens X) : is_ring_hom (to_extension HB Bstd O U) :=
{ map_one := subtype.eq $ funext $ λ x, funext $ λ hxU, quotient.sound
    ⟨opens.some (to_extension._proof_1 HB U x hxU),
    to_extension._proof_2 HB U x hxU, to_extension._proof_3 HB U x hxU,
    set.subset.refl _, set.subset_univ _,
    show O.F.res _ _ _ (O.F.res _ _ _ 1) = O.F.res _ _ _ 1,
    by rw [res_one, res_one, res_one]⟩,
  map_mul := λ s1 s2, subtype.eq $ funext $ λ x, funext $ λ hxU, quotient.sound
    ⟨opens.some (to_extension._proof_1 HB U x hxU),
    to_extension._proof_2 HB U x hxU, to_extension._proof_3 HB U x hxU,
    set.subset.refl _, set.subset_inter (set.subset.refl _) (set.subset.refl _),
    show O.F.res _ _ _ (O.F.res _ _ _ (s1 * s2)) = O.F.res _ _ _ (O.F.res _ _ _ (O.F.res _ _ _ _) * O.F.res _ _ _ (O.F.res _ _ _ _)),
    by iterate 3 { rw res_mul }; iterate 6 { rw ← presheaf.Hcomp' }⟩,
  map_add := λ s1 s2, subtype.eq $ funext $ λ x, funext $ λ hxU, quotient.sound
    ⟨opens.some (to_extension._proof_1 HB U x hxU),
    to_extension._proof_2 HB U x hxU, to_extension._proof_3 HB U x hxU,
    set.subset.refl _, set.subset_inter (set.subset.refl _) (set.subset.refl _),
    show O.F.res _ _ _ (O.F.res _ _ _ (s1 + s2)) = O.F.res _ _ _ (O.F.res _ _ _ (O.F.res _ _ _ _) + O.F.res _ _ _ (O.F.res _ _ _ _)),
    by iterate 3 { rw res_add }; iterate 6 { rw ← presheaf.Hcomp' }⟩ }

noncomputable def ring_equiv_extension (U : opens X) :
  O U ≃r ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U :=
{ to_fun := to_extension HB Bstd O U,
  inv_fun := of_extension HB Bstd O U,
  left_inv := of_to_extension HB Bstd O U,
  right_inv := to_of_extension HB Bstd O U,
  hom := sheaf_of_rings.is_ring_hom_to_extension HB Bstd O U }

instance is_ring_hom_of_extension (U : opens X) : is_ring_hom (of_extension HB Bstd O U) :=
(ring_equiv_extension HB Bstd O U).symm.hom

def stalk_on_basis_to_stalk (F : presheaf_of_rings X) (U : opens X) (p : X) (hpU : p ∈ U)
  (σ : stalk_on_basis (presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd F : presheaf_of_rings_on_basis X HB).to_presheaf_on_basis p) :
  stalk_of_rings F p :=
quotient.lift_on σ (λ e, to_stalk F p e.U e.Hx e.s) $ λ e₁ e₂ ⟨V, HVB, hpV, HV1, HV2, HV⟩,
quotient.sound ⟨V, hpV, HV1, HV2, HV⟩

def stalk_to_stalk_on_basis (F : presheaf_of_rings.{u v} X) (U : opens X) (p : X) (hpU : p ∈ U)
  (σ : stalk_of_rings F p) :
  stalk_on_basis (presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd F : presheaf_of_rings_on_basis X HB).to_presheaf_on_basis p :=
quotient.lift_on σ (λ e, (⟦⟨opens.some (opens.is_basis_iff_nbhd.1 HB e.HxU),
    Exists.fst $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB e.HxU),
    and.left $ Exists.snd $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB e.HxU),
    presheaf.res _ _ _ (and.right $ Exists.snd $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB e.HxU)) e.s⟩⟧ :
      stalk_on_basis (presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd F : presheaf_of_rings_on_basis X HB).to_presheaf_on_basis p)) $
λ e₁ e₂ ⟨V, hpV, HV1, HV2, HV⟩,
have p ∈ V ∩ (opens.some (opens.is_basis_iff_nbhd.1 HB e₁.HxU) ∩ opens.some (opens.is_basis_iff_nbhd.1 HB e₂.HxU)),
from ⟨hpV, and.left $ Exists.snd $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB e₁.HxU),
  and.left $ Exists.snd $ opens.some_spec (opens.is_basis_iff_nbhd.1 HB e₂.HxU)⟩,
let ⟨W, HWB, hpW, HWV⟩ := opens.is_basis_iff_nbhd.1 HB this in
quotient.sound ⟨W, HWB, hpW, set.subset.trans HWV (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_left _ _)),
set.subset.trans HWV (set.subset.trans (set.inter_subset_right _ _) (set.inter_subset_right _ _)),
have _ := congr_arg (F.res _ W (set.subset.trans HWV (set.inter_subset_left _ _))) HV,
show F.res _ _ _ (F.res _ _ _ _) = F.res _ _ _ (F.res _ _ _ _),
by rw [← presheaf.Hcomp', ← presheaf.Hcomp'] at this ⊢; exact this⟩

theorem to_stalk_of_extension (U : opens X)
  (F : ((presheaf_of_rings_to_presheaf_of_rings_on_basis Bstd O.F)ᵣₑₓₜ Bstd) U)
  (p : X) (hpU : p ∈ U) :
  to_stalk O.F p U hpU (of_extension HB Bstd O U F) = stalk_on_basis_to_stalk _ _ _ U _ hpU (F.1 p hpU) :=
let ⟨V, HVB, hpV, HVU, hv⟩ := of_extension_spec HB Bstd O U F p hpU in
hv.symm ▸ quotient.sound ⟨V, hpV, HVU, set.subset.refl V, presheaf.Hcomp' _ _ _ _ _ _ _⟩

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

theorem presheaf.fmap.commutes' {α : Type u} [topological_space α] {β : Type v} [topological_space β]
  {f : α → β} {hf : continuous f} {F : presheaf α} {G : presheaf β} (m : presheaf.fmap hf F G)
  (U V : topological_space.opens β) (HVU : V ⊆ U) (s : G U) (h : opens.comap hf V ⊆ opens.comap hf U) :
  F.res (opens.comap hf U) (opens.comap hf V) h (m.map U s) = m.map V (G.res U V HVU s) :=
(congr_fun (m.commutes U V HVU) s).symm

def presheaf.fmap.stalk {α : Type u} [topological_space α] {β : Type v} [topological_space β]
  {f : α → β} {hf : continuous f} {F : presheaf α} {G : presheaf β} (m : presheaf.fmap hf F G) (x : α) :
  stalk G (f x) → stalk F x :=
quotient.lift (λ s : stalk.elem G (f x), (⟦⟨opens.comap hf s.U, s.HxU, m.map s.U s.s⟩⟧ : stalk F x)) $
λ s1 s2 ⟨U, hfxU, HUs1, HUs2, HU⟩, quotient.sound ⟨opens.comap hf U, hfxU, opens.comap_mono _ _ _ HUs1, opens.comap_mono _ _ _ HUs2,
show F.res (opens.comap hf s1.U) (opens.comap hf U) _ (m.map s1.U s1.s) =
  F.res (opens.comap hf s2.U) (opens.comap hf U) _ (m.map s2.U s2.s),
by rw [m.commutes', m.commutes', HU]⟩

def presheaf.fmap.stalk_of_rings {α : Type u} [topological_space α] {β : Type v} [topological_space β]
  {f : α → β} {hf : continuous f} {F : presheaf_of_rings α} {G : presheaf_of_rings β} (m : presheaf_of_rings.fmap hf F G)
  (x : α) (s : stalk_of_rings G (f x)) : stalk_of_rings F x :=
m.stalk x s

theorem is_ring_hom_stalk_of_rings {α : Type u} [topological_space α] {β : Type v} [topological_space β]
  {f : α → β} {hf : continuous f} {F : presheaf_of_rings α} {G : presheaf_of_rings β} (m : presheaf_of_rings.fmap hf F G) [hm : ∀ U, is_ring_hom (m.map U)]
  (x : α) : is_ring_hom (presheaf.fmap.stalk_of_rings m x) :=
{ map_one := quotient.sound ⟨⊤, trivial, set.subset.refl _, set.subset.refl _, congr_arg _ (is_ring_hom.map_one (m.map ⊤))⟩,
  map_mul := λ s1 s2, quotient.induction_on₂ s1 s2 $ λ e1 e2, quotient.sound ⟨opens.comap hf (e1.U ∩ e2.U),
    ⟨e1.HxU, e2.HxU⟩, set.subset.refl _,
    set.subset_inter (opens.comap_mono _ _ _ (set.inter_subset_left _ _)) (opens.comap_mono _ _ _ (set.inter_subset_right _ _)),
    show F.res (opens.comap hf (e1.U ∩ e2.U)) (opens.comap hf (e1.U ∩ e2.U)) _ (m.map (e1.U ∩ e2.U) (G.res _ _ _ e1.s * G.res _ _ _ e2.s)) =
      F.res (opens.comap hf e1.U ∩ opens.comap hf e2.U) (opens.comap hf (e1.U ∩ e2.U)) _ (F.res _ _ _ (m.map e1.U e1.s) * F.res _ _ _ (m.map e2.U e2.s)),
    by rw [m.commutes' _ _ (set.subset.refl _),
        res_mul,
        is_ring_hom.map_mul (F.res (opens.comap hf e1.U ∩ opens.comap hf e2.U) (opens.comap hf (e1.U ∩ e2.U))
          (set.subset_inter (opens.comap_mono _ _ _ (set.inter_subset_left _ _)) (opens.comap_mono _ _ _ (set.inter_subset_right _ _)))),
        ← presheaf.Hcomp', ← presheaf.Hcomp', ← presheaf.Hcomp', ← presheaf.Hcomp',
        m.commutes' e1.U (e1.U ∩ e2.U) (set.inter_subset_left _ _),
        m.commutes' e2.U (e1.U ∩ e2.U) (set.inter_subset_right _ _),
        is_ring_hom.map_mul (m.map (e1.U ∩ e2.U))]; refl⟩,
  map_add := λ s1 s2, quotient.induction_on₂ s1 s2 $ λ e1 e2, quotient.sound ⟨opens.comap hf (e1.U ∩ e2.U),
    ⟨e1.HxU, e2.HxU⟩, set.subset.refl _,
    set.subset_inter (opens.comap_mono _ _ _ (set.inter_subset_left _ _)) (opens.comap_mono _ _ _ (set.inter_subset_right _ _)),
    show F.res (opens.comap hf (e1.U ∩ e2.U)) (opens.comap hf (e1.U ∩ e2.U)) _ (m.map (e1.U ∩ e2.U) (G.res _ _ _ e1.s + G.res _ _ _ e2.s)) =
      F.res (opens.comap hf e1.U ∩ opens.comap hf e2.U) (opens.comap hf (e1.U ∩ e2.U)) _ (F.res _ _ _ (m.map e1.U e1.s) + F.res _ _ _ (m.map e2.U e2.s)),
    by rw [m.commutes' _ _ (set.subset.refl _),
        is_ring_hom.map_add (G.res (e1.U ∩ e2.U) (e1.U ∩ e2.U) (set.subset.refl _)),
        is_ring_hom.map_add (F.res (opens.comap hf e1.U ∩ opens.comap hf e2.U) (opens.comap hf (e1.U ∩ e2.U))
          (set.subset_inter (opens.comap_mono _ _ _ (set.inter_subset_left _ _)) (opens.comap_mono _ _ _ (set.inter_subset_right _ _)))),
        ← presheaf.Hcomp', ← presheaf.Hcomp', ← presheaf.Hcomp', ← presheaf.Hcomp',
        m.commutes' e1.U (e1.U ∩ e2.U) (set.inter_subset_left _ _),
        m.commutes' e2.U (e1.U ∩ e2.U) (set.inter_subset_right _ _),
        is_ring_hom.map_add (m.map (e1.U ∩ e2.U))]; refl⟩ }

namespace locally_ringed_space

structure morphism {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  {Y : Type v} [topological_space Y] (OY : locally_ringed_space Y) extends morphism OX OY :=
(hom : ∀ U, is_ring_hom (fO.map U))
(hlocal : ∀ x s, is_unit (presheaf.fmap.stalk_of_rings fO x s) → is_unit s)
attribute [instance] morphism.hom

end locally_ringed_space

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
  stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis (D_fs_standard_basis R) (structure_presheaf_on_basis R) p →
  stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis (D_fs_standard_basis R)
    (presheaf_of_rings_to_presheaf_of_rings_on_basis
      (D_fs_standard_basis R) (presheaf_of_rings.pushforward (induced_continuous OX R f) OX.O.F) :
        presheaf_of_rings_on_basis (Spec R) (D_fs_basis R))
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

noncomputable def induced_sheafification {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type u) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f]
  (U : topological_space.opens (Spec R)) (s : (Spec.locally_ringed_space R).O U) :
  ((presheaf_of_rings_to_presheaf_of_rings_on_basis
      (D_fs_standard_basis R)
      (OX.O.pushforward (induced_continuous OX R f)).F :
    presheaf_of_rings_on_basis (Spec R) (D_fs_basis R))ᵣₑₓₜ (D_fs_standard_basis R)) U :=
⟨λ x hxU, induced_stalk OX R f x (s.1 x hxU),
λ x hxU, let ⟨V, HVB, hxV, s1, hs1⟩ := s.2 x hxU in
⟨V, HVB, hxV, induced_basis OX R f V HVB s1, λ g hg, funext $ λ hgU, by rw hs1 g hg; refl⟩⟩

instance is_ring_hom_induced_basis (U : topological_space.opens $ Spec R) (HUB : U ∈ D_fs R) :
  is_ring_hom (induced_basis OX R f U HUB) :=
localization.lift.is_ring_hom _ _

theorem induced_basis_res (U V : topological_space.opens $ Spec R) (HUB : U ∈ D_fs R) (HVB : V ∈ D_fs R) (HVU : V ⊆ U)
  (s : ((structure_presheaf_on_basis R).to_presheaf_on_basis).F HUB) :
  induced_basis OX R f V HVB (presheaf_on_basis.res _ HUB HVB HVU s) =
  OX.O.F.res (opens.comap (induced_continuous OX R f) U) (opens.comap (induced_continuous OX R f) V)
    (opens.comap_mono _ _ _ HVU) (induced_basis OX R f U HUB s) :=
suffices induced_basis OX R f V HVB ∘ presheaf_on_basis.res _ HUB HVB HVU =
  OX.O.F.res (opens.comap (induced_continuous OX R f) U) (opens.comap (induced_continuous OX R f) V)
    (opens.comap_mono _ _ _ HVU) ∘ induced_basis OX R f U HUB, from congr_fun this s,
localization.funext _ _ $ λ x, show localization.lift (OX.O.F.res ⊤ (opens.comap _ V) _ ∘ f ∘ to_Spec_top R) _ ↑x =
  OX.O.F.res (opens.comap _ U) (opens.comap _ V) _ (localization.lift (OX.O.F.res ⊤ (opens.comap _ U) _ ∘ f ∘ to_Spec_top R) _ ↑x),
by rw [localization.lift_coe, localization.lift_coe, ← presheaf.Hcomp']; refl

instance is_ring_hom_induced_stalk (p : Spec R) :
  is_ring_hom (induced_stalk OX R f p) :=
{ map_one := congr_arg quotient.mk (congr_arg (stalk_on_basis.elem.mk _ _ _) (by exact is_ring_hom.map_one (induced_basis _ _ _ _ _))),
  map_mul := λ x y, quotient.induction_on₂ x y $ λ s t, congr_arg quotient.mk
    (congr_arg (stalk_on_basis.elem.mk _ _ _) (by exact (is_ring_hom.map_mul (induced_basis _ _ _ _ _)).trans
      (by rw [induced_basis_res, induced_basis_res]; refl))),
  map_add := λ x y, quotient.induction_on₂ x y $ λ s t, congr_arg quotient.mk
    (congr_arg (stalk_on_basis.elem.mk _ _ _) (by exact (is_ring_hom.map_add (induced_basis _ _ _ _ _)).trans
      (by rw [induced_basis_res, induced_basis_res]; refl))) }

instance is_ring_hom_induced_sheafification {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type u) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f]
  (U : topological_space.opens (Spec R)) :
  is_ring_hom (induced_sheafification OX R f U) :=
{ map_one := subtype.eq $ funext $ λ x, funext $ λ hxU, by exact is_ring_hom.map_one (induced_stalk OX R f x),
  map_mul := λ x y, subtype.eq $ funext $ λ p, funext $ λ hpU, by change induced_stalk _ _ _ _ _ = _ * _;
    rw [Fext_mul.eq, is_ring_hom.map_mul (induced_stalk OX R f p)],
  map_add := λ x y, subtype.eq $ funext $ λ p, funext $ λ hpU, by change induced_stalk _ _ _ _ _ = _ + _;
    rw [Fext_add.eq, is_ring_hom.map_add (induced_stalk OX R f p)] }

theorem to_stalk_res {X : Type u} [topological_space X] (F : presheaf_of_rings X) (x : X)
  (U V : topological_space.opens X) (hxU : x ∈ U) (hxV : x ∈ V) (HVU : V ⊆ U) (s : F U) :
  to_stalk F x V hxV (F.res U V HVU s) = to_stalk F x U hxU s :=
quotient.sound ⟨V, hxV, set.subset.refl V, HVU, (presheaf.Hcomp' _ _ _ _ _ _ _).symm⟩

theorem is_unit_to_stalk {X : Type u} [topological_space X] (F : presheaf_of_rings X) (x : X)
  (U : topological_space.opens X) (hxU : x ∈ U) (s : F U) :
  is_unit (to_stalk F x U hxU s) ↔
  ∃ V : topological_space.opens X, ∃ hxV : x ∈ V, ∃ HVU : V ⊆ U, is_unit (F.res U V HVU s) :=
⟨λ hu, let ⟨t, ht⟩ := is_unit_iff_exists_inv.1 hu in quotient.induction_on t (λ ⟨V, hxV, τ⟩ H,
let ⟨W, hxW, HWUV, HWtop, HW⟩ := quotient.exact H in ⟨W, hxW, set.subset.trans HWUV (set.inter_subset_left _ _),
is_unit_iff_exists_inv.2 ⟨F.res V W (set.subset.trans HWUV (set.inter_subset_right _ _)) τ,
by dsimp only at HW; rw [res_mul, ← presheaf.Hcomp', ← presheaf.Hcomp'] at HW; exact HW.trans (res_one _ _ _ _)⟩⟩) ht,
λ ⟨V, hxV, HVU, hv⟩, hv.map' (to_stalk F x V hxV) _ (to_stalk_res _ _ _ _ _ _ _ _)⟩

section presheaf_of_rings_extension

instance to_presheaf_of_rings_extension.is_ring_hom' {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB)
  {U : topological_space.opens α} (BU : U ∈ B)
: is_ring_hom (to_presheaf_of_rings_extension Bstd F BU) :=
{ map_one := 
    begin
      apply subtype.eq,
      funext x Hx,
      apply quotient.sound,
      use [U, BU, Hx, set.subset.refl _, set.subset_univ _],
      iterate 2 { erw (F.res_is_ring_hom _ _ _).map_one, },
    end,
  map_mul := 
    begin
      intros x y,
      apply subtype.eq,
      funext z Hz,
      apply quotient.sound,
      use [U, BU, Hz], 
      use [set.subset.refl _, set.subset_inter (set.subset.refl _) (set.subset.refl _)],
      erw ←(F.res_is_ring_hom _ _ _).map_mul,
      erw ←presheaf_on_basis.Hcomp',
      refl
    end,
  map_add := 
    begin
      intros x y,
      apply subtype.eq,
      funext z Hz,
      apply quotient.sound,
      use [U, BU, Hz], 
      use [set.subset.refl _, set.subset_inter (set.subset.refl _) (set.subset.refl _)],
      erw ←(F.res_is_ring_hom _ _ _).map_add,
      erw ←presheaf_on_basis.Hcomp',
      refl
    end, }

theorem res_to_presheaf_of_rings_extension {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB) (U V : topological_space.opens α) (HUB : U ∈ B) (HVB : V ∈ B) (HVU : V ⊆ U) (σ : F.F HUB) :
  presheaf.res _ U V HVU (to_presheaf_of_rings_extension Bstd F HUB σ) =
  to_presheaf_of_rings_extension Bstd F HVB (F.res HUB HVB HVU σ) :=
subtype.eq $ funext $ λ x, funext $ λ hxV, quotient.sound ⟨V, HVB, hxV, HVU, set.subset.refl V, presheaf_on_basis.Hcomp' _ _ _ _ _ _ _⟩

noncomputable def to_presheaf_of_rings_extension.ring_equiv {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB) 
  (HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
  {U : topological_space.opens α} (HUB : U ∈ B) :
  F.F HUB ≃r (F ᵣₑₓₜ Bstd).F U :=
ring_equiv.mk
  (equiv.of_bijective (to_presheaf_of_rings_extension.bijective Bstd F HF HUB))
  (to_presheaf_of_rings_extension.is_ring_hom Bstd F HF HUB)

noncomputable def of_presheaf_of_rings_extension {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB) 
  (HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
  {U : topological_space.opens α} (HUB : U ∈ B) :
  (F ᵣₑₓₜ Bstd).F U → F.F HUB :=
(to_presheaf_of_rings_extension.ring_equiv HB Bstd F HF HUB).symm.to_fun

instance of_presheaf_of_rings_extension.is_ring_hom {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB) 
  (HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
  {U : topological_space.opens α} (HUB : U ∈ B) :
  is_ring_hom (of_presheaf_of_rings_extension HB Bstd F HF HUB) :=
(to_presheaf_of_rings_extension.ring_equiv HB Bstd F HF HUB).symm.hom

theorem of_to_presheaf_of_rings_extension {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB) 
  (HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
  {U : topological_space.opens α} (HUB : U ∈ B) (σ : F.F HUB) :
  of_presheaf_of_rings_extension HB Bstd F HF HUB (to_presheaf_of_rings_extension Bstd F HUB σ) = σ :=
equiv.symm_apply_apply _ _

theorem to_of_presheaf_of_rings_extension {α : Type u} [topological_space α]
  {B : set (topological_space.opens α)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis α HB) 
  (HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
  {U : topological_space.opens α} (HUB : U ∈ B) (σ : (F ᵣₑₓₜ Bstd) U) :
  to_presheaf_of_rings_extension Bstd F HUB (of_presheaf_of_rings_extension HB Bstd F HF HUB σ) = σ :=
equiv.apply_symm_apply (to_presheaf_of_rings_extension.ring_equiv HB Bstd F HF HUB).to_equiv σ

end presheaf_of_rings_extension

theorem is_unit_localization_mk {R : Type u} [comm_ring R] {S : set R} [is_submonoid S]
  (r : R) (s : S) : is_unit (localization.mk r s) ↔ ∃ t, r * t ∈ S :=
begin
  rw is_unit_iff_exists_inv, split,
  { intros hu, cases hu with w hu, revert hu,
    refine localization.induction_on w (λ r2 s2 hu, _),
    rcases quotient.exact hu with ⟨t, hts, ht⟩,
    change (s.1 * s2.1 * 1 - 1 * (r * r2)) * t = 0 at ht,
    rw [mul_one, one_mul, sub_mul, sub_eq_zero_iff_eq] at ht,
    refine ⟨r2 * t, _⟩, rw [← mul_assoc, ← ht], exact (s * s2 * ⟨t, hts⟩).2 },
  { rintros ⟨t, hrt⟩, refine ⟨localization.mk (s.1 * t) ⟨r * t, hrt⟩, quotient.sound $ localization.r_of_eq _⟩,
    change (s.1 * (r * t)) * 1 = 1 * (r * (s.val * t)), rw [mul_one, one_mul, mul_left_comm] }
end

theorem is_unit_to_stalk_affine (p : Spec R)
  (U : topological_space.opens (Spec R)) (HUB : U ∈ D_fs R) (hpU : p ∈ U) (σ : (structure_presheaf_on_basis R).F HUB) :
  is_unit (to_stalk (Spec.locally_ringed_space R).O.F p U hpU (to_presheaf_of_rings_extension _ _ HUB σ)) ↔
  ∃ r : R, ∃ s : S U, p ∈ Spec.D' r ∧ localization.mk r s = σ :=
begin
  rw is_unit_to_stalk, split,
  { rintros ⟨V, hpV, HVU, hv⟩,
    rcases topological_space.opens.is_basis_iff_nbhd.1 (D_fs_basis R) hpV with ⟨W, HWB, hpW, HWV⟩,
    have := hv.map (presheaf.res _ V W HWV), rw ← presheaf.Hcomp' at this,
    dsimp only [Spec.locally_ringed_space, structure_sheaf, structure_sheaf.presheaf] at this,
    rw [res_to_presheaf_of_rings_extension _ _ _ _ _ HUB HWB] at this,
    replace this := this.map (of_presheaf_of_rings_extension (D_fs_basis R) (D_fs_standard_basis R)
      (structure_presheaf_on_basis R) structure_presheaf_on_basis_is_sheaf_on_basis HWB),
    rw of_to_presheaf_of_rings_extension at this, revert this, refine localization.induction_on σ (λ r s this, _),
    change is_unit (localization.mk r ⟨s.1, _⟩) at this, rw is_unit_localization_mk at this, cases this with t hrt,
    change W.1 ⊆ Spec.D' (r * t) at hrt, rw Spec.D'.product_eq_inter at hrt,
    refine ⟨r, s, (hrt hpW).1, rfl⟩ },
  { rintros ⟨r, s, hrp, rfl⟩, refine ⟨U ∩ Spec.DO R r, ⟨hpU, hrp⟩, set.inter_subset_left _ _, _⟩,
    dsimp only [Spec.locally_ringed_space, structure_sheaf, structure_sheaf.presheaf],
    rw res_to_presheaf_of_rings_extension _ _ _ _ _ _ ((D_fs_standard_basis R).2 HUB (D_fs.mem R r)),
    refine is_unit.map _ _, rw is_unit_iff_exists_inv, refine ⟨localization.mk s.1 ⟨r, set.inter_subset_right _ _⟩, _⟩,
    change localization.mk r ⟨s.1, _⟩ * localization.mk s.1 ⟨r, _⟩ = _,
    rw [localization.mk_mul_mk, mul_comm], exact localization.mk_self }
end

theorem is_unit_to_stalk_on_basis {X : Type u} [topological_space X]
  {B : set (topological_space.opens X)} (HB : topological_space.opens.is_basis B) (Bstd)
  (F : presheaf_of_rings_on_basis X HB)
  (p : X) (U : topological_space.opens X) (hpU : p ∈ U) (σ : (F ᵣₑₓₜ Bstd) U) :
  is_unit (to_stalk (F ᵣₑₓₜ Bstd) p U hpU σ) ↔
  @is_unit (stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis Bstd F p) _ (σ.1 p hpU) :=
begin
  rw is_unit_to_stalk, split,
  { rintros ⟨W, hpW, HWU, HW⟩, rcases is_unit_iff_exists_inv.1 HW with ⟨τ, hστ⟩,
    refine is_unit_iff_exists_inv.2 ⟨τ.1 p hpW, _⟩,
    replace hστ := congr_arg subtype.val hστ,
    replace hστ := congr_fun (congr_fun hστ p) hpW,
    rwa Fext_mul.eq at hστ },
  { rcases σ.2 p hpU with ⟨V, HVB, hpV, σ2, HV⟩, rw HV p ⟨hpU, hpV⟩, dsimp only, rintros hu,
    rcases is_unit_iff_exists_inv.1 hu with ⟨e, he⟩, revert he, refine quotient.induction_on e (λ τ hστ, _),
    rcases quotient.exact hστ with ⟨S, HSB, hpS, HSVτ, HStop, HS⟩, dsimp only at HS,
    rcases topological_space.opens.is_basis_iff_nbhd.1 HB (show p ∈ S ∩ U, from ⟨hpS, hpU⟩) with ⟨T, HTB, hpT, HTSU⟩,
    have HTS : T ⊆ S := set.subset.trans HTSU (set.inter_subset_left _ _),
    have HTτ : T ⊆ τ.U := set.subset.trans HTS (set.subset.trans HSVτ (set.inter_subset_right _ _)),
    refine ⟨T, hpT, set.subset.trans HTSU (set.inter_subset_right _ _), is_unit_iff_exists_inv.2
      ⟨⟨λ q hqT, ⟦⟨T, HTB, hqT, F.res τ.BU HTB HTτ τ.s⟩⟧, λ q hqT, ⟨T, HTB, hqT, F.res τ.BU HTB HTτ τ.s, λ _ _, rfl⟩⟩, _⟩⟩,
    replace HS := congr_arg (F.res HSB HTB HTS) HS,
    refine subtype.eq (funext $ λ x, funext $ λ hxT, _), rw Fext_mul.eq,
    change (σ.1 x _ * _ : stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis Bstd F x) = 1,
    rw HV x ⟨(HTSU hxT).2, (HSVτ $ HTS hxT).1⟩,
    refine quotient.sound ⟨T, HTB, hxT, set.subset_inter (set.subset.trans HTS (set.subset.trans HSVτ (set.inter_subset_left _ _)))
      (set.subset.refl T), set.subset_univ _, _⟩,
    dsimp only, rw bres_mul at HS ⊢, rw bres_mul at HS,
    repeat { rw ← presheaf_on_basis.Hcomp' at HS }, repeat { rw ← presheaf_on_basis.Hcomp' }, exact HS }
end

def of_pushforward_stalk {α : Type u} [topological_space α]
  {β : Type u} [topological_space β]
  {f : α → β} (hf : continuous f) (F : presheaf_of_rings α) (p : α) :
  stalk_of_rings (presheaf_of_rings.pushforward hf F) (f p) → stalk_of_rings F p :=
presheaf.fmap.stalk_of_rings ⟨λ U, id, λ U V HVU, rfl⟩ p

instance is_ring_hom_of_pushforward_stalk {α : Type u} [topological_space α]
  {β : Type u} [topological_space β]
  {f : α → β} (hf : continuous f) (F : presheaf_of_rings α) (p : α) :
  is_ring_hom (of_pushforward_stalk hf F p) :=
is_ring_hom_stalk_of_rings _ _

theorem presheafasdf {α : Type u} [topological_space α]
  {β : Type u} [topological_space β]
  {f : α → β} (hf : continuous f) (F : presheaf_of_rings α) (G : presheaf_of_rings β)
  (m : presheaf_of_rings.fmap hf F G) (p : α) (σ) :
  presheaf.fmap.stalk_of_rings m p σ =
  of_pushforward_stalk hf F p
    (presheaf.fmap.stalk_of_rings
      (⟨m.map, m.commutes⟩ : presheaf_of_rings.fmap continuous_id (presheaf_of_rings.pushforward hf F) G)
      (f p)
      σ) :=
quotient.induction_on σ $ λ e, rfl

@[simp] lemma localization.lift_mul {α : Type u} [comm_ring α] {S : set α} [is_submonoid S]
  {β : Type v} [comm_ring β] (f : α → β) [is_ring_hom f] (H) (x y : localization α S) :
  localization.lift f H (x * y) = localization.lift f H x * localization.lift f H y :=
is_ring_hom.map_mul _

/- https://stacks.math.columbia.edu/tag/01I1 -/
noncomputable def hom_to_mor {X : Type u} [topological_space X] (OX : locally_ringed_space X)
  (R : Type u) [comm_ring R]
  (f : (Spec.locally_ringed_space R).O ⊤ → OX.O ⊤) [is_ring_hom f] :
  OX.morphism (Spec.locally_ringed_space R) :=
{ f := induced OX R f,
  Hf := induced_continuous OX R f,
  fO :=
  { map := λ U s, (sheaf_of_rings.of_extension (D_fs_basis R)
      (D_fs_standard_basis R) _ _
      (induced_sheafification OX R f U s) :
      OX.O.pushforward (induced_continuous OX R f) U),
    commutes := λ U V HVU, funext $ λ s, begin
      dsimp only [function.comp_apply],
      change _ = (sheaf_of_rings.pushforward _ (OX.O)).F.res _ _ _ _,
      rw ← sheaf_of_rings.of_extension_res, refl
    end },
  hom := λ U, @is_ring_hom.comp _ _ _ _ _ (is_ring_hom_induced_sheafification OX R f U) _ _ _ _,
  hlocal := λ p s, quotient.induction_on s $ λ e he, begin
    cases e with U hpU σ, generalize hσ : σ.1 (induced OX R f p) hpU = t,
    revert hσ, refine quotient.induction_on t (λ τ, _), cases τ with V HVB hpV τ,
    refine localization.induction_on τ (λ r s hu, _),
    rw presheafasdf at he,
    change is_unit (of_pushforward_stalk (induced_continuous OX R f) OX.O.F p
      (to_stalk (OX.O.pushforward (induced_continuous OX R f)).F (induced OX R f p) U hpU
        (sheaf_of_rings.of_extension _ _ (OX.O.pushforward (induced_continuous OX R f)) U (induced_sheafification OX R f U σ) :
          OX.O.pushforward (induced_continuous OX R f) U))) at he,
    rw sheaf_of_rings.to_stalk_of_extension at he,
    dsimp only [induced_sheafification] at he,
    change σ.val (induced OX R f p) hpU = _ at hu,
    rw hu at he,
    change is_unit (of_pushforward_stalk (induced_continuous OX R f) OX.O.F p
      (to_stalk (OX.O.pushforward (induced_continuous OX R f)).F (induced OX R f p) V hpV
        (localization.lift
          (OX.O.F.to_presheaf.res ⊤ (opens.comap (induced_continuous OX R f) V) (set.subset_univ _) ∘ f ∘ to_Spec_top R)
          (induced_basis._proof_3 OX R f V)
          (localization.mk r s)))) at he,
    rw [localization.mk_eq, localization.lift_mul, localization.lift_coe,
        is_ring_hom.map_mul (to_stalk (OX.O.pushforward (induced_continuous OX R f)).F (induced OX R f p) V hpV),
        is_ring_hom.map_mul (of_pushforward_stalk (induced_continuous OX R f) OX.O.F p)] at he,
    replace he := is_unit_of_mul_is_unit_left he,
    change is_unit (to_stalk OX.O.F p (opens.comap (induced_continuous OX R f) V) hpV
      (OX.O.F.to_presheaf.res ⊤ (opens.comap (induced_continuous OX R f) V) (set.subset_univ _)
        (f (to_Spec_top R r)))) at he,
    rw to_stalk_res _ p ⊤ _ trivial at he,
    change p ∈ (OX.D (f (to_Spec_top R r)) : set X) at he,
    rw ← induced_preimage_D' at he,
    refine (is_unit_to_stalk_on_basis _ _ _ _ _ _ _).2 _, rw hu,
    refine is_unit_iff_exists_inv.2 ⟨⟦⟨V ∩ Spec.DO R r, (D_fs_standard_basis R).2 HVB (D_fs.mem _ _), ⟨hpV, he⟩,
      localization.mk s.1 ⟨r, set.inter_subset_right _ _⟩⟩⟧, quotient.sound ⟨V ∩ Spec.DO R r,
      (D_fs_standard_basis R).2 HVB (D_fs.mem _ _), ⟨hpV, he⟩, set.subset_inter (set.inter_subset_left _ _) (set.subset.refl _),
      set.subset_univ _, _⟩⟩,
    change localization.mk (r * s.1) ⟨s.1 * r, _⟩ = 1,
    rw mul_comm, exact localization.mk_self
  end }

end tag01I1
