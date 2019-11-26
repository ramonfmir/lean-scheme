/-
  Extension of a sheaf of rings on the basis to a sheaf of rings on the whole space.

  https://stacks.math.columbia.edu/tag/009M
  https://stacks.math.columbia.edu/tag/009N
-/

import topology.opens
import sheaves.stalk_of_rings
import sheaves.stalk_of_rings_on_standard_basis
import sheaves.presheaf_of_rings_on_basis
import sheaves.presheaf_of_rings_extension
import sheaves.sheaf_on_basis
import sheaves.sheaf_on_standard_basis
import sheaves.sheaf_of_rings

open topological_space classical

noncomputable theory

universe u

section presheaf_of_rings_extension

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α)} {HB : opens.is_basis B}
variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

include Bstd

theorem extension_is_sheaf_of_rings 
(F : presheaf_of_rings_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis)
: is_sheaf_of_rings (F ᵣₑₓₜ Bstd) := 
begin
  show is_sheaf (F ᵣₑₓₜ Bstd).to_presheaf,
  constructor,
  { intros U OC s t Hres,
    apply subtype.eq,
    apply funext,
    intros x,
    apply funext,
    intros HxU,
    rw OC.Hcov.symm at HxU,
    rcases HxU with ⟨Uj1, ⟨⟨⟨Uj2, OUj⟩, ⟨⟨j, HUj⟩, Heq⟩⟩, HxUj⟩⟩,
    rcases Heq, rcases Heq,
    have Hstj := congr_fun (subtype.mk_eq_mk.1 (Hres j)),
    have HxUj1 : x ∈ OC.Uis j := HUj.symm ▸ HxUj,
    have Hstjx := congr_fun (Hstj x) HxUj1,
    exact Hstjx, },
  { intros U OC s Hsec,
    existsi (global_section (F.to_presheaf_on_basis) U OC s Hsec),
    intros i,
    apply subtype.eq,
    apply funext,
    intros x,
    apply funext,
    intros HxUi,
    have HxU : x ∈ U := OC.Hcov ▸ (opens_supr_subset OC.Uis i) HxUi,
    let HyUi := λ t, ∃ (H : t ∈ set.range OC.Uis), x ∈ t,
    dunfold presheaf_of_rings_extension; dsimp,
    dunfold global_section; dsimp,
    -- Same process of dealing with subtype.rec.
    let HyUi := λ t, ∃ (H : t ∈ subtype.val '' set.range OC.Uis), x ∈ t,
    rcases (classical.indefinite_description HyUi _) with ⟨S, HS⟩; dsimp,
    let HyS := λ H : S ∈ subtype.val '' set.range OC.Uis, x ∈ S,
    rcases (classical.indefinite_description HyS HS) with ⟨HSUiR, HySUiR⟩; dsimp,
    let HOUksub := λ t : subtype is_open, t ∈ set.range (OC.Uis) ∧ t.val = S,
    rcases (classical.indefinite_description HOUksub _) with ⟨OUl, ⟨HOUl, HOUleq⟩⟩; dsimp,
    let HSUi := λ i, OC.Uis i = OUl,
    cases (classical.indefinite_description HSUi _) with l HSUil; dsimp,
    -- Now we just need to apply Hsec in the right way.
    dunfold presheaf_of_rings_extension at Hsec,
    dunfold res_to_inter_left at Hsec,
    dunfold res_to_inter_right at Hsec,
    dsimp at Hsec,
    replace Hsec := Hsec i l,
    rw subtype.ext at Hsec,
    dsimp at Hsec,
    replace Hsec := congr_fun Hsec x,
    dsimp at Hsec,
    replace Hsec := congr_fun Hsec,
    have HxOUk : x ∈ OUl.val := HOUleq.symm ▸ HySUiR,
    have HxUl : x ∈ OC.Uis l := HSUil.symm ▸ HxOUk,
    exact (Hsec ⟨HxUi, HxUl⟩).symm, },
  end

section extension_coincides

-- The extension is done in a way that F(U) ≅ Fext(U).

-- The map ψ : F(U) → Π x ∈ U, Fx

def to_stalk_product (F : presheaf_on_basis α HB) {U : opens α} (BU : U ∈ B)
: F.F BU → Π (x ∈ U), stalk_on_basis F x :=
λ s x Hx, ⟦{U := U, BU := BU, Hx := Hx, s := s}⟧

lemma to_stalk_product.injective 
(F : presheaf_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F)
{U : opens α} (BU : U ∈ B)
: function.injective (to_stalk_product Bstd F BU) :=
begin
  intros s₁ s₂ Hs,
  have Hsx := λ (HxU : U), congr_fun (congr_fun Hs HxU.1) HxU.2,
  let OC : covering_standard_basis B U :=
  { γ := U,
    Uis := λ HxU, some (quotient.eq.1 (Hsx HxU)),
    BUis := λ HxU, some (some_spec (quotient.eq.1 (Hsx HxU))),
    Hcov := 
      begin
        ext z,
        split,
        { rintros ⟨Ui, ⟨⟨OUi, ⟨⟨i, HUi⟩, HUival⟩⟩, HzUi⟩⟩,
          rw [←HUival, ←HUi] at HzUi,
          exact some (some_spec (some_spec (some_spec (quotient.eq.1 (Hsx i))))) HzUi, },
        { intros Hz,
          use [(some (quotient.eq.1 (Hsx ⟨z, Hz⟩))).val],
          have Hin : (some (quotient.eq.1 (Hsx ⟨z, Hz⟩))).val 
            ∈ subtype.val '' set.range (λ (HxU : U), some ((quotient.eq.1 (Hsx HxU)))),
            use [classical.some ((quotient.eq.1 (Hsx ⟨z, Hz⟩)))],
            split,
            { use ⟨z, Hz⟩, },
            { refl, },
          use Hin,
          exact some (some_spec (some_spec (quotient.eq.1 (Hsx ⟨z, Hz⟩)))), },
      end, },
  apply (HF BU OC).1,
  intros i,
  replace Hs := congr_fun (congr_fun Hs i.1) i.2,
  exact some_spec (some_spec (some_spec (some_spec (some_spec (quotient.eq.1 (Hsx i)))))),
end

-- The map φ : F(U) → im(ψ).

def to_presheaf_of_rings_extension (F : presheaf_of_rings_on_basis α HB) {U : opens α} (BU : U ∈ B)
: F.F BU → (F ᵣₑₓₜ Bstd).F U :=
λ s,
  ⟨to_stalk_product Bstd F.to_presheaf_on_basis BU s,
   λ x Hx, ⟨U, BU, Hx, s, λ y Hy, funext $ λ Hy', 
   quotient.sound $ ⟨U, BU, Hy', set.subset.refl U, set.subset.refl U, rfl⟩⟩⟩

lemma to_presheaf_of_rings_extension.injective 
(F : presheaf_of_rings_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
{U : opens α} (BU : U ∈ B)
: function.injective (to_presheaf_of_rings_extension Bstd F BU) :=
begin
  intros s₁ s₂ Hs,
  erw subtype.mk_eq_mk at Hs,
  have Hinj := to_stalk_product.injective Bstd F.to_presheaf_on_basis (λ V BV OC, HF BV OC) BU,
  exact Hinj Hs,
end

lemma to_presheaf_of_rings_extension.surjective 
(F : presheaf_of_rings_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
{U : opens α} (BU : U ∈ B)
: function.surjective (to_presheaf_of_rings_extension Bstd F BU) :=
begin
  intros s,
  let V := λ (HxU : U), some (s.2 HxU.1 HxU.2),
  let BV := λ (HxU : U), some (some_spec (s.2 HxU.1 HxU.2)),
  let HxV := λ (HxU : U), some (some_spec (some_spec (s.2 HxU.1 HxU.2))),
  let σ := λ (HxU : U), some (some_spec (some_spec (some_spec (s.2 HxU.1 HxU.2)))),
  let Hσ := λ (HxU : U), some_spec (some_spec (some_spec (some_spec (s.2 HxU.1 HxU.2)))),
  let OC : covering_standard_basis B U :=
  { γ := U,
    Uis := λ HxU, (V HxU) ∩ U,
    BUis := λ HxU, Bstd.2 (BV HxU) BU,
    Hcov := 
      begin
        ext z,
        split,
        { rintros ⟨Ui, ⟨⟨OUi, ⟨⟨i, HUi⟩, HUival⟩⟩, HzUi⟩⟩,
          rw [←HUival, ←HUi] at HzUi,
          exact HzUi.2, },
        { intros Hz,
          use [(some (s.2 z Hz) ∩ U).val],
          have Hin : (some (s.2 z Hz) ∩ U).val 
            ∈ subtype.val '' set.range (λ (HxU : U), ((some (s.2 HxU.1 HxU.2) ∩ U : opens α))),
            use [(some (s.2 z Hz) ∩ U : opens α)],
            split,
            { use ⟨z, Hz⟩, },
            { refl, },
          use Hin,
          exact ⟨some (some_spec (some_spec (s.2 z Hz))), Hz⟩, },
      end, },
  -- Now let's try to apply sheaf condition.
  let res := λ (HxU : OC.γ), F.res (BV HxU) (Bstd.2 (BV HxU) BU) (set.inter_subset_left _ _),
  let sx := λ (HxU : OC.γ), res HxU (σ HxU),
  have Hglue := (HF BU OC).2 sx,
  have Hsx : ∀ j k, 
    sheaf_on_standard_basis.res_to_inter_left Bstd F.to_presheaf_on_basis (OC.BUis j) (OC.BUis k) (sx j) =
    sheaf_on_standard_basis.res_to_inter_right Bstd F.to_presheaf_on_basis (OC.BUis j) (OC.BUis k) (sx k), 
    intros j k,
    dsimp only [sheaf_on_standard_basis.res_to_inter_left],
    dsimp only [sheaf_on_standard_basis.res_to_inter_right],
    dsimp only [sx, res],
    iterate 2 { rw ←presheaf_on_basis.Hcomp', },
    show (F.to_presheaf_on_basis).res (BV j) (Bstd.2 (OC.BUis j) (OC.BUis k)) _ (σ j) 
       = (F.to_presheaf_on_basis).res (BV k) (Bstd.2 (OC.BUis j) (OC.BUis k)) _ (σ k),
    -- We can cover the U ∩ Vj ∩ Vk and use locality.
    -- But first let's check that all the stalks coincide in the intersectons.
    have Hstalks : ∀ {y} (Hy : y ∈ (OC.Uis j) ∩ (OC.Uis k)),
        (⟦{U := V j, BU := BV j, Hx := Hy.1.1, s := σ j}⟧ : stalk_on_basis F.to_presheaf_on_basis y)
      = ⟦{U := V k, BU := BV k, Hx := Hy.2.1, s := σ k}⟧,
      intros y Hy,
      have Hj := congr_fun (Hσ j y ⟨Hy.1.2, Hy.1.1⟩) Hy.1.2; dsimp at Hj,
      have Hk := congr_fun (Hσ k y ⟨Hy.2.2, Hy.2.1⟩) Hy.2.2; dsimp at Hk,
      erw [←Hj, ←Hk],
    -- Therefore there exists Wjk where σj|Wjk = σk|Wjk. We will use these as a cover.
    let Ujk : opens α := (OC.Uis j) ∩ (OC.Uis k),
    let BUjk := Bstd.2 (OC.BUis j) (OC.BUis k),
    -- Again, all the information we will need but on Uj ∩ Uk.
    let Hjk := λ (HxUjk : Ujk), quotient.eq.1 (Hstalks HxUjk.2),
    let Wjk := λ (HxUjk : Ujk), some (Hjk HxUjk) ∩ U,
    let BWjk := λ (HxUjk : Ujk), Bstd.2 (some (some_spec (Hjk HxUjk))) BU,
    let HxWjk := λ (HxUjk : Ujk), some (some_spec (some_spec (Hjk HxUjk))),
    let HWjkUj := λ (HxUjk : Ujk), some (some_spec (some_spec (some_spec (Hjk HxUjk)))),
    let HWjkUk := λ (HxUjk : Ujk), some (some_spec (some_spec (some_spec (some_spec (Hjk HxUjk))))),
    let HWjk := λ (HxUjk : Ujk), some_spec (some_spec (some_spec (some_spec (some_spec (Hjk HxUjk))))),
    let OCjk : covering_standard_basis B ((OC.Uis j) ∩ (OC.Uis k)) :=
    { γ := Ujk,
      Uis := Wjk,
      BUis := BWjk,
      Hcov := 
        begin
          ext z,
          split,
          { rintros ⟨W, ⟨⟨OW, ⟨⟨i, HWi⟩, HWival⟩⟩, HzW⟩⟩,
            rw [←HWival, ←HWi] at HzW,
            have HzUj := (HWjkUj i) HzW.1,
            have HzUk := (HWjkUk i) HzW.1,
            exact ⟨⟨HzUj, HzW.2⟩, ⟨HzUk, HzW.2⟩⟩, },
          { intros Hz,
            use [(some (Hjk ⟨z, Hz⟩) ∩ U).val],
            have Hin : (some (Hjk ⟨z, Hz⟩) ∩ U).val 
              ∈ subtype.val '' set.range (λ (HxUjk : Ujk), ((some (Hjk HxUjk) ∩ U : opens α))),
              use [(some (Hjk ⟨z, Hz⟩) ∩ U : opens α)],
              split,
              { use ⟨z, Hz⟩, },
              { refl, },
            use Hin,
            have HzWjk := HxWjk ⟨z, Hz⟩,
            have HzU := Hz.1.2,
            exact ⟨HzWjk, HzU⟩, }
        end, },
    apply (HF BUjk OCjk).1,
    intros i,
    rw ←presheaf_on_basis.Hcomp',
    rw ←presheaf_on_basis.Hcomp',
    have Hres : 
        F.res (some (some_spec (Hjk i))) (BWjk i) (set.inter_subset_left _ _)
          (F.res (BV j) (some (some_spec (Hjk i))) (HWjkUj i) (σ j))
      = F.res (some (some_spec (Hjk i))) (BWjk i) (set.inter_subset_left _ _)
          (F.res (BV k) (some (some_spec (Hjk i))) (HWjkUk i) (σ k)),
      rw (HWjk i),
    rw ←presheaf_on_basis.Hcomp' at Hres,
    rw ←presheaf_on_basis.Hcomp' at Hres,
    use Hres,
  -- Ready to prove it.
  rcases (Hglue Hsx) with ⟨S, HS⟩,
  existsi S,
  apply subtype.eq,
  dsimp [to_presheaf_of_rings_extension],
  apply funext,
  intros x,
  dsimp [to_stalk_product],
  apply funext,
  intros Hx,
  replace HS := HS ⟨x, Hx⟩,
  dsimp [sx, res] at HS,
  rw Hσ ⟨x, Hx⟩,
  swap,
  { exact ⟨Hx, HxV ⟨x, Hx⟩⟩, },
  dsimp,
  apply quotient.sound,
  use [(V ⟨x, Hx⟩) ∩ U],
  use [Bstd.2 (BV ⟨x, Hx⟩) BU],
  use [⟨HxV ⟨x, Hx⟩, Hx⟩],
  use [set.inter_subset_right _ _],
  use [set.inter_subset_left _ _],
  dsimp,
  erw HS,
end

lemma to_presheaf_of_rings_extension.bijective
(F : presheaf_of_rings_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
{U : opens α} (BU : U ∈ B)
: function.bijective (to_presheaf_of_rings_extension Bstd F BU) :=
⟨to_presheaf_of_rings_extension.injective Bstd F (λ U BU OC, HF BU OC) BU,
to_presheaf_of_rings_extension.surjective Bstd F (λ U BU OC, HF BU OC) BU ⟩

-- We now that they are equivalent as sets. 
-- Now we to assert that they're isomorphic as rings. 
-- It suffices to show that it is a ring homomorphism.

lemma to_presheaf_of_rings_extension.is_ring_hom 
(F : presheaf_of_rings_on_basis α HB) 
{U : opens α} (BU : U ∈ B)
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
    end, }

lemma to_presheaf_of_rings_extension.ring_equiv
(F : presheaf_of_rings_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis) 
{U : opens α} (BU : U ∈ B)
: F BU ≃+* (presheaf_of_rings_extension Bstd F) U :=
begin
  have H := function.bijective_iff_has_inverse.1 (to_presheaf_of_rings_extension.bijective Bstd F @HF BU),
  rcases (classical.indefinite_description _ H) with ⟨inv, Hlinv, Hrinv⟩,
  use [(to_presheaf_of_rings_extension Bstd F BU), inv, Hlinv, Hrinv],
  { apply (to_presheaf_of_rings_extension.is_ring_hom Bstd F BU).map_mul, },
  { apply (to_presheaf_of_rings_extension.is_ring_hom Bstd F BU).map_add, }
end

-- Moreover, for all x, Fₓ ≅ Fextₓ.

-- We will need this to show that the stalks of the structure sheaf on
-- Spec(R) are local rings.

open stalk_of_rings_on_standard_basis

lemma to_stalk_extension
(F : presheaf_of_rings_on_basis α HB) 
(x : α)
: stalk_of_rings_on_standard_basis Bstd F x → stalk_of_rings (F ᵣₑₓₜ Bstd) x :=
begin
  intros BUs,
  let Us := quotient.out BUs,
  exact ⟦{U := Us.U, 
          HxU := Us.Hx, 
          s := (to_presheaf_of_rings_extension Bstd F Us.BU) Us.s}⟧,
end

lemma to_stalk_extension.injective 
(F : presheaf_of_rings_on_basis α HB) 
(x : α)
: function.injective (to_stalk_extension Bstd F x) :=
begin
  intros Us₁' Us₂', 
  apply quotient.induction_on₂ Us₁' Us₂',
  rintros Us₁ Us₂ HUs,
  rcases (quotient.mk_out Us₁) with ⟨W₁, BW₁, HxW₁, HW₁Us₁, HW₁U₁, Hres₁⟩,
  rcases (quotient.mk_out Us₂) with ⟨W₂, BW₂, HxW₂, HW₂Us₂, HW₂U₂, Hres₂⟩,
  dunfold to_stalk_extension at HUs,
  rw quotient.eq at HUs,
  rcases HUs with ⟨W, HxW, HWU₁, HWU₂, Hres⟩,
  dsimp at HWU₁,
  dsimp at HWU₂,
  dunfold to_presheaf_of_rings_extension at Hres,
  dunfold to_stalk_product at Hres,
  erw subtype.mk.inj_eq at Hres,
  replace Hres := congr_fun (congr_fun Hres x) HxW,
  dsimp at Hres,
  rw quotient.eq at Hres,
  rcases Hres with ⟨W₃, BW₃, HxW₃, HW₃U₁, HW₃U₂, Hres₃⟩,
  dsimp at HW₃U₁, 
  dsimp at HW₃U₂,
  dsimp at Hres₃,
  apply quotient.sound,
  have BW₁₂₃ : W₁ ∩ W₂ ∩ W₃ ∈ B := Bstd.2 (Bstd.2 BW₁ BW₂) BW₃,
  have HW₁₂₃U₁ : W₁ ∩ W₂ ∩ W₃ ⊆ Us₁.U := λ x Hx, HW₁U₁ Hx.1.1,
  have HW₁₂₃U₂ : W₁ ∩ W₂ ∩ W₃ ⊆ Us₂.U := λ x Hx, HW₂U₂ Hx.1.2,
  use [W₁ ∩ W₂ ∩ W₃, BW₁₂₃, ⟨⟨HxW₁, HxW₂⟩, HxW₃⟩, HW₁₂₃U₁, HW₁₂₃U₂],
  have HW₁W₁₂₃ : W₁ ∩ W₂ ∩ W₃ ⊆ W₁ := λ x Hx, Hx.1.1,
  have HW₂W₁₂₃ : W₁ ∩ W₂ ∩ W₃ ⊆ W₂ := λ x Hx, Hx.1.2,
  have HW₃W₁₂₃ : W₁ ∩ W₂ ∩ W₃ ⊆ W₃ := λ x Hx, Hx.2,
  replace Hres₁ := congr_arg (F.res BW₁ BW₁₂₃ HW₁W₁₂₃) Hres₁,
  replace Hres₂ := congr_arg (F.res BW₂ BW₁₂₃ HW₂W₁₂₃) Hres₂,
  replace Hres₃ := congr_arg (F.res BW₃ BW₁₂₃ HW₃W₁₂₃) Hres₃,
  iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₁, },
  iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₂, },
  iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₃, },
  erw [←Hres₁, ←Hres₂],
  exact Hres₃,
end

lemma to_stalk_extension.surjective 
(F : presheaf_of_rings_on_basis α HB) 
(x : α)
: function.surjective (to_stalk_extension Bstd F x) :=
begin
  intros Us',
  apply quotient.induction_on Us',
  rintros ⟨U, HxU, s⟩,
  rcases (s.2 x HxU) with ⟨V, BV, HxV, t, Ht⟩,
  let Vt : stalk_on_basis.elem (F.to_presheaf_on_basis) x 
    := {U := V, BU := BV, Hx := HxV, s := t},
  use ⟦Vt⟧,
  dunfold to_stalk_extension,
  apply quotient.sound,
  rcases (quotient.mk_out Vt) with ⟨W, BW, HxW, HWVtV, HWV, Hres⟩,
  have HUVWV : U ∩ V ∩ W ⊆ (quotient.out ⟦Vt⟧).U := λ x Hx, HWVtV Hx.2,
  have HUVWU : U ∩ V ∩ W ⊆ U := λ x Hx, Hx.1.1,
  use [U ∩ V ∩ W, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWV, HUVWU],
  apply subtype.eq,
  dsimp only [presheaf_of_rings_extension],
  dsimp only [to_presheaf_of_rings_extension],
  dsimp only [to_stalk_product],
  funext y Hy,
  rw (Ht y Hy.1),
  apply quotient.sound,
  have BVW : V ∩ W ∈ B := Bstd.2 BV BW,
  have HVWVtV : V ∩ W ⊆ (quotient.out ⟦Vt⟧).U := λ x Hx, HWVtV Hx.2,
  have HVWV : V ∩ W ⊆ V := λ x Hx, Hx.1,
  use [V ∩ W, BVW, ⟨Hy.1.2,Hy.2⟩, HVWVtV, HVWV],
  have HVWW : V ∩ W ⊆ W := λ x Hx, Hx.2,
  replace Hres := congr_arg (F.res BW BVW HVWW) Hres,
  iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres, },
  exact Hres,
end

lemma to_stalk_extension.bijective
(F : presheaf_of_rings_on_basis α HB) 
(x : α)
: function.bijective (to_stalk_extension Bstd F x) :=
⟨to_stalk_extension.injective Bstd F x,
to_stalk_extension.surjective Bstd F x⟩

lemma to_stalk_extension.is_ring_hom
(F : presheaf_of_rings_on_basis α HB) 
(x : α)
: is_ring_hom (to_stalk_extension Bstd F x) :=
{ map_one := 
    begin
      dunfold to_stalk_extension,
      let one.elem : stalk_on_basis.elem F.to_presheaf_on_basis x
        := {U := opens.univ, BU := Bstd.1, Hx := trivial, s:= 1},
      let one.stalk : stalk_of_rings_on_standard_basis Bstd F x := ⟦one.elem⟧,
      let one := quotient.out one.stalk,
      apply quotient.sound,
      rcases (quotient.mk_out one.elem) with ⟨W₁, BW₁, HxW₁, HW₁Uout, HW₁U, Hres₁⟩,
      have BUW₁ : one.U ∩ W₁ ∈ B := Bstd.2 one.BU BW₁,
      have HUUW₁ : one.U ∩ W₁ ⊆ one.U := set.inter_subset_left _ _,
      use [one.U ∩ W₁, ⟨one.Hx, HxW₁⟩, HUUW₁, set.subset_univ _],
      apply subtype.eq,
      dsimp only [presheaf_of_rings_extension],
      dsimp only [to_presheaf_of_rings_extension],
      dsimp only [to_stalk_product],
      funext z Hz,
      apply quotient.sound,
      use [one.U ∩ W₁, BUW₁, Hz, set.inter_subset_left _ _, set.subset_univ _],
      dsimp,
      have HUW₁W₁ : one.U ∩ W₁ ⊆ W₁ := set.inter_subset_right _ _,
      replace Hres₁ := congr_arg (F.res BW₁ BUW₁ HUW₁W₁) Hres₁,
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₁, },
      exact Hres₁,
    end,
  map_mul := 
    begin
      intros y z,
      apply quotient.induction_on₂ y z,
      intros Us₁ Us₂,
      simp,
      let Us₃ : stalk_on_basis.elem F.to_presheaf_on_basis x :=
        { U := Us₁.U ∩ Us₂.U, 
          BU := Bstd.2 Us₁.BU Us₂.BU,
          Hx := ⟨Us₁.Hx, Us₂.Hx⟩, 
          s :=  F.res Us₁.BU _ (set.inter_subset_left _ _) Us₁.s * 
                F.res Us₂.BU _ (set.inter_subset_right _ _) Us₂.s },
      dunfold to_stalk_extension,
      apply quotient.sound,
      rcases (quotient.mk_out Us₁) with ⟨W₁, BW₁, HxW₁, HW₁U₁out, HW₁U₁, Hres₁⟩,
      rcases (quotient.mk_out Us₂) with ⟨W₂, BW₂, HxW₂, HW₂U₂out, HW₂U₂, Hres₂⟩,
      rcases (quotient.mk_out Us₃) with ⟨W₃, BW₃, HxW₃, HW₃U₃out, HW₃U₃, Hres₃⟩,
      let W := W₁ ∩ W₂ ∩ W₃,
      have HxW : x ∈ W := ⟨⟨HxW₁, HxW₂⟩, HxW₃⟩,
      have HWW₁ : W ⊆ W₁ := λ x Hx, Hx.1.1,
      have HWW₂ : W ⊆ W₂ := λ x Hx, Hx.1.2,
      have HWW₃ : W ⊆ W₃ := λ x Hx, Hx.2,
      have HWU₁out : W ⊆ (quotient.out ⟦Us₁⟧).U := set.subset.trans HWW₁ HW₁U₁out,
      have HWU₂out : W ⊆ (quotient.out ⟦Us₂⟧).U := set.subset.trans HWW₂ HW₂U₂out,
      have HWU₃out : W ⊆ (quotient.out ⟦Us₃⟧).U := set.subset.trans HWW₃ HW₃U₃out,
      have HWU₁₂out : W ⊆ (quotient.out ⟦Us₁⟧).U ∩ (quotient.out ⟦Us₂⟧).U
        := set.subset_inter HWU₁out HWU₂out,
      use [W, HxW, HWU₃out, HWU₁₂out],
      apply subtype.eq,
      dsimp only [presheaf_of_rings_extension],
      dsimp only [to_presheaf_of_rings_extension],
      dsimp only [to_stalk_product],
      funext z HzW,
      apply quotient.sound,
      have BW : W ∈ B := Bstd.2 (Bstd.2 BW₁ BW₂) BW₃,
      use [W, BW, HzW, HWU₃out, HWU₁₂out],
      rw (presheaf_of_rings_on_basis.res_is_ring_hom _ _ _ _).map_mul,
      rw ←presheaf_on_basis.Hcomp',
      rw ←presheaf_on_basis.Hcomp',
      replace Hres₁ := congr_arg (F.res BW₁ BW HWW₁) Hres₁,
      replace Hres₂ := congr_arg (F.res BW₂ BW HWW₂) Hres₂,
      replace Hres₃ := congr_arg (F.res BW₃ BW HWW₃) Hres₃,
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₁, },
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₂, },
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₃, },
      erw [Hres₁, Hres₂, Hres₃],
      rw (presheaf_of_rings_on_basis.res_is_ring_hom _ _ _ _).map_mul,
      rw ←presheaf_on_basis.Hcomp',
      rw ←presheaf_on_basis.Hcomp',
    end,
  map_add := 
    begin
      intros y z,
      apply quotient.induction_on₂ y z,
      intros Us₁ Us₂,
      simp,
      let Us₃ : stalk_on_basis.elem F.to_presheaf_on_basis x :=
        { U := Us₁.U ∩ Us₂.U, 
          BU := Bstd.2 Us₁.BU Us₂.BU,
          Hx := ⟨Us₁.Hx, Us₂.Hx⟩, 
          s :=  F.res Us₁.BU _ (set.inter_subset_left _ _) Us₁.s + 
                F.res Us₂.BU _ (set.inter_subset_right _ _) Us₂.s },
      dunfold to_stalk_extension,
      apply quotient.sound,
      rcases (quotient.mk_out Us₁) with ⟨W₁, BW₁, HxW₁, HW₁U₁out, HW₁U₁, Hres₁⟩,
      rcases (quotient.mk_out Us₂) with ⟨W₂, BW₂, HxW₂, HW₂U₂out, HW₂U₂, Hres₂⟩,
      rcases (quotient.mk_out Us₃) with ⟨W₃, BW₃, HxW₃, HW₃U₃out, HW₃U₃, Hres₃⟩,
      let W := W₁ ∩ W₂ ∩ W₃,
      have HxW : x ∈ W := ⟨⟨HxW₁, HxW₂⟩, HxW₃⟩,
      have HWW₁ : W ⊆ W₁ := λ x Hx, Hx.1.1,
      have HWW₂ : W ⊆ W₂ := λ x Hx, Hx.1.2,
      have HWW₃ : W ⊆ W₃ := λ x Hx, Hx.2,
      have HWU₁out : W ⊆ (quotient.out ⟦Us₁⟧).U := set.subset.trans HWW₁ HW₁U₁out,
      have HWU₂out : W ⊆ (quotient.out ⟦Us₂⟧).U := set.subset.trans HWW₂ HW₂U₂out,
      have HWU₃out : W ⊆ (quotient.out ⟦Us₃⟧).U := set.subset.trans HWW₃ HW₃U₃out,
      have HWU₁₂out : W ⊆ (quotient.out ⟦Us₁⟧).U ∩ (quotient.out ⟦Us₂⟧).U
        := set.subset_inter HWU₁out HWU₂out,
      use [W, HxW, HWU₃out, HWU₁₂out],
      apply subtype.eq,
      dsimp only [presheaf_of_rings_extension],
      dsimp only [to_presheaf_of_rings_extension],
      dsimp only [to_stalk_product],
      funext z HzW,
      apply quotient.sound,
      have BW : W ∈ B := Bstd.2 (Bstd.2 BW₁ BW₂) BW₃,
      use [W, BW, HzW, HWU₃out, HWU₁₂out],
      rw (presheaf_of_rings_on_basis.res_is_ring_hom _ _ _ _).map_add,
      rw ←presheaf_on_basis.Hcomp',
      rw ←presheaf_on_basis.Hcomp',
      replace Hres₁ := congr_arg (F.res BW₁ BW HWW₁) Hres₁,
      replace Hres₂ := congr_arg (F.res BW₂ BW HWW₂) Hres₂,
      replace Hres₃ := congr_arg (F.res BW₃ BW HWW₃) Hres₃,
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₁, },
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₂, },
      iterate 2 { rw ←presheaf_on_basis.Hcomp' at Hres₃, },
      erw [Hres₁, Hres₂, Hres₃],
      rw (presheaf_of_rings_on_basis.res_is_ring_hom _ _ _ _).map_add,
      rw ←presheaf_on_basis.Hcomp',
      rw ←presheaf_on_basis.Hcomp',
    end, }

lemma to_stalk_extension.ring_equiv
(F : presheaf_of_rings_on_basis α HB) 
(x : α)
: stalk_of_rings_on_standard_basis Bstd F x ≃+* 
stalk_of_rings (presheaf_of_rings_extension Bstd F) x :=
begin
  have H := function.bijective_iff_has_inverse.1 (to_stalk_extension.bijective Bstd F x),
  rcases (classical.indefinite_description _ H) with ⟨inv, Hlinv, Hrinv⟩,
  use [(to_stalk_extension Bstd F x), inv, Hlinv, Hrinv],
  { apply (to_stalk_extension.is_ring_hom Bstd F x).map_mul, },
  { apply (to_stalk_extension.is_ring_hom Bstd F x).map_add, }
end

end extension_coincides

end presheaf_of_rings_extension
