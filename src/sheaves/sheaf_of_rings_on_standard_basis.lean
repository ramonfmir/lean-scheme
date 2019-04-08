import topology.opens
import sheaves.presheaf_of_rings_on_basis
import sheaves.presheaf_of_rings_extension
import sheaves.sheaf_on_standard_basis
import sheaves.sheaf_of_rings

open topological_space classical


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
    dunfold presheaf_of_rings_on_basis_to_presheaf_of_rings; dsimp,
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
    dunfold presheaf_of_rings_on_basis_to_presheaf_of_rings at Hsec,
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

--- https://stacks.math.columbia.edu/tag/009M

-- The map F(U) → Π x ∈ U, Fx

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

-- We want to show that F(U) ≃ Fext(U) as rings when U ∈ B and F is a presheaf of rings.
-- From this it will follow that the stalks are isomorphic.

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
  -- 
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
    -- have Hj := congr_fun (Hσ j j.1 ⟨j.2, HxV j⟩) j.2; dsimp at Hj,
    -- have Hk := congr_fun (Hσ k k.1 ⟨k.2, HxV k⟩) k.2; dsimp at Hk,
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
    -- Thereofre there exists Wjk where σj|Wjk = σk|Wjk. We will use these as a cover.#check
    sorry,
  sorry,
end

end extension_coincides

end presheaf_of_rings_extension
