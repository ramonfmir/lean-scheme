import topology.opens
import sheaves.presheaf_of_rings_on_basis
import sheaves.presheaf_of_rings_extension
import sheaves.sheaf_on_standard_basis
import sheaves.sheaf_of_rings

open topological_space

universe u

section presheaf_of_rings_extension

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α)} {HB : opens.is_basis B}
variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

include Bstd

-- lemma presheaf_extension.eq (F : presheaf_on_basis α HB) (HF : is_sheaf_on_basis F)
-- {U : opens α} (BU : U ∈ B)
-- : (F ₑₓₜ).F U ≃ F.F BU := 
-- { to_fun := 
--     begin
--       rintros ⟨s, Hs⟩,
--       let OC : @covering_basis _ _ B U :=
--         { γ := U,
--           Uis := λ x, (classical.some (Hs x x.2)) ∩ U, 
--           BUis := λ x, Bstd.2 (classical.some (classical.some_spec (Hs x x.2))) BU,
--           Hcov := 
--             begin
--               apply opens.ext,
--               apply set.ext,
--               intros x,
--               split,
--               { rintros ⟨V, ⟨⟨OV, ⟨⟨y, Hy⟩, Hval⟩⟩, HxV⟩⟩,
--                 rw ←Hval at HxV,
--                 simp at Hy,
--                 rw ←Hy at HxV,
--                 rcases HxV with ⟨HxV, HxU⟩,
--                 exact HxU, },
--               { intros Hx,
--                 existsi [(classical.some (Hs x Hx)).val ∩ U.val],
--                 simp,
--                 split,
--                 existsi [(classical.some (Hs x Hx)).val ∩ U.val],
--                 split,
--                 { exact (classical.some (classical.some_spec (classical.some_spec (Hs x x.2)))), },
--                 {}, },
--             end,
--           Iij := sorry,
--           Uijks := sorry,
--           BUijks := sorry,
--           Hintercov := sorry, },
--       rcases HF BU OC,
--     end,
--   inv_fun := sorry,
--   left_inv := sorry,
--   right_inv := sorry, }

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

end presheaf_of_rings_extension
