/-
  Sheaf (of types) on basis and extension.

  https://stacks.math.columbia.edu/tag/009J
  https://stacks.math.columbia.edu/tag/009N
-/

import sheaves.covering.covering_on_basis
import sheaves.presheaf
import sheaves.presheaf_on_basis
import sheaves.presheaf_extension
import sheaves.sheaf
import sheaves.sheaf_on_standard_basis
import sheaves.stalk_on_basis

universes u v w

open topological_space
open lattice
open covering
open classical

section sheaf_on_basis

parameters {α : Type u} [topological_space α]
parameters {B : set (opens α)} {HB : opens.is_basis B}

-- Sheaf condition.

definition is_sheaf_on_basis (F : presheaf_on_basis α HB) :=
∀ {U} (BU : U ∈ B) (OC : covering_basis U),
∀ (s : Π i, F (OC.BUis i)),
(∀ i j k, F.res (OC.BUis i) (OC.BUijks i j k) (subset_covering_basis_inter_left i j k) (s i) =
          F.res (OC.BUis j) (OC.BUijks i j k) (subset_covering_basis_inter_right i j k) (s j)) → 
∃! S, ∀ i, F.res BU (OC.BUis i) (subset_covering i) S = s i

section presheaf_extension_preserves_sheaf_condition

-- Presheaf extension preserves sheaf condition.

noncomputable def global_section 
(F : presheaf_on_basis α HB) (U : opens α) (OC : covering U) 
(s : Π i, (F ₑₓₜ) (OC.Uis i))
(Hsec : ∀ (j k : OC.γ),
  res_to_inter_left (F ₑₓₜ) (OC.Uis j) (OC.Uis k) (s j) =
  res_to_inter_right (F ₑₓₜ) (OC.Uis j) (OC.Uis k) (s k))
: {r : Π (x ∈ U), stalk_on_basis F x //
∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F BV),
∀ (y ∈ U ∩ V), r y = λ _, ⟦{U := V, BU := BV, Hx := H.2, s := σ}⟧} :=
begin 
refine ⟨_, _⟩,
{ -- Define s.
  intros x HxU,
  rw OC.Hcov.symm at HxU,
  rcases (classical.indefinite_description _ HxU) with ⟨Uk, HUk⟩,
  rcases (classical.indefinite_description _ HUk) with ⟨HUkUis, HxUk⟩,
  rcases (classical.indefinite_description _ HUkUis) with ⟨OUk, ⟨HOUkUis, HUkeq⟩⟩,
  rcases (classical.indefinite_description _ HOUkUis) with ⟨k, HUiskeq⟩,
  rw HUkeq.symm at HxUk,
  rw HUiskeq.symm at HxUk,
  exact (s k).val x HxUk },
{ -- Prove the property of s.
  intros x HxU,
  erw OC.Hcov.symm at HxU,
  rcases HxU with ⟨Uk, ⟨⟨OUk, ⟨⟨k, HUiskeq⟩, HUkeq⟩⟩, HxUk⟩⟩,
  rw HUkeq.symm at HxUk,
  rw HUiskeq.symm at HxUk,
  rcases (s k).property x HxUk with ⟨V, ⟨BV, ⟨HxV, ⟨σ, Hσ⟩⟩⟩⟩,
  -- We find W ∈ B such that x ∈ W and W ⊆ V ∩ Ui k.
  have HxVUik : x ∈ (V ∩ OC.Uis k) := ⟨HxV, HxUk⟩,
  have OVUik := is_open_inter V.2 (OC.Uis k).2,
  have HVUik := mem_nhds_sets OVUik HxVUik,
  have HW := (mem_nhds_of_is_topological_basis HB).1 HVUik,
  rcases HW with ⟨W, BW, ⟨HxW, HWVUk⟩⟩,
  simp at BW,
  rcases BW with ⟨OW, BW⟩,
  -- We now find the right σ' ∈ F(W).
  have HWV := (set.subset.trans HWVUk $ set.inter_subset_left _ _),
  let σ' := F.res BV BW HWV σ,
  -- Exists (W, σ') and proceed. 
  use [⟨W, OW⟩, BW, HxW, σ'],
  rintros y ⟨HyU, HyW⟩,
  have HyVUik : y ∈ (V ∩ OC.Uis k) := HWVUk HyW,
  apply funext,
  intros HyU; dsimp,
  -- Now we need to show that ⟦(s k, Ui k)⟧ corresponds to ⟦(σ', W)⟧.
  have Hsk := Hσ y HyVUik.symm,
  let HyUi := λ t, ∃ (H : t ∈ subtype.val '' set.range OC.Uis), y ∈ t,
  rcases (classical.indefinite_description HyUi _) with ⟨S, HS⟩; dsimp,
  let HyS := λ H : S ∈ subtype.val '' set.range OC.Uis, y ∈ S,
  rcases (classical.indefinite_description HyS _) with ⟨HSUiR, HySUiR⟩; dsimp,
  let HOUksub := λ t : subtype is_open, t ∈ set.range (OC.Uis) ∧ t.val = S,
  rcases (classical.indefinite_description HOUksub _) with ⟨OUl, ⟨HOUl, HOUleq⟩⟩; dsimp,
  let HSUi := λ i, OC.Uis i = OUl,
  cases (classical.indefinite_description HSUi _) with l HSUil; dsimp,
  -- We finally have (s l).val y _ = ⟦(W, σ')⟧.
  have HyOUk : y ∈ OUl.val := HOUleq.symm ▸ HySUiR,
  have HyUil : y ∈ OC.Uis l := HSUil.symm ▸ HyOUk,
  have HyUik : y ∈ OC.Uis k := HyVUik.2,
  suffices Hsuff : (s l).val y HyUil = (s k).val y HyUik,
    erw [Hsuff, Hsk],
    apply quotient.sound,
    use [⟨W, OW⟩, BW, HyW, HWV, (set.subset.refl _)]; simp,
    apply F.Hcomp',
  -- Proving Hsuff.
  let F' := presheaf_on_basis_to_presheaf F,
  let UkUl := OC.Uis k ∩ OC.Uis l,
  have Hslres : (s l).val y HyUil = 
    (F'.res (OC.Uis l) UkUl (set.inter_subset_right _ _) (s l)).val y ⟨HyUik, HyUil⟩ := rfl,
  have Hskres : (s k).val y HyUik = 
    (F'.res (OC.Uis k) UkUl (set.inter_subset_left _ _) (s k)).val y ⟨HyUik, HyUil⟩ := rfl,
  have Hs := Hsec k l,
  unfold res_to_inter_left at Hs,
  unfold res_to_inter_right at Hs,
  erw [Hslres, Hskres, Hs],
  apply congr_arg; simp }
end

theorem extension_is_sheaf (F : presheaf_on_basis α HB) (HF : is_sheaf_on_basis F)
: is_sheaf (F ₑₓₜ) := 
begin
  split,
  -- Locality.
  { intros U OC s t Hst,
    apply subtype.eq, 
    apply funext,
    intros x,
    apply funext,
    intros HxU,
    rw OC.Hcov.symm at HxU,
    rcases HxU with ⟨Uj1, ⟨⟨⟨Uj2, OUj⟩, ⟨⟨j, HUj⟩, Heq⟩⟩, HxUj⟩⟩,
    rcases Heq, rcases Heq,
    have Hstj := congr_fun (subtype.mk_eq_mk.1 (Hst j)),
    have HxUj1 : x ∈ OC.Uis j := HUj.symm ▸ HxUj,
    have Hstjx := congr_fun (Hstj x) HxUj1,
    exact Hstjx, },
  -- Gluing.
  { intros U OC s Hsec,
    existsi (global_section F U OC s Hsec),
    -- To show: S|i = s_i for all i.
    intros i,
    apply subtype.eq,
    apply funext,
    intros x,
    apply funext,
    intros HxUi,
    have HxU : x ∈ U := OC.Hcov ▸ (opens_supr_subset OC.Uis i) HxUi,
    let HyUi := λ t, ∃ (H : t ∈ set.range OC.Uis), x ∈ t,
    dunfold presheaf_on_basis_to_presheaf; dsimp,
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
    dunfold presheaf_on_basis_to_presheaf at Hsec,
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
    exact (Hsec ⟨HxUi, HxUl⟩).symm },
end 

end presheaf_extension_preserves_sheaf_condition

end sheaf_on_basis
