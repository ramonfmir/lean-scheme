-- tag 009N

import sheaves.presheaf_of_types
import sheaves.presheaf_of_types_on_basis
import sheaves.sheaf_of_types
import sheaves.stalk_on_basis

universes u v w

open topological_space

section sheaf_of_types_on_basis

section preliminaries

parameters {α : Type u} [topological_space α]
parameters {B : set (opens α)} [HB : opens.is_basis B]

-- Open cover.

instance : has_union (opens α) :=
{ union := λ U V, ⟨U.1 ∪ V.1, is_open_union U.2 V.2⟩ }

structure covering (U : opens α) := 
{γ    : Type u}
(Ui   : γ → opens α)
(BUi  : ∀ i, Ui i ∈ B)
(Hcov : (⋃ i, (Ui i).1) = U) -- TODO: change to lattice.Sup (set.range Ui) = U
(Hcov': lattice.Sup (set.range Ui) = U)
(Hsub : ∀ i, Ui i ⊆ U)

-- Open cover for basis.

structure covering_inter {U : opens α} (CU : covering U) :=
(Iij       : CU.γ → CU.γ → Type u)
(Uijk      : ∀ i j, Iij i j → opens α)
(BUijk     : ∀ i j, ∀ (k : Iij i j), (Uijk i j k) ∈ B)
(Hintercov : ∀ i j, (⋃ (k : Iij i j), (Uijk i j k).1) = CU.Ui i ∩ CU.Ui j) -- TODO: same
(Hintersub : ∀ i j k, Uijk i j k ⊆ CU.Ui i ∩ CU.Ui j)

-- If ⋃ Ui = U then for all i, Ui ⊆ U.

-- lemma subset_cover {U : opens α} {OC : covering U} : ∀ j, OC.Ui j ⊆ U := 
-- λ j x HxUj, OC.Hcov ▸ ⟨_, ⟨_, rfl⟩, HxUj⟩

-- If ⋃ Uijk = Ui ∩ Uj then for all k, Uijk ⊆ Ui ∩ Uj.

-- lemma subset_basis_cover_inter {U : opens α} {OC : covering U} {OCI : covering_inter OC}
-- : ∀ i j k, OCI.Uijk i j k ⊆ OC.Ui i ∩ OC.Ui j :=
-- λ i j k x HxUijk, (OCI.Hintercov i j) ▸ ⟨_, ⟨_, rfl⟩, HxUijk⟩

-- If ⋃ Uijk = Ui ∩ Uj then for all k, Uijk ⊆ Ui.

lemma subset_basis_cover_left {U : opens α} {OC : covering U} {OCI : covering_inter OC}
: ∀ i j k, OCI.Uijk i j k ⊆ OC.Ui i :=
λ i j k, set.subset.trans (OCI.Hintersub i j k) (set.inter_subset_left _ _) 

-- If ⋃ Uijk = Ui ∩ Uj then for all k, Uijk ⊆ Uj.

lemma subset_basis_cover_right {U : opens α} {OC : covering U} {OCI : covering_inter OC}
: ∀ i j k, OCI.Uijk i j k ⊆ OC.Ui j :=
λ i j k, set.subset.trans (OCI.Hintersub i j k) (set.inter_subset_right _ _) 

end preliminaries

section presheaf_extension

parameters {α : Type u} [topological_space α]
parameters {B : set (opens α)} [HB : opens.is_basis B]

-- Sheaf condition.

definition is_sheaf_of_types_on_basis (F : presheaf_of_types_on_basis α HB) :=
∀ {U} (BU : U ∈ B) (OC : covering U) (OCI : covering_inter OC),
∀ (s : Π (i : OC.γ), F (OC.BUi i)) (i j : OC.γ) (k : OCI.Iij i j),
F.res (OC.BUi i) (OCI.BUijk i j k) (subset_basis_cover_left i j k) (s i) =
F.res (OC.BUi j) (OCI.BUijk i j k) (subset_basis_cover_right i j k) (s j) → 
∃! (S : F BU), ∀ (i : OC.γ), 
  F.res BU (OC.BUi i) (OC.Hsub i) S = s i  

-- F defined in the whole space to F defined on the basis.

definition presheaf_of_types_to_presheaf_of_types_on_basis 
(F : presheaf_of_types α) : presheaf_of_types_on_basis α HB :=
{ F := λ U BU, F U,
  res := λ U V BU BV HVU, F.res U V HVU,
  Hid := λ U BU, F.Hid U,
  Hcomp := λ U V W BU BV BW, F.Hcomp U V W }

-- F defined on the bases extended to the whole space.

definition presheaf_of_types_on_basis_to_presheaf_of_types
(F : presheaf_of_types_on_basis α HB) : presheaf_of_types α :=
{ F := λ U, {s : Π (x ∈ U), stalk_on_basis F x //
        ∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F BV),
        ∀ (y ∈ U ∩ V), s y = λ _, ⟦{U := V, BU := BV, Hx := H.2, s := σ}⟧},
  res := λ U W HWU FU, 
        { val := λ x HxW, (FU.val x $ HWU HxW),
          property := λ x HxW,
            begin
              rcases (FU.property x (HWU HxW)) with ⟨V, ⟨BV, ⟨HxV, ⟨σ, HFV⟩⟩⟩⟩,
              use [V, BV, HxV, σ],
              rintros y ⟨HyW, HyV⟩,
              rw (HFV y ⟨HWU HyW, HyV⟩),
            end },
  Hid := λ U, funext $ λ x, subtype.eq rfl,
  Hcomp := λ U V W HWV HVU, funext $ λ x, subtype.eq rfl}

instance forget_basis : has_coe (presheaf_of_types_on_basis α HB) (presheaf_of_types α) :=
⟨presheaf_of_types_on_basis_to_presheaf_of_types⟩
 
-- Presheaf extension preserves sheaf condition.
-- TODO: Factor out all of the classical indefinite decription stuff.

-- theorem extension_is_sheaf
--   (F : presheaf_of_types_on_basis α HB) 
--   (HF : is_sheaf_of_types_on_basis F)
--   : is_sheaf_of_types (presheaf_of_types_on_basis_to_presheaf_of_types F) := 
-- begin
--   split,
--   -- Locality.
--   { intros U OC s t Hst,
--     apply subtype.eq, 
--     apply funext,
--     intros x,
--     apply funext,
--     intros HxU,
--     rw OC.Hcov'.symm at HxU,
--     rcases HxU with ⟨Uj1, ⟨⟨⟨Uj2, OUj⟩, ⟨⟨j, HUj⟩, Heq⟩⟩, HxUj⟩⟩,
--     rcases Heq, rcases Heq,
--     have Hstj := congr_fun (subtype.mk_eq_mk.1 (Hst j)),
--     have HxUj1 : x ∈ OC.Ui j,
--       rw HUj,
--       exact HxUj,
--     have Hstjx := congr_fun (Hstj x) HxUj1,
--     exact Hstjx,
--   },
--   -- Gluing.
--   { intros U OC s,
--     existsi _, swap,
--     { refine ⟨_, _⟩,
--       { intros x HxU,
--         rw OC.Hcov'.symm at HxU,
--         cases (classical.indefinite_description _ HxU) with Uk HUk,
--         cases (classical.indefinite_description _ HUk) with HUk HxUk,
--         cases (classical.indefinite_description _ HUk) with Uk1 HUk,
--         rcases HUk with ⟨HUk, Heq⟩,
--         cases (classical.indefinite_description _ HUk) with k HUk,
--         rw ←HUk at HxUk,
--         exact (s.val k).val x HxUk,
--       },
--       { intros x HxU,
--         erw OCU.symm at HxU,
--         rcases HxU with ⟨Uk, ⟨⟨k, HUk⟩, HxUk⟩⟩,
--         erw ←HUk at HxUk,
--         rcases (s.val k).property x HxUk with ⟨V, ⟨BV, ⟨HxV, ⟨σ, Hσ⟩⟩⟩⟩,
--         -- We find W ∈ B such that x ∈ W and W ⊆ V ∩ Ui k.
--         have HxVUik : x ∈ (V ∩ OC.Ui k) := ⟨HxV, HxUk⟩,
--         have OVUik := T.is_open_inter V (OC.Ui k) (open_basis_elem BV) (OC.OUi k),
--         have HVUik := mem_nhds_sets OVUik HxVUik,
--         have HW := (mem_nhds_of_is_topological_basis HB).1 HVUik,
--         rcases HW with ⟨W, BW, ⟨HxW, HWVUik⟩⟩,
--         -- We now find the right σ' ∈ F(W).
--         have HWV := (set.subset.trans HWVUik $ set.inter_subset_left _ _),
--         let σ' := F.res BV BW HWV σ,
--         -- Exists (W, σ') and proceed. 
--         use [W, BW, HxW, σ'],
--         rintros y ⟨HyU, HyW⟩,
--         have HyVUik : y ∈ (V ∩ OC.Ui k) := HWVUik HyW,
--         apply funext,
--         intros HyU; dsimp,
--         -- Now we need to show that ⟦(s k, Ui k)⟧ corresponds to ⟦(σ', W)⟧.
--         have Hsk := Hσ y HyVUik.symm,
--         let HyUi := λ t, ∃ (H : t ∈ set.range OC.Ui), y ∈ t,
--         cases (classical.indefinite_description HyUi _) with S HS; dsimp,
--         let HyS := λ H : S ∈ set.range OC.Ui, y ∈ S,
--         cases (classical.indefinite_description HyS HS) with HSUiR HySUiR; dsimp,
--         let HSUi := λ i, OC.Ui i = S,
--         cases (classical.indefinite_description HSUi HSUiR) with l HSUil; dsimp,
--         -- We finally have (s l).val y _ = ⟦(W, σ')⟧.
--         have HyUil : y ∈ OC.Ui l := HSUil.symm ▸ HySUiR,
--         have HyUik : y ∈ OC.Ui k := HyVUik.2,
--         suffices Hsuff : (s.val l).val y HyUil = (s.val k).val y HyUik,
--           rw Hsuff,
--           rw Hsk,
--           apply quotient.sound,
--           use [W, BW, HyW, HWV],
--           existsi _,
--           simp,
--         -- Proving Hsuff.
--         have OUikUil : T.is_open (OC.Ui k ∩ OC.Ui l) :=
--             T.is_open_inter _ _ (OC.OUi k) (OC.OUi l),
--         have HUikUilUil := set.inter_subset_right (OC.Ui k) (OC.Ui l),
--         have HUikUilUik := set.inter_subset_left (OC.Ui k) (OC.Ui l),
--         let F' := presheaf_of_types_on_basis_to_presheaf_of_types F,
--         have Hslres : (s.val l).val y HyUil = 
--           (F'.res (OC.OUi l) OUikUil HUikUilUil (s.val l)).val y ⟨HyUik, HyUil⟩ := rfl,
--         have Hskres : (s.val k).val y HyUik = 
--           (F'.res (OC.OUi k) OUikUil HUikUilUik (s.val k)).val y ⟨HyUik, HyUil⟩ := rfl,
--         have Hs := s.property k l,
--         unfold presheaf_of_types.res_to_inter_left at Hs,
--         unfold presheaf_of_types.res_to_inter_right at Hs,
--         rw [Hslres, Hskres, Hs] 
--       },
--     },
--     { -- S|i = s_i for all i.
--       intros i, simp,
--       apply subtype.eq; dsimp,
--       apply funext,
--       intros x,
--       apply funext,
--       intros HxUi,
--       have HxU : x ∈ U := OCU ▸ (set.subset_Union OC.Ui i) HxUi,
--       let HyUi := λ t, ∃ (H : t ∈ set.range OC.Ui), x ∈ t,
--       dunfold presheaf_of_types_on_basis_to_presheaf_of_types,
--       dsimp,
--       cases (classical.indefinite_description HyUi _) with S HS,dsimp,
--       let HyS := λ H : S ∈ set.range OC.Ui, x ∈ S,
--       cases (classical.indefinite_description HyS HS) with HSUiR HySUiR; dsimp,
--       let HSUi := λ i, OC.Ui i = S,
--       cases (classical.indefinite_description HSUi HSUiR) with l HSUil; dsimp,
--       have HxUlUi : x ∈ OC.Ui i ∩ OC.Ui l := ⟨HxUi, HSUil.symm ▸ HySUiR⟩,
--       have X := s.property i l,
--       dunfold presheaf_of_types_on_basis_to_presheaf_of_types at X,
--       dunfold presheaf_of_types.res_to_inter_left at X,
--       dunfold presheaf_of_types.res_to_inter_right at X,
--       dsimp at X,
--       rw subtype.ext at X,
--       dsimp at X,
--       replace X := congr_fun X x,
--       dsimp at X,
--       replace X := congr_fun X,
--       exact (X HxUlUi).symm, }
--   },
-- end 

end presheaf_extension

end sheaf_of_types_on_basis

-- definition extend_off_basis_map {X : Type*} [T : topological_space X] {B : set (set X)} 
--   {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
--   (HF : is_sheaf_of_types_on_basis FB) :
--   morphism_of_presheaves_of_types_on_basis FB (restriction_of_presheaf_to_basis (extend_off_basis FB HF)) := sorry

-- theorem extension_extends {X : Type*} [T : topological_space X] {B : set (set X)} 
--   {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
--   (HF : is_sheaf_of_types_on_basis FB) : 
--   is_isomorphism_of_presheaves_of_types_on_basis (extend_off_basis_map FB HF) := sorry 

-- theorem extension_unique {X : Type*} [T : topological_space X] {B : set (set X)} 
--   {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
--   (HF : is_sheaf_of_types_on_basis FB) (G : presheaf_of_types X)
--   (HG : is_sheaf_of_types G) (psi : morphism_of_presheaves_of_types_on_basis FB (restriction_of_presheaf_to_basis G))
--   (HI : is_isomorphism_of_presheaves_of_types_on_basis psi) -- we have an extension which agrees with FB on B
--   : ∃ rho : morphism_of_presheaves_of_types (extend_off_basis FB HF) G, -- I would happily change the direction of the iso rho
--     is_isomorphism_of_presheaves_of_types rho ∧ 
--     ∀ (U : set X) (BU : B U), 
--       (rho.morphism U (basis_element_is_open HB BU)) ∘ ((extend_off_basis_map FB HF).morphism BU) = (psi.morphism BU) := sorry
