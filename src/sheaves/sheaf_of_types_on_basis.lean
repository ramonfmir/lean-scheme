import sheaves.presheaf_of_types
import sheaves.presheaf_of_types_on_basis
import sheaves.sheaf_of_types
import sheaves.stalk_on_basis

universes u v w

-- Kevin and Kenny

open topological_space

-- TODO: Rename this. helper1 will be useful for presheaves as well.

-- If ⋃ Ui = U then for all i U_i ⊆ U
def helper1 {α : Type u} {γ : Type u} {U : set α} {Ui : γ → set α} {i : γ} :
(⋃ (i' : γ), (Ui i')) = U → Ui i ⊆ U := 
λ Hcov z HzUi, Hcov ▸ ⟨_, ⟨_, rfl⟩, HzUi⟩

-- union of a bunch of sets U_{ijk} = U_i intersect U_j implies U_{ijk} sub U_i
def helper2 {X : Type u} {γ : Type u}  {Ui : γ → set X}
{β : γ → γ → Type*} {Uijk : Π (i j : γ), β i j → set X} {i j : γ} {k : β i j}
: (⋃ (k' : β i j), Uijk i j k') = Ui i ∩ Ui j → Uijk i j k ⊆ Ui i :=
λ H, have H1 : Uijk i j k ⊆ Ui i ∩ Ui j,
from λ z hz, H ▸ ⟨_, ⟨_, rfl⟩, hz⟩,
set.subset.trans H1 (set.inter_subset_left _ _)

-- union of a bunch of sets U_{ijk} = U_i intersect U_j implies U_{ijk} sub U_j
def helper3 {X : Type u} {γ : Type u} {Ui : γ → set X}
{β : γ → γ → Type*} {Uijk : Π (i j : γ), β i j → set X} {i j : γ} {k : β i j}
: (⋃ (k' : β i j), Uijk i j k') = Ui i ∩ Ui j → Uijk i j k ⊆ Ui j :=
λ H, have H1 : Uijk i j k ⊆ Ui i ∩ Ui j,
from λ z hz, H ▸ ⟨_, ⟨_, rfl⟩, hz⟩,
set.subset.trans H1 (set.inter_subset_right _ _)

section preliminaries

-- Sheaf condition.

parameters {α : Type u} [T : topological_space α]
parameters {B : set (set α)} [HB : is_topological_basis B]

structure covering (U : set α) := 
{γ    : Type u}
(Ui   : γ → set α)
(BUi  : ∀ i, (Ui i) ∈ B)
(Hcov : (⋃ i : γ, Ui i) = U)

structure covering_inter {U : set α} (CU : covering U) :=
(Iij       : CU.γ → CU.γ → Type u)
(Uijk      : ∀ i j, Iij i j → set α)
(BUijk     : ∀ i j, ∀ (k : Iij i j), (Uijk i j k) ∈ B)
(Hintercov : ∀ i j, (⋃ (k : Iij i j), Uijk i j k) = CU.Ui i ∩ CU.Ui j)

definition is_sheaf_of_types_on_basis (F : presheaf_of_types_on_basis α HB) :=
∀ {U} (BU : U ∈ B) (OC : covering U) (OCI : covering_inter OC),
∀ (s : Π (i : OC.γ), F (OC.BUi i)) (i j : OC.γ) (k : OCI.Iij i j),
F.res (OC.BUi i) (OCI.BUijk i j k) (helper2 (OCI.Hintercov i j)) (s i) =
F.res (OC.BUi j) (OCI.BUijk i j k) (helper3 (OCI.Hintercov i j)) (s j) → 
∃! (S : F BU), ∀ (i : OC.γ), 
  F.res BU (OC.BUi i) (helper1 OC.Hcov) S = s i  

-- -- This is the correct definition of sheaf of types on a basis, with no assumption that
-- -- intersection of two basis elements is a basis element. I prove it for O_X
-- -- in tag01HR
-- definition is_sheaf_of_types_on_basis 
--   (F : presheaf_of_types_on_basis α HB) : Prop :=

-- ∀ {U} (BU : U ∈ B) {γ : Type u} (Ui : γ → set α) (BUi : ∀ i, (Ui i) ∈ B)
--   (Hcov : (⋃ (x : γ), (Ui x)) = U)

--   {β : γ → γ → Type u} (Uijk : Π (i j : γ), β i j → set X)
  
--   (BUijk : ∀ i j : γ, ∀ k : β i j, B (Uijk i j k) )
  
--   (Hcov2 : ∀ i j : γ, (⋃ (k : β i j), Uijk i j k )= Ui i ∩ Ui j)
  
--   (si : Π (i : γ), F (BUi i))-- sections on the cover
--   -- if they agree on overlaps
--   (Hagree : ∀ i j : γ, ∀ k : β i j, 
--     FPTB.res (BUi i) (BUijk i j k) (helper2 (Hcov2 i j): Uijk i j k ⊆ Ui i) (si i)
--     = FPTB.res (BUi j) (BUijk i j k) (helper3 (Hcov2 i j) : Uijk i j k ⊆ Ui j) (si j)),


--   -- then there's a unique global section which agrees with all of them.
--   ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) ((helper1 Hcov) : Ui i ⊆ U) s = si i

-- tag 009N

include HB -- TODO: why is this not included?

lemma open_basis_elem {U : set α} (BU : U ∈ B) : T.is_open U := 
HB.2.2.symm ▸ generate_open.basic U BU

definition presheaf_of_types_to_presheaf_of_types_on_basis 
(F : presheaf_of_types α) : presheaf_of_types_on_basis α HB :=
{ F := λ U BU, F (open_basis_elem BU),
  res := λ U V BU BV HVU, F.res (open_basis_elem BU) (open_basis_elem BV) HVU,
  Hid := λ U BU, F.Hid (open_basis_elem BU),
  Hcomp := λ U V W BU BV BW, F.Hcomp (open_basis_elem BU) (open_basis_elem BV) (open_basis_elem BW) }

definition presheaf_of_types_on_basis_to_presheaf_of_types
(F : presheaf_of_types_on_basis α HB) : presheaf_of_types α :=
{ F := λ U OU, {s : Π (x ∈ U), stalk_on_basis F x //
        ∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F BV),
        ∀ (y ∈ U ∩ V), s y = λ _, ⟦{U := V, BU := BV, Hx := H.2, s := σ}⟧},
  res := λ U W OU OW HWU FU, 
        { val := λ x HxW, (FU.val x $ HWU HxW),
          property := λ x HxW,
            begin
              rcases (FU.property x (HWU HxW)) with ⟨V, ⟨BV, ⟨HxV, ⟨σ, HFV⟩⟩⟩⟩,
              use [V, BV, HxV, σ],
              rintros y ⟨HyW, HyV⟩,
              rw (HFV y ⟨HWU HyW, HyV⟩),
            end },
  Hid := λ U OU, funext $ λ x, subtype.eq rfl,
  Hcomp := λ U V W OU OV OW HWV HVU, funext $ λ x, subtype.eq rfl}

instance forget_basis : has_coe (presheaf_of_types_on_basis α HB) (presheaf_of_types α) :=
⟨presheaf_of_types_on_basis_to_presheaf_of_types⟩
 
-- end preliminaries


-- --  #print subtype.mk_eq_mk -- this is a simp lemma so why can't
-- -- I use simp?

-- --variables {X : Type*} [T : topological_space X] {B : set (set X)} 
-- --  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
-- --  (HF : is_sheaf_of_types_on_basis FB)

-- --set_option pp.notation false 
-- -- set_option pp.proofs true 

-- section extension

-- parameters {α : Type u} [T : topological_space α]
-- parameters {B : set (set α)} [HB : is_topological_basis B]

-- include HB

/-
def locality (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering) (OCU : covers OC U) (s t : F OU), 
(∀ (i : OC.γ),
F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) s =
F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) t) → 
s = t

def gluing (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering) (OCU : covers OC U),
∀ (s : Π (i : OC.γ), F (OC.OUi i)) (i j : OC.γ),
res_to_inter_left F (OC.OUi i) (OC.OUi j) (s i) = 
res_to_inter_right F (OC.OUi i) (OC.OUi j) (s j) → 
∃ (S : F OU), ∀ (i : OC.γ),
  F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) S = s i

-/

theorem extension_is_sheaf
  (F : presheaf_of_types_on_basis α HB) 
  (HF : is_sheaf_of_types_on_basis F)
  : is_sheaf_of_types (presheaf_of_types_on_basis_to_presheaf_of_types F) := 
begin
  split, 
  -- Locality.
  { intros U OU OC OCU s t Hst,
    rcases OC with ⟨γ, Ui, OUi⟩,
    apply subtype.eq, 
    apply funext,
    intros x,
    apply funext,
    intros HxU,
    rw OCU.symm at HxU,
    rcases HxU with ⟨Uj, ⟨⟨j, HUj⟩, HxUj⟩⟩,
    rw ←HUj at HxUj,
    have Hstj := congr_fun (subtype.mk_eq_mk.1 (Hst j)),
    have Hstjx := Hstj x,
    have HstjxU := congr_fun Hstjx HxUj,
    exact HstjxU,
  },
  -- Gluing.
  { intros U OU OC OCU s i j Hij,
    sorry, }
end

end preliminaries

#exit

theorem extension_is_sheaf {X : Type u} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB)
  : is_sheaf_of_types (extend_off_basis FB HF) := begin
  intros U OU γ Ui UiO Hcov,
  split,
  { -- Done
  },
  { intro s,
    existsi _,swap,
    { refine ⟨_,_⟩,
      { intros x HxU,
        rw ←Hcov at HxU,
        cases (classical.indefinite_description _ HxU) with Uig HUig,
        cases (classical.indefinite_description _ HUig) with H2 HUigx,
        cases (classical.indefinite_description _ H2) with g Hg,
        rw Hg at HUigx,
        have t := (s.val g),
        exact t.val x HUigx,
      },
      intros x HxU,
      rw ←Hcov at HxU,
      cases HxU with Uig HUig,
      cases HUig with H2 HUigx,
      cases H2 with g Hg,
      rw Hg at HUigx,
      cases (s.val g).property x HUigx with V HV,
      cases HV with BV H2,
      cases H2 with HxV H3,
      -- now replace V by W, in B, contained in V and in Uig, and containing x
      have OUig := UiO g,
      have H := ((topological_space.mem_nhds_of_is_topological_basis HB).1 _ :
        ∃ (W : set X) (H : W ∈ B), x ∈ W ∧ W ⊆ (V ∩ Ui g)),
        swap,
        have UVUig : T.is_open (V ∩ Ui g) := T.is_open_inter V (Ui g) _ OUig,
        have HxVUig : x ∈ V ∩ Ui g := ⟨_,HUigx⟩,
        exact mem_nhds_sets UVUig HxVUig,
        exact HxV,
        rw HB.2.2,
        exact topological_space.generate_open.basic V BV,
      cases H with W HW,
      cases HW with HWB HW,
      existsi W,
      existsi HWB,
      existsi HW.1,
      cases H3 with sigma Hsigma,
      have HWV := (set.subset.trans HW.2 $ set.inter_subset_left _ _),
      existsi FB.res BV HWB HWV sigma,
      intros y Hy,
      -- now apply Hsigma
      have Hy2 : y ∈ V ∩ Ui g := HW.2 Hy.2,
      have Hy3 : y ∈ (Ui g) ∩ V := ⟨Hy2.2,Hy2.1⟩,
      have H := Hsigma y Hy3,
      apply funext,
      intro Hyu,
      dsimp,
      /- goal now
      subtype.rec
      (λ (Uig : set X) (HUig : ∃ (H : ∃ (i : γ), Uig = Ui i), y ∈ Uig),
         subtype.rec
           (λ (H2 : ∃ (i : γ), Uig = Ui i) (HUigx : y ∈ Uig),
              subtype.rec (λ (g : γ) (Hg : Uig = Ui g), (s.val g).val y _)
                (classical.indefinite_description (λ (i : γ), Uig = Ui i) H2))
           (classical.indefinite_description (λ (H : ∃ (i : γ), Uig = Ui i), y ∈ Uig) HUig))
      (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), y ∈ t) _) =
    ⟦{U := W, BU := HWB, Hx := _, s := FB.res BV HWB _ sigma}⟧
      -/
      cases (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), y ∈ t) _) with S HS,
      dsimp,
      /- goal now
      subtype.rec
      (λ (H2 : ∃ (i : γ), T = Ui i) (HUigx : y ∈ T),
         subtype.rec (λ (g : γ) (Hg : T = Ui g), (s.val g).val y _)
           (classical.indefinite_description (λ (i : γ), T = Ui i) H2))
      (classical.indefinite_description (λ (H : ∃ (i : γ), T = Ui i), y ∈ T) HT) =
    ⟦{U := W, BU := HWB, Hx := _, s := FB.res BV HWB _ sigma}⟧
      -/
      cases (classical.indefinite_description (λ (H : ∃ (i : γ), S = Ui i), y ∈ S) HS) with Hh HyS2,
      dsimp,
      /-
      subtype.rec (λ (g : γ) (Hg : T = Ui g), (s.val g).val y _)
      (classical.indefinite_description (λ (i : γ), T = Ui i) Hh) =
    ⟦{U := W, BU := HWB, Hx := _, s := FB.res BV HWB _ sigma}⟧-/
      cases (classical.indefinite_description (λ (i : γ), S = Ui i) Hh) with h HSUih,
      dsimp,
      /-
      (s.val h).val y _ = ⟦{U := W, BU := HWB, Hx := _, s := FB.res BV HWB _ sigma}⟧
      -/
      rw HSUih at HyS2,
      revert HyS2,
      intro HyS,
      suffices : (s.val h).val y HyS = (s.val g).val y Hy2.2,
        rw this,
        rw Hsigma y Hy3,
        apply quotient.sound,
        existsi W,
        existsi Hy.2,
        existsi HWB,
        existsi HWV,
        existsi set.subset.refl _,
        suffices this2 : FB.res _ HWB HWV sigma = FB.res _ HWB _ (FB.res BV HWB HWV sigma),
        simpa using this2,
        rw FB.Hid,refl,
      -- what's left here is (s.val h).val y HyT = (s.val g).val y _
      have Hy4 : y ∈ Ui g := Hy3.1,
      show (s.val h).val y HyS = (s.val g).val y Hy4, -- both of type presheaf_on_basis_stalk FB x
      have H2 := s.property g h,
      unfold res_to_inter_left at H2,
      unfold res_to_inter_right at H2,
      have OUigh : T.is_open (Ui g ∩ Ui h) := T.is_open_inter _ _ (UiO g) (UiO h),
      have H3 : (s.val g).val y Hy4 = 
        ((extend_off_basis FB HF).res (Ui g) (Ui g ∩ Ui h) (UiO g) OUigh (set.inter_subset_left _ _) (s.val g)).val y ⟨Hy4,HyS⟩ := rfl,
      have H4 : (s.val h).val y HyS = 
        ((extend_off_basis FB HF).res (Ui h) (Ui g ∩ Ui h) (UiO h) OUigh (set.inter_subset_right _ _) (s.val h)).val y ⟨Hy4,HyS⟩ := rfl,
      rw H3,
      rw H4,
      rw H2,
    },
    {
      dsimp,
      /- goal now
      gluing (extend_off_basis FB HF) U Ui Hcov
      ⟨λ (x : X) (HxU : x ∈ U),
         subtype.rec
           (λ (Uig : set X) (HUig : ∃ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig),
              subtype.rec
                (λ (H2 : ∃ (i : γ), Uig = Ui i) (HUigx : x ∈ Uig),
                   subtype.rec (λ (g : γ) (Hg : Uig = Ui g), (s.val g).val x _)
                     (classical.indefinite_description (λ (i : γ), Uig = Ui i) H2))
                (classical.indefinite_description (λ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig) HUig))
           (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), x ∈ t) _),
       _⟩ =
    s
    -/
    unfold gluing,

    apply subtype.eq,
    dsimp,
    apply funext,
    intro i,
    apply subtype.eq,
    /- goal now
     ((extend_off_basis FB HF).res U (Ui i) OU _ _
       ⟨λ (x : X) (HxU : x ∈ U),
          subtype.rec
            (λ (Uig : set X) (HUig : ∃ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig),
               subtype.rec
                 (λ (H2 : ∃ (i : γ), Uig = Ui i) (HUigx : x ∈ Uig),
                    subtype.rec (λ (g : γ) (Hg : Uig = Ui g), (s.val g).val x _)
                      (classical.indefinite_description (λ (i : γ), Uig = Ui i) H2))
                 (classical.indefinite_description (λ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig) HUig))
            (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), x ∈ t) _),
        _⟩).val =
    (s.val i).val
    -/
    apply funext,
    intro x,
    
    apply funext,
    intro HxUi,
    
    /- goal now
    ((extend_off_basis FB HF).res U (Ui i) OU _ _
       ⟨λ (x : X) (HxU : x ∈ U),
          subtype.rec
            (λ (Uig : set X) (HUig : ∃ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig),
               subtype.rec
                 (λ (H2 : ∃ (i : γ), Uig = Ui i) (HUigx : x ∈ Uig),
                    subtype.rec (λ (g : γ) (Hg : Uig = Ui g), (s.val g).val x _)
                      (classical.indefinite_description (λ (i : γ), Uig = Ui i) H2))
                 (classical.indefinite_description (λ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig) HUig))
            (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), x ∈ t) _),
        _⟩).val
      x
      HxUi =
    (s.val i).val x HxUi
    -/
    have HxU : x ∈ U := Hcov ▸ (set.subset_Union Ui i) (HxUi),
    
    let HHH : presheaf_on_basis_stalk FB x := subtype.rec
            (λ (Uig : set X) (HUig : ∃ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig),
               subtype.rec
                 (λ (H2 : ∃ (i : γ), Uig = Ui i) (HUigx : x ∈ Uig),
                    subtype.rec (λ (g : γ) (Hg : Uig = Ui g), (s.val g).val x (Hg ▸ HUigx))
                      (classical.indefinite_description (λ (i : γ), Uig = Ui i) H2))
                 (classical.indefinite_description (λ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig) HUig))
            (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), x ∈ t) ⟨Ui i,⟨i,rfl⟩,HxUi⟩),

    suffices : (subtype.rec
            (λ (Uig : set X) (HUig : ∃ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig),
               subtype.rec
                 (λ (H2 : ∃ (i : γ), Uig = Ui i) (HUigx : x ∈ Uig),
                    subtype.rec (λ (g : γ) (Hg : Uig = Ui g), (s.val g).val x (Hg ▸ HUigx))
                      (classical.indefinite_description (λ (i : γ), Uig = Ui i) H2))
                 (classical.indefinite_description (λ (H : ∃ (i : γ), Uig = Ui i), x ∈ Uig) HUig))
            (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), x ∈ t) ⟨Ui i,⟨i,rfl⟩,HxUi⟩) 
              : presheaf_on_basis_stalk FB x)
            = (s.val i).val x HxUi,
      rw ←this,
      refl,
    cases (classical.indefinite_description (λ (t : set X), ∃ (H : ∃ (i : γ), t = Ui i), x ∈ t) ⟨Ui i,⟨i,rfl⟩,HxUi⟩) with Uij HUij,
    dsimp,
    cases (classical.indefinite_description (λ (H : ∃ (i : γ), Uij = Ui i), x ∈ Uij) HUij) with H2 HxUij,
    dsimp,
    cases (classical.indefinite_description (λ (i : γ), Uij = Ui i) H2) with j Hj,
    dsimp,
    rw Hj at HxUij,
    -- HxUi : x in Ui i
    -- HxUij : x in Ui j 
    show (s.val j).val x HxUij = (s.val i).val x HxUi,
    have HxUiUj : x ∈ Ui i ∩ Ui j := ⟨HxUi,HxUij⟩,
    have Hs := s.property i j,
    have H3 : (s.val j).val x HxUij = (@res_to_inter_right _ _ (extend_off_basis FB HF) (Ui i) (Ui j) (UiO i) (UiO j) (s.val j)).val x HxUiUj := rfl,
    rw H3,
    rw ←Hs,
    refl,
    }
  }
end 

#exit

definition extend_off_basis_map {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) :
  morphism_of_presheaves_of_types_on_basis FB (restriction_of_presheaf_to_basis (extend_off_basis FB HF)) := sorry

theorem extension_extends {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) : 
  is_isomorphism_of_presheaves_of_types_on_basis (extend_off_basis_map FB HF) := sorry 

theorem extension_unique {X : Type*} [T : topological_space X] {B : set (set X)} 
  {HB : topological_space.is_topological_basis B} (FB : presheaf_of_types_on_basis HB)
  (HF : is_sheaf_of_types_on_basis FB) (G : presheaf_of_types X)
  (HG : is_sheaf_of_types G) (psi : morphism_of_presheaves_of_types_on_basis FB (restriction_of_presheaf_to_basis G))
  (HI : is_isomorphism_of_presheaves_of_types_on_basis psi) -- we have an extension which agrees with FB on B
  : ∃ rho : morphism_of_presheaves_of_types (extend_off_basis FB HF) G, -- I would happily change the direction of the iso rho
    is_isomorphism_of_presheaves_of_types rho ∧ 
    ∀ (U : set X) (BU : B U), 
      (rho.morphism U (basis_element_is_open HB BU)) ∘ ((extend_off_basis_map FB HF).morphism BU) = (psi.morphism BU) := sorry
