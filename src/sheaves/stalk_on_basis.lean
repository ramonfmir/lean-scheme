import sheaves.presheaf_of_types_on_basis

universe u 

variables {α : Type u} [T : topological_space α] 
variables {B : set (set α )} {HB : topological_space.is_topological_basis B}
variables (F : presheaf_of_types_on_basis α HB) (x : α)

structure stalk_on_basis.elem :=
(U : set α)
(BU : U ∈ B)
(Hx : x ∈ U)
(s : F BU)

-- Equivalence relation on the set of pairs. (U,s) ~ (V,t) iff there exists W 
-- open s.t. x ∈ W ⊆ U ∩ V, and s|W = t|W.

def stalk_on_basis.relation : stalk_on_basis.elem F x → stalk_on_basis.elem F x → Prop :=
λ Us Vt,
    ∃ W (BW : W ∈ B) (HxW : x ∈ W) (HWU : W ⊆ Us.U) (HWV : W ⊆ Vt.U),
    F.res Us.BU BW HWU Us.s = F.res Vt.BU BW HWV Vt.s

-- TODO: CHANGE THIS

lemma stalk_on_basis.relation.reflexive : reflexive (stalk_on_basis.relation F x) :=
λ ⟨U, OU, HxU, s⟩, ⟨U, OU, HxU, set.subset.refl _, set.subset.refl _, rfl⟩

lemma stalk_on_basis.relation.symmetric : symmetric (stalk_on_basis.relation F x) :=
λ Us Vt ⟨W, OW, HxW, HWU, HWV, Hres⟩, ⟨W, OW, HxW, HWV, HWU, Hres.symm⟩

lemma stalk_on_basis.relation.transitive : transitive (stalk_on_basis.relation F x) :=
λ ⟨U, OU, HxU, sU⟩ ⟨V, OV, HxV, sV⟩ ⟨W, OW, HxW, sW⟩,
λ ⟨R, OR, HxR, HRU, HRV, HresR⟩ ⟨S, OS, HxS, HSV, HSW, HresS⟩,
⟨R ∩ S, is_open_inter OR OS, ⟨HxR, HxS⟩,
λ y ⟨HyR, _⟩, HRU HyR, λ y ⟨_, HyS⟩, HSW HyS,
have ORS : _ := is_open_inter OR OS,
have HURRS : _ := F.Hcomp OU OR ORS (set.inter_subset_left _ _) HRU,
have HVRRS : _ := F.Hcomp OV OR ORS (set.inter_subset_left _ _) HRV,
have HVSRS : _ := F.Hcomp OV OS ORS (set.inter_subset_right _ _) HSV,
have HWSRS : _ := F.Hcomp OW OS ORS (set.inter_subset_right _ _) HSW,
calc  F.res OU ORS _ sU 
    = F.res OR ORS _ (F.res OU OR _ sU) : congr_fun HURRS sU 
... = F.res OR ORS _ (F.res OV OR _ sV) : congr_arg _ HresR
... = F.res OV ORS _ sV                 : congr_fun HVRRS.symm sV
... = F.res OS ORS _ (F.res OV OS _ sV) : congr_fun HVSRS sV
... = F.res OS ORS _ (F.res OW OS _ sW) : congr_arg _ HresS
... = F.res OW ORS _ sW                 : congr_fun HWSRS.symm sW⟩

lemma stalk_on_basis.relation.equivalence : equivalence (stalk.relation F x) :=
⟨stalk_on_basis.relation.reflexive F x, 
stalk_on_basis.relation.symmetric F x,
stalk_on_basis.relation.transitive F x⟩

instance stalk_on_basis.setoid : setoid (stalk_on_basis.elem F x) :=
{ r := stalk_on_basis.relation F x,
  iseqv := stalk_on_basis.relation.equivalence F x }

-- We define a stalk as the set of stalk elements under the defined relation.

definition stalk_on_basis := quotient (stalk_on_basis.setoid F x)