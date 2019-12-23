/- Theory of presheaves of categories on a topological space

cf :   https://stacks.math.columbia.edu/tag/006D

Notes: KMB has never really understood whether we should be using
category theory or not when working with sheaves on a topological space.
By explicitly avoiding this and doing everything from first principles
on the topological space side, but letting sheaves take values which are
objects of a general category is certainly something we want to do.

This is just really an exercise for KB to learn how to use the category theory
library.
-/
import category_theory.full_subcategory

import category_theory.limits.limits -- random import
import topology.opens
import topology.sheaves.presheaf

open category_theory
open topological_space

universes v u -- Homs in C and the top space will be in the same universe v ("sets").

-- when I hover over 𝟙 I don't get the keyboard shortcut
/-- Definition of a presheaf -/
structure topological_space.presheaf (X : Type v) [topological_space X]
  (C : Type u) [𝒞 : category.{v} C] :=
(val : Π (U : opens X), C) -- ℱ
(res   : ∀ (U V) (HVU : V ⊆ U), val U ⟶ val V)
(Hid   : ∀ (U), res U U (set.subset.refl U) = 𝟙 (val U))
(Hcomp : ∀ (U V W) (HWV : W ⊆ V) (HVU : V ⊆ U),
  res U W (set.subset.trans HWV HVU) = res U V HVU ≫ res V W HWV)


open topological_space lattice

namespace topological_space.presheaf

variables {C : Type u} [𝒞 : category.{v} C]
variables {X : Type v} [topological_space X]
include 𝒞

-- I don't know why they used (U V), this changes it to {U V}
def res' : ∀ (ℱ : presheaf X C) {U V : opens X} (HVU : V ⊆ U), ℱ.val U ⟶ ℱ.val V := res

instance : has_coe_to_fun (topological_space.presheaf X C) :=
{ F := λ ℱ, opens X → C,
  coe := topological_space.presheaf.val}

-- simp lemma to get ℱ.val U back into ℱ U form
@[simp] lemma val_eq_coe {ℱ : presheaf X C} {U : opens X} : ℱ.val U = ℱ U := rfl

-- Simplification lemmas for Hid and Hcomp.
@[simp] lemma Hcomp' (ℱ : presheaf X C) :
∀ (U V W : opens X) (HWV : W ⊆ V) (HVU : V ⊆ U),
  (ℱ.res _ _ (set.subset.trans HWV HVU)) =
  (ℱ.res _ _ HVU) ≫ (ℱ.res _ _ HWV)  :=
λ U V W HWV HVU, by rw ℱ.Hcomp _ _ _ HWV HVU; simp

@[simp] lemma Hid' (ℱ : presheaf X C) :
∀ (U : opens X),
  (ℱ.res _ _ (set.subset.refl U)) = 𝟙 (ℱ U) :=
λ U, begin rw ℱ.Hid U, dunfold coe_fn has_coe_to_fun.coe,
-- why refl no work?
simp, end

-- presheaves are a category.
structure morphism (ℱ 𝒢 : presheaf X C) :=
(map      : ∀ (U), ℱ U ⟶ 𝒢 U)
(commutes : ∀ (U V) (HVU : V ⊆ U),
  (map U) ≫ (𝒢.res U V HVU) = (ℱ.res U V HVU) ≫ (map V))

variables {ℱ 𝒢 : presheaf X C}

-- notation
instance : has_hom (presheaf X C) := ⟨morphism⟩

namespace morphism

instance : has_coe_to_fun (morphism ℱ 𝒢) :=
{ F := λ φ, Π (U : opens X), ℱ U ⟶ 𝒢 U,
  coe := λ φ, φ.map}

def commutes' (φ : ℱ ⟶ 𝒢): ∀ {U V : opens X} (HVU : V ⊆ U),
  φ U ≫ 𝒢.res' HVU = ℱ.res' HVU ≫ φ V := φ.commutes

@[ext] def ext (φ ψ : ℱ ⟶ 𝒢) : (φ : ∀ (U : opens X), ℱ U ⟶ 𝒢 U) = ψ → φ = ψ :=
begin
  intro h,
  -- how am I supposed to be doing this? This is too CS for me :-/
  cases φ, cases ψ, unfold_coes at h, dsimp at h, simp [h],
end


end morphism

--#check morphism.commutes'

-- Morphism of presheaves.
instance category_struct : category_struct (presheaf X C) :=
{ hom := morphism,--∀ ℱ 𝒢 (U), ℱ U ⟶ 𝒢 U),
  id := λ ℱ, { map := λ U, 𝟙 (ℱ U), commutes := begin
  intros U V HVU, cases V, cases U, dsimp at *, simp at *, end
  }, -- is there a better tactic?
  comp := λ ℱ 𝒢 ℋ φ ψ,{ map := λ U, (φ U) ≫ (ψ U),--begin sorry end,--λ U, φ U ≫ ψ U,
    commutes := begin intros,
    -- I surely want automation to do this.
      show (φ U ≫ ψ U) ≫ ℋ.res' HVU = ℱ.res' HVU ≫ φ V ≫ ψ V,
      rw category.assoc,
      have X1 := φ.commutes', have Xφ := X1 HVU,
      have X2 := ψ.commutes', have Xψ := X2 HVU,
      rw ψ.commutes',
      rw ←category.assoc,
      -- tidy just makes everything explode at this point
      rw φ.commutes',
      apply category.assoc,
    end}
}
instance category : category (presheaf X C) :=
{
  id_comp' := begin
  -- what is the tactic?
    intros,
    ext,
    apply category.id_comp,
  end,
  comp_id' := begin
    intros,
    ext,
    apply category.comp_id,
  end,
  assoc' := begin
    intros,
    ext,
    apply category.assoc,
  end,
  ..topological_space.presheaf.category_struct }

-- Equality lemma

lemma presheaf_eq_of_subset_eq (ℱ : presheaf X C) (U V : opens X)
: U = V → ℱ U = ℱ V :=
λ h, by simp [h]

end topological_space.presheaf

-- 𝟙 is \b1 and 𝟭 who knows

/-!
pushforwards and pullbacks for presheaves and maybe sheaves too
-/

open topological_space lattice category_theory

variables {X Y : Type v} [topological_space X] [topological_space Y]
variables {C : Type u} [𝒞 : category.{v} C]
variables (f : X → Y) (hf : continuous f)
include 𝒞

instance : preorder (opens X) := by apply_instance
--instance : small_category (opens X) := by apply_instance -- :-( -- wrong way
def small_category {α : Type v} [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (V ≤ U)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ _ _ _ f g, ⟨ ⟨ le_trans g.down.down f.down.down ⟩ ⟩ }

-- need to beat 100 to have an effect
local attribute [instance, priority 200] small_category

--instance : category (presheaf X C) := topological_space.presheaf.category
--instance foo : category (presheaf Y C) := topological_space.presheaf.category

--set_option trace.class_instances true
def map (f : X → Y) (hf : continuous f) : presheaf X C ⥤ presheaf Y C :=
{ obj := λ ℱ, {
    val := λ _, ℱ (hf.comap _),
    res := λ _ _ hV, ℱ.res' (λ _ hv, hV hv),
    Hid := λ _, ℱ.Hid _,
    Hcomp := λ _ _ _ _ _, ℱ.Hcomp _ _ _ _ _},
  map := λ ℱ 𝒢 φ,{
    map := λ V, φ (continuous.comap hf V),
    commutes := λ _ _ _, φ.commutes _ _ _},
  map_id' := by intros; split,
  map_comp' := by intros; split }

-- todo: pushforward of a sheaf should be a sheaf

--example (X Y : Type) {f : X → Y}
--  (U : set X) (V : set Y) : f '' U ⊆ V ↔ U ⊆ f ⁻¹' V := easy

namespace topological_space.presheaf

/-- The functor induced by ℱ on the opens containing a subset of X -/
def to_aux_functor (ℱ : presheaf X C) (Y : set X)
  : {V : opens X // Y ⊆ V} ⥤ C :=
{ obj := λ V, ℱ V,
        map := λ V₁ V₂ j, ℱ.res' j.1.1,
        map_id' := λ _, ℱ.Hid _,
        map_comp' := λ _ _ _ _ _, ℱ.Hcomp _ _ _ _ _}

-- I should only need filtered colimits
variable [limits.has_colimits.{v} C]

def aux_cocone (ℱ : presheaf X C) (Y : set X) : limits.cocone (ℱ.to_aux_functor Y) :=
limits.colimit.cocone (ℱ.to_aux_functor Y)

def aux_colimit (ℱ : presheaf X C) (Y : set X) : C :=
(ℱ.aux_cocone Y).X

def res_functor {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
    {V : opens X // Y₁ ⊆ V} ⥤ {V : opens X // Y₂ ⊆ V} :=
{ obj := λ V, ⟨V.1, set.subset.trans hY V.2⟩,
  map := λ _ _, id}

example (ℱ : presheaf X C) {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
  res_functor hY ⋙ ℱ.to_aux_functor Y₂ = ℱ.to_aux_functor Y₁ := rfl -- :-)

example (Y : set X) : res_functor (set.subset.refl Y) ≅ 𝟭 _ :=
begin
  /- `tidy` says -/
  fsplit,
    { fsplit,
      { intros X_1, cases X_1, cases X_1_val, dsimp at *, fsplit, dsimp at *, fsplit, intros a a_1, assumption },
      { intros X_1 Y_1 f, refl}},
    { fsplit,
      { intros X_1, cases X_1, cases X_1_val, dsimp at *, fsplit, dsimp at *, fsplit, intros a a_1, assumption },
      { intros X_1 Y_1 f, refl }},
      { apply_auto_param },
      { apply_auto_param }
end

example (Y : set X) : res_functor (set.subset.refl Y) = 𝟭 _ := begin
  unfold res_functor,
  unfold category_theory.functor.id,
  simp, refl,
end

example (C D E : Type*) [𝒞 : category C] [𝒟 : category D] [ℰ : category E] (F G : C ⥤ D) (H : D ⥤ E)
  (h : F ≅ G) : (F ⋙ H) ≅ (G ⋙ H) := iso_whisker_right h H

#check limits.colimit.pre
/-
category_theory.limits.colimit.pre : Π {J K : Type v} [_inst_1 : small_category J]
[_inst_2 : small_category K] {C : Type u} [𝒞 : category_theory.category C] (F : J ⥤ C)
[_inst_3 : limits.has_colimit F] (E : K ⥤ J) [_inst_4 : limits.has_colimit (E ⋙ F)],
limits.colimit (E ⋙ F) ⟶ limits.colimit F
-/

--example {J K : Type v} [_inst_1 : small_category J]
--[small_category K] {C : Type u} [𝒞 : category_theory.category C] (F : J ⥤ C)
--[limits.has_colimit F] (E₁ E₂ : K ⥤ J) [limits.has_colimit (E₁ ⋙ F)] [limits.has_colimit (E₂ ⋙ F)]
--(h : E₁ = E₂) : limits.colimit.pre F E₁ = limits.colimit.pre F E₂ := sorry

#check limits.colimit.desc
set_option pp.proofs true
--set_option trace.simplify.rewrite true
def comap {f : X → Y} (hf : continuous f) : presheaf Y C ⥤ presheaf X C :=
{ obj := λ ℱ,
  { val := λ U, ℱ.aux_colimit (f '' U),
    res := λ U₁ U₂ hU,
      limits.colimit.pre (ℱ.to_aux_functor _) (res_functor $ set.image_subset _ hU),
    Hid := λ U, begin
      show limits.colimit.pre (to_aux_functor ℱ (f '' U.val)) (res_functor _) = 𝟙 (aux_colimit ℱ (f '' ↑U)),
      have h : res_functor (set.subset.refl (f '' U.val)) = 𝟭 _,
        unfold res_functor,
        unfold category_theory.functor.id,
        simp, refl,
      have h' : res_functor (set.image_subset f (set.subset.refl ↑U)) = 𝟭 _,
        unfold res_functor,
        unfold category_theory.functor.id,
        simp, refl,

      unfold limits.colimit.pre,
      dsimp,
      ext V,
      dsimp,
--      simp only [h'], -- fails
    sorry end,
    Hcomp := begin sorry end },
  map := λ ℱ 𝒢 φ,
  { map := λ U, sorry,
    commutes := sorry },
  map_id' := sorry,
  map_comp' := sorry }

end topological_space.presheaf
