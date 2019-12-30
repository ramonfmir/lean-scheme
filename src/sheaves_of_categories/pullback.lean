import sheaves_of_categories.sheaf

universes v u

namespace topological_space.presheaf

open category_theory topological_space

variables {X Y : Type v} [topological_space X] [topological_space Y]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- hack to reverse arrows on a preorder
def small_category {α : Type v} [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (V ≤ U)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ _ _ _ f g, ⟨ ⟨ le_trans g.down.down f.down.down ⟩ ⟩ }

-- need to beat 100 to have an effect
local attribute [instance, priority 200] small_category

--example (X Y : Type) {f : X → Y}
--  (U : set X) (V : set Y) : f '' U ⊆ V ↔ U ⊆ f ⁻¹' V := easy

/-- The functor induced by ℱ on the opens containing a subset of X -/
def aux_functor (ℱ : presheaf X C) (Y : set X)
  : {V : opens X // Y ⊆ V} ⥤ C :=
{ obj := λ V, ℱ V,
  map := λ V₁ V₂ j, ℱ.res j.1.1,
  map_id' := λ _, ℱ.Hid _,
  map_comp' := λ _ _ _ _ _, ℱ.Hcomp _ _
}

def aux_functor.hom {ℱ 𝒢 : presheaf X C} (φ : ℱ ⟶ 𝒢) (Y : set X) :
  aux_functor ℱ Y ⟶ aux_functor 𝒢 Y :=
{ app := λ V, φ V,
  naturality' := λ V W i, (morphism.commutes' φ V W i.down.down).symm }

-- I should only need filtered colimits
variable [limits.has_colimits.{v} C]

def aux_cocone (ℱ : presheaf X C) (Y : set X) : limits.cocone (ℱ.aux_functor Y) :=
limits.colimit.cocone (ℱ.aux_functor Y)

def aux_colimit (ℱ : presheaf X C) (Y : set X) : C :=
(ℱ.aux_cocone Y).X

def res_functor {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
    {V : opens X // Y₁ ⊆ V} ⥤ {V : opens X // Y₂ ⊆ V} :=
{ obj := λ V, ⟨V.1, set.subset.trans hY V.2⟩,
  map := λ _ _, id}

lemma res_res {Y₁ Y₂ Y₃ : set X} (h21 : Y₂ ⊆ Y₁) (h32 : Y₃ ⊆ Y₂) :
  res_functor h21 ⋙ res_functor h32 = res_functor (set.subset.trans h32 h21) := rfl

example (ℱ : presheaf X C) {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
  res_functor hY ⋙ ℱ.aux_functor Y₂ = ℱ.aux_functor Y₁ := rfl -- :-)

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

/-
#check limits.colimit.pre

category_theory.limits.colimit.pre : Π {J K : Type v} [_inst_1 : small_category J]
[_inst_2 : small_category K] {C : Type u} [𝒞 : category_theory.category C] (F : J ⥤ C)
[_inst_3 : limits.has_colimit F] (E : K ⥤ J) [_inst_4 : limits.has_colimit (E ⋙ F)],
limits.colimit (E ⋙ F) ⟶ limits.colimit F
-/

--example {J K : Type v} [_inst_1 : small_category J]
--[small_category K] {C : Type u} [𝒞 : category_theory.category C] (F : J ⥤ C)
--[limits.has_colimit F] (E₁ E₂ : K ⥤ J) [limits.has_colimit (E₁ ⋙ F)] [limits.has_colimit (E₂ ⋙ F)]
--(h : E₁ = E₂) : limits.colimit.pre F E₁ = limits.colimit.pre F E₂ := sorry

lemma res_aux (ℱ : presheaf X C) {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
  res_functor hY ⋙ ℱ.aux_functor Y₂ = ℱ.aux_functor Y₁ := rfl -- :-)

--set_option pp.proofs true
--set_option trace.simplify.rewrite true
set_option profiler true
def comap {f : X → Y} (hf : continuous f) : presheaf Y C ⥤ presheaf X C :=
{ obj := λ ℱ,
  { val := λ U, ℱ.aux_colimit (f '' U),
    res' := λ U₁ U₂ hU,
      limits.colimit.pre (ℱ.aux_functor _) (res_functor $ set.image_subset _ hU),
    Hid' := λ U, begin
      ext,
      rw limits.colimit.ι_pre,
      erw category.comp_id,
      cases j, cases U, refl,
    end,
    Hcomp' := begin
      intros,
      ext,
      erw limits.colimit.ι_pre,
      conv begin
        to_rhs,
        congr, skip,
        congr,
        change limits.colimit.pre (res_functor
          (show f '' W.val ⊆ f '' V.val, from set.image_subset f HWV) ⋙
          aux_functor ℱ (f '' W.val)) (res_functor (set.image_subset f HVU)),
      end,
      rw limits.colimit.pre_pre,
      conv begin
        to_rhs,
        congr, skip,
        change limits.colimit.pre (aux_functor ℱ (f '' W.val))
          (res_functor (show f '' W.val ⊆ f '' U.val, from set.subset.trans
          (show f '' W.val ⊆ f '' V.val, from set.image_subset f HWV)
          (show f '' V.val ⊆ f '' U.val, from set.image_subset f HVU))),
      end,
      rw limits.colimit.ι_pre,
    end },
  map := λ ℱ 𝒢 φ,
  { map := λ U, limits.colimit.desc _
      ((limits.cocones.precompose (aux_functor.hom φ _)).obj ((aux_cocone 𝒢 (f '' U)))),
    commutes' := begin sorry end },
  map_id' := sorry,
  map_comp' := sorry }

end topological_space.presheaf
