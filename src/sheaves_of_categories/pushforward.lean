import sheaves_of_categories.sheaf
import category_theory.full_subcategory

-- 𝟙 is \b1 and 𝟭 who knows

/-!
pushforwards and pullbacks for presheaves and maybe sheaves too
-/

universes v u

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

#print prefix category_theory.functor
#check category_theory.functor.mk.inj_eq

example (ℱ : presheaf X C) {Y : set X} :
  res_functor (show Y ⊆ Y, by refl) = 𝟭 _ := -- rfl fails :-()
begin
  unfold res_functor,
  unfold category_theory.functor.id,
  rw category_theory.functor.mk.inj_eq, -- is there an ext lemma missing?
  split,
    ext, apply subtype.eq, refl,
  apply heq_of_eq,
  ext,
end


-- I should only need filtered colimits
def comap {f : X → Y} (hf : continuous f) : presheaf Y C ⥤ presheaf X C :=
{ obj := λ ℱ,
  { val := λ U, ℱ.aux_colimit (f '' U),
    res := λ U₁ U₂ hU,
      limits.colimit.pre (ℱ.to_aux_functor _) (res_functor $ set.image_subset _ hU),
    Hid := λ U, begin
      show limits.colimit.pre (to_aux_functor ℱ (f '' U.val)) (res_functor _) = 𝟙 (aux_colimit ℱ (f '' ↑U)),
    ext, tidy,  sorry end,
    Hcomp := begin intros, ext, tidy, sorry end },
  map := λ ℱ 𝒢 φ,
  { map := λ U, sorry,
    commutes := sorry },
  map_id' := sorry,
  map_comp' := sorry }

end topological_space.presheaf
