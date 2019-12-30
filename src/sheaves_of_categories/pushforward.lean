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

namespace topological_space.presheaf

def map {f : X → Y} (hf : continuous f) : presheaf X C ⥤ presheaf Y C :=
{ obj := λ ℱ, {
    val := λ _, ℱ (hf.comap _),
    res' := λ _ _ hV, ℱ.res (λ _ hv, hV hv),
    Hid' := λ _, ℱ.Hid _,
    Hcomp' := λ _ _ _ _ _, ℱ.Hcomp _ _},
  map := λ ℱ 𝒢 φ, {
    map := λ V, φ (continuous.comap hf V),
    commutes' := λ U V HVU, presheaf.morphism.commutes _ _},
  map_id' := by intros; split,
  map_comp' := by intros; split }

def map.id : map (@continuous_id X _) ≅ 𝟭 (presheaf X C):=
{ hom :=
  { app := λ ℱ,
    { map := λ U, ℱ.res (set.subset.refl U),
      commutes' := λ U V HVU, by erw [←ℱ.Hcomp, ←ℱ.Hcomp] },
    naturality' := λ ℱ 𝒢 φ, by ext; apply presheaf.morphism.commutes φ },
  inv := {
    app := λ ℱ, {
      map := λ U, ℱ.res (λ _, id),
      commutes' := λ U V HVU, by erw [←ℱ.Hcomp, ←ℱ.Hcomp] },
    naturality' := λ ℱ 𝒢 φ, by ext; apply presheaf.morphism.commutes φ },
  hom_inv_id' := begin
    ext ℱ U,
    dsimp,
    unfold_coes,
    unfold category_struct.comp, dsimp,
    unfold_coes,
    dsimp,
    rw ←ℱ.Hcomp,
    exact ℱ.Hid _,
  end,
  inv_hom_id' := begin
    ext ℱ U,
    unfold_coes,
    dsimp,
    unfold category_struct.comp, dsimp,
    unfold_coes,
    dsimp,
    rw ←ℱ.Hcomp,
    exact ℱ.Hid _,
  end }

end topological_space.presheaf

namespace topological_space.sheaf

variables [limits.has_products.{v} C] [limits.has_equalizers.{v} C]

/-
sheaf.is_limit :
  Π (ℱ : sheaf X C) {U : opens X} (OC : covering U),
    limits.is_limit (presheaf.to_fork (ℱ.to_presheaf) OC)

presheaf.to_fork :
  Π (ℱ : presheaf X C) {U : opens X} (OC : covering U),
    limits.fork (presheaf.res_left ℱ OC) (presheaf.res_right ℱ OC)
-/

#check covering

def map {f : X → Y} (hf : continuous f) : sheaf X C ⥤ sheaf Y C :=
{ obj := λ ℱ, {
    val := λ _, ℱ (hf.comap _),
    res' := λ _ _ hV, ℱ.res (λ _ hv, hV hv),
    Hid' := λ _, ℱ.Hid _,
    Hcomp' := λ _ _ _ _ _, ℱ.Hcomp _ _,
    is_limit := λ U OC, begin
      sorry
    end},
  map := λ ℱ 𝒢 φ, {
    map := λ V, φ (continuous.comap hf V),
    commutes' := λ U V HVU, presheaf.morphism.commutes _ _},
--  map_id' := by intros; split,
--  map_comp' := by intros; split
}

-- todo: pushforward of a sheaf should be a sheaf

end topological_space.sheaf
