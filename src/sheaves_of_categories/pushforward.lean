import sheaves_of_categories.sheaf
import category_theory.full_subcategory

universes v u

open topological_space lattice category_theory

variables {X Y : Type v} [topological_space X] [topological_space Y]
variables {C : Type u} [𝒞 : category.{v} C]
variables (f : X → Y) (hf : continuous f)
include 𝒞

instance : preorder (opens X) := by apply_instance

instance small_category {α : Type v} [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (V ≤ U)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans g.down.down f.down.down ⟩ ⟩ }

attribute [instance, priority 200] small_category

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

example (X Y : Type) {f : X → Y}
  (U : set X) (V : set Y) : f '' U ⊆ V ↔ U ⊆ f ⁻¹' V :=
begin
  split,
    intro h,
    intros u hu,
    apply h,
    use u,
    split, assumption, refl,
  rintros h v ⟨u, hu, rfl⟩,
  apply h,
  assumption
end

variable [limits.has_colimits.{v} C]
def comap {f : X → Y} (hf : continuous f) : presheaf Y C ⥤ presheaf X C :=
{ obj := λ ℱ, {
    val := λ U, limits.colimit (
      { obj := λ V, ℱ V,
        map := λ V₁ V₂ j, ℱ.res' j.1.1,
        map_id' := λ _, ℱ.Hid _,
        map_comp' := λ _ _ _ _ _, ℱ.Hcomp _ _ _ _ _} :
          {V : opens Y // U ⊆ hf.comap V} ⥤ C), -- colimit of ℱ(V) as V runs through the opens containing f(U)
    res := λ U₁ U₂ hU, _,--category_theory.limits.colimit.desc _ _,
    Hid := _,
    Hcomp := _ } ,
  map := _,
  map_id' := _,
  map_comp' := _ }
