import category_theory.limits.limits

universes v w u

namespace category_theory

inductive pullback_diagram : Type v
| base_left | base_right | target

namespace pullback_diagram

inductive hom : pullback_diagram → pullback_diagram → Type v
| id_base_left : hom base_left base_left
| id_base_right : hom base_right base_right
| id_target : hom target target
| to_target_left : hom base_left target
| to_target_right : hom base_right target

def id : Π X : pullback_diagram.{v}, hom X X
| base_left  := hom.id_base_left
| base_right := hom.id_base_right
| target     := hom.id_target

def comp : Π X Y Z : pullback_diagram.{v}, hom X Y → hom Y Z → hom X Z
| _ _ _ hom.id_base_left    g             := g
| _ _ _ hom.id_base_right   g             := g
| _ _ _ hom.id_target       g             := g
| _ _ _ hom.to_target_left  hom.id_target := hom.to_target_left
| _ _ _ hom.to_target_right hom.id_target := hom.to_target_right

instance : small_category pullback_diagram.{v} :=
{ hom := hom,
  id := id,
  comp := comp,
  comp_id' := λ X Y f, by cases f; refl,
  id_comp' := λ X Y f, by cases f; refl,
  assoc' := λ W X Y Z f g h, by cases f; cases g; cases h; refl }

def to_category {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  pullback_diagram.{w} ⥤ C :=
{ obj := λ p, pullback_diagram.rec_on p X Y Z,
  map := λ p q h, @hom.rec_on (λ p' q' h', (pullback_diagram.rec_on p' X Y Z : C) ⟶ pullback_diagram.rec_on q' X Y Z) p q h
    (𝟙 X) (𝟙 Y) (𝟙 Z) f g,
  map_id' := λ p, by cases p; refl,
  map_comp' := λ p q r h1 h2, by cases h1; cases h2; dsimp only [category_struct.comp, comp]; simp only [category.comp_id, category.id_comp] }

def to_category_cone {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (W : C) (f' : W ⟶ X) (g' : W ⟶ Y) (h : f' ≫ f = g' ≫ g) :
  limits.cone (to_category f g) :=
{ X := W,
  π :=
  { app := λ p, pullback_diagram.rec_on p f' g' (f' ≫ f),
    naturality' := λ p q f, by cases f; dsimp only [functor.const, to_category]; simp only [category.comp_id, category.id_comp, h] } }

end pullback_diagram

@[class] def has_pullback (C : Type u) [category.{v} C] : Type (max u v) :=
limits.has_limits_of_shape pullback_diagram.{v} C

section has_pullback

variables {C : Type u} [𝒞 : category.{v} C] [P : has_pullback.{v} C]
include 𝒞 P

def pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : C :=
(P (pullback_diagram.to_category f g)).cone.X

def pullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : pullback f g ⟶ X :=
(P (pullback_diagram.to_category f g)).cone.π.app pullback_diagram.base_left

def pullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : pullback f g ⟶ Y :=
(P (pullback_diagram.to_category f g)).cone.π.app pullback_diagram.base_right

def pullback.corec {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (W : C) (f' : W ⟶ X) (g' : W ⟶ Y) (h : f' ≫ f = g' ≫ g) : W ⟶ pullback f g :=
(P (pullback_diagram.to_category f g)).is_limit.lift (pullback_diagram.to_category_cone f g W f' g' h)

end has_pullback

class has_site (C : Type u) [category.{v} C] [has_pullback C] : Type (max u v) :=
(cov : Π U : C, set (set (Σ V, V ⟶ U)))
(iso_mem : ∀ {U V : C} (e : V ≅ U), { sigma.mk V e.1 } ∈ cov U)
(comp_mem : ∀ {U : C} (S : set (Σ V, V ⟶ U)) (HS : S ∈ cov U)
  (F : Π m : Σ V, V ⟶ U, m ∈ S → set (Σ V, V ⟶ m.1)),
  (∀ m hm, F m hm ∈ cov m.1) →
  { m | ∃ t ∈ S, ∃ u ∈ F t H, (⟨u.1, u.2 ≫ t.2⟩ : Σ V, V ⟶ U) = m } ∈ cov U)
(pullback_mem : ∀ {U} (S ∈ cov U) (V) (f : V ⟶ U),
  { m | ∃ t ∈ S, (⟨_, pullback.fst f t.2⟩ : Σ W, W ⟶ V) = m } ∈ cov V)

end category_theory
