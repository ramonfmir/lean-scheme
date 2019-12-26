/-
    Sheaf (of categories).

    https://stacks.math.columbia.edu/tag/006S
-/

import sheaves.covering.covering
import sheaves_of_categories.presheaf
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers

universes v u

open topological_space lattice category_theory

variables {X : Type v} [topological_space X]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

instance XYZ: has_coe_to_fun (presheaf X C) :=
{F := λ (ℱ : presheaf X C), opens X → C, coe := presheaf.val}

namespace topological_space.presheaf

def res_to_inter_left (ℱ : presheaf X C) (U V : opens X)
: ((ℱ : opens X → C) U) ⟶ ((ℱ : opens X → C) (U ∩ V)) :=
ℱ.res (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right (ℱ : presheaf X C) (U V : opens X)
: ((ℱ : opens X → C) V) ⟶ ((ℱ : opens X → C) (U ∩ V)) :=
ℱ.res (set.inter_subset_right U V)

open category_theory.limits

variable [has_products.{v} C]

def prod_res (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  ℱ U ⟶ ∏ (λ i, ℱ.val (OC.Uis i)) :=
pi.lift (λ i, ℱ.res $ subset_covering i)

def res_left (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  ∏ (λ i, ℱ.val (OC.Uis i)) ⟶ ∏ (λ jk : OC.γ × OC.γ, ℱ.val (OC.Uis jk.1 ∩ OC.Uis jk.2)) :=
(pi.lift (λ jk : OC.γ × OC.γ, ((pi.π (λ i, ℱ (OC.Uis i)) jk.1) ≫
(ℱ.res_to_inter_left _ _))))

def res_right (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  ∏ (λ i, ℱ.val (OC.Uis i)) ⟶ ∏ (λ jk : OC.γ × OC.γ, ℱ.val (OC.Uis jk.1 ∩ OC.Uis jk.2)) :=
(pi.lift (λ jk : OC.γ × OC.γ, ((pi.π (λ i, ℱ.val (OC.Uis i)) jk.2) ≫
(ℱ.res_to_inter_right _ _))))

variable [has_equalizers.{v} C]

lemma res_commutes (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  prod_res ℱ OC ≫ res_left ℱ OC = prod_res ℱ OC ≫ res_right ℱ OC :=
begin
  unfold res_left, -- why?
  unfold res_right, -- why?
  unfold prod_res,
  ext jk,
  -- carefully avoiding non-terminal simp
  suffices : ℱ.res.{v u} (subset_covering.{v} (jk.fst)) ≫
      ℱ.res_to_inter_left.{v u} (OC.Uis (jk.fst)) (OC.Uis (jk.snd)) =
    ℱ.res.{v u} (subset_covering.{v} (jk.snd)) ≫
      ℱ.res_to_inter_right.{v u} (OC.Uis (jk.fst)) (OC.Uis (jk.snd)),
    dsimp, simpa using this, -- non-terminal dsimp
  convert (rfl : ℱ.res (show OC.Uis jk.1 ∩ OC.Uis jk.2 ⊆ U, from _) = ℱ.res _),
    exact (ℱ.Hcomp _ _).symm,
  exact (ℱ.Hcomp _ _).symm,
end

-- the canonical map from ℱ U to the equalizer of Π ℱ (U_i) → Π ℱ (U_j ∩ U_k)
def map_to_equalizer (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  ℱ U ⟶ _ :=
equalizer.lift
(ℱ.res_left OC)
(ℱ.res_right OC)
(ℱ.prod_res OC)
(ℱ.res_commutes OC)

-- Sheaf condition.

section sheaf_condition

open category_theory.limits

variable [has_products.{v} C]

-- I'm not sure how relevant this is now; sheaf axiom is that something is an isomorphism,
-- not just mono and epi
def locality (ℱ : presheaf X C) : Prop :=
∀ {U : opens X} (OC : covering.{v} U),
mono (ℱ.prod_res OC)

variable [has_equalizers.{v} C]

def gluing (ℱ : presheaf X C) : Prop :=
∀ {U : opens X} (OC : covering U),
epi (ℱ.map_to_equalizer OC)

/-- creates the cone with vertex ℱ U for the equalizer diagram -/
def to_fork (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  fork (ℱ.res_left OC) (ℱ.res_right OC) :=
fork.of_ι (ℱ.prod_res OC) (ℱ.res_commutes OC)

end sheaf_condition

end topological_space.presheaf

-- Definition of a sheaf of objects in a category.

open category_theory.limits

namespace topological_space

variable [has_products.{v} C]
variable [has_equalizers.{v} C]

omit 𝒞

-- this is data
structure sheaf (X : Type v) [topological_space X] (C : Type u) [category.{v} C]
  [has_products.{v} C] [has_equalizers.{v} C]
extends presheaf X C :=
(is_limit : ∀ {U : opens X} (OC : covering U),
   is_limit (topological_space.presheaf.to_fork to_presheaf OC))

include 𝒞

instance : has_coe_to_fun (sheaf X C) :=
{ F := λ ℱ, opens X → C,
  coe := λ ℱ, topological_space.sheaf.to_presheaf ℱ}

namespace sheaf

def map_to_equalizer (ℱ : sheaf X C) {U : opens X} (OC : covering U) :=
  (ℱ.to_presheaf).map_to_equalizer OC

instance : category (sheaf X C) :=
{ hom := λ ℱ 𝒢, ℱ.to_presheaf ⟶ 𝒢.to_presheaf,
  id := λ ℱ, 𝟙 (ℱ.to_presheaf),
  comp := λ ℱ 𝒢 ℋ f g, f ≫ g,
  id_comp' := by simp,
  comp_id' := by simp,
  assoc' := by intros;simp }

end sheaf

end topological_space

open topological_space

variable [has_products.{v} C]
variable [has_equalizers.{v} C]

-- this is no longer right: monic and epi don't imply iso
--def is_sheaf (F : presheaf X C) :=
--locality F ∧ gluing F

def condition (ℱ : sheaf X C) {U : opens X} (OC : covering U) :
  ℱ.to_presheaf.to_fork OC ≅
    (limit.cone (parallel_pair (ℱ.to_presheaf.res_left OC) (ℱ.to_presheaf.res_right OC))) :=
is_limit.unique_up_to_iso (ℱ.is_limit OC) (limit.is_limit _)
