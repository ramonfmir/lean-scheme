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

-- Restriction map from U to U ∩ V.

set_option pp.universes true

namespace topological_space.presheaf

def res_to_inter_left (ℱ : presheaf X C) (U V : opens X)
: ((ℱ : opens X → C) U) ⟶ ((ℱ : opens X → C) (U ∩ V)) :=
ℱ.res' (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right (ℱ : presheaf X C) (U V : opens X)
: ((ℱ : opens X → C) V) ⟶ ((ℱ : opens X → C) (U ∩ V)) :=
ℱ.res' (set.inter_subset_right U V)

open category_theory.limits

variable [has_products.{v} C]

def prod_res (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  ℱ U ⟶ ∏ (λ i, ℱ.val (OC.Uis i)) :=
pi.lift (λ i, ℱ.res' $ subset_covering i)

variable [has_equalizers.{v} C]

-- the canonical map from ℱ U to the equalizer of Π ℱ (U_i) → Π ℱ (U_j ∩ U_k)
def map_to_equalizer (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
  ℱ U ⟶ _ :=
equalizer.lift
(pi.lift.{v} (λ jk : OC.γ × OC.γ, ((pi.π (λ i, ℱ (OC.Uis i)) jk.1) ≫
(ℱ.res_to_inter_left (OC.Uis jk.1 : opens X) (OC.Uis jk.2 : opens X)
-- why do I need to say this
  : ℱ (OC.Uis (jk.fst)) ⟶ ℱ (OC.Uis (jk.fst) ∩ OC.Uis (jk.snd))
))))
(pi.lift (λ jk : OC.γ × OC.γ, ((pi.π (λ i, ℱ.val (OC.Uis i)) jk.2) ≫
(ℱ.res_to_inter_right _ _))))
(pi.lift (λ i, ℱ.res' $ subset_covering i)
-- why do I need to say this
    : ℱ U ⟶ ∏ (λ i, ℱ.val (OC.Uis i)
))
begin
  ext jk,
  suffices : presheaf.res'.{v u} ℱ (subset_covering.{v} (jk.fst)) ≫
      topological_space.presheaf.res_to_inter_left.{v u} ℱ (OC.Uis (jk.fst)) (OC.Uis (jk.snd)) =
    presheaf.res'.{v u} ℱ (subset_covering.{v} (jk.snd)) ≫
      topological_space.presheaf.res_to_inter_right.{v u} ℱ (OC.Uis (jk.fst)) (OC.Uis (jk.snd)),
    dsimp, simpa using this, -- non-terminal dsimp
  convert (rfl : ℱ.res' (show OC.Uis jk.1 ∩ OC.Uis jk.2 ⊆ U, from _) = ℱ.res' _),
    exact (ℱ.Hcomp' _ _ _ _ _).symm,
  exact (ℱ.Hcomp' _ _ _ _ _).symm,
end

#check topological_space.presheaf.map_to_equalizer

end topological_space.presheaf

-- Sheaf condition.

section sheaf_condition

open category_theory.limits

variable [has_products.{v} C]

-- this was a monumental effort.
-- Why not just
-- mono (pi.lift (λ i, (ℱ.res' (subset_covering i))))

def locality (ℱ : presheaf X C) : Prop :=
∀ {U : opens X} (OC : covering.{v} U),
mono (ℱ.prod_res OC)

--example (ℱ : presheaf X C) {U : opens X} (OC : covering U) : C := ∏ (λ i, ℱ.val (OC.Uis i))
--example (ℱ : presheaf X C) {U : opens X} (OC : covering U) : C :=
--  ∏ (λ jk : OC.γ × OC.γ, ℱ.val (OC.Uis jk.1 ∩ OC.Uis jk.2))

variable [has_equalizers.{v} C]

--example (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
--   ∏ (λ i, ℱ.val (OC.Uis i)) ⟶
--   ∏ (λ jk : OC.γ × OC.γ, ℱ.val (OC.Uis jk.1 ∩ OC.Uis jk.2)) :=
--pi.lift (λ jk : OC.γ × OC.γ, ((pi.π (λ i, ℱ.val (OC.Uis i)) jk.1) ≫
--(ℱ.res_to_inter_left _ _)))

--example (ℱ : presheaf X C) {U : opens X} (OC : covering U) :
--   ∏ (λ i, ℱ.val (OC.Uis i)) ⟶
--   ∏ (λ jk : OC.γ × OC.γ, ℱ.val (OC.Uis jk.1 ∩ OC.Uis jk.2)) :=
--pi.lift (λ jk : OC.γ × OC.γ, ((pi.π (λ i, ℱ.val (OC.Uis i)) jk.2) ≫
--(ℱ.res_to_inter_right _ _)))

def gluing (ℱ : presheaf X C) : Prop :=
∀ {U : opens X} (OC : covering U),
epi (-- the map from ℱ(U) to the equalizer of the two res maps : Π i, ℱ(U_i) → Π_{j,k}(ℱ(U_jk})
--coming from the fact that res res = res = res res
ℱ.map_to_equalizer OC)

end sheaf_condition

-- Definition of a sheaf of types.

open category_theory.limits

variable [has_products.{v} C]
variable [has_equalizers.{v} C]

structure sheaf (X : Type v) [topological_space X]
extends presheaf X C :=
(locality : locality to_presheaf)
(gluing   : ∀ {U : opens X} (OC : covering U), gluing to_presheaf)

def is_sheaf (F : presheaf X C) :=
locality F ∧ gluing F

def is_sheaf_def (ℱ : presheaf X C) (h : is_sheaf ℱ) {U : opens X} (OC : covering U) :
  is_iso (ℱ.prod_res OC) :=
{ inv := begin -- data
    cases h,
    replace h_left := h_left OC,
    replace h_right := h_right OC,
    sorry
  end,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
