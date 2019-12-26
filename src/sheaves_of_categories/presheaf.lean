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
(res'   : ∀ (U V) (HVU : V ⊆ U), val U ⟶ val V)
(Hid'   : ∀ (U), res' U U (set.subset.refl U) = 𝟙 (val U))
(Hcomp' : ∀ (U V W) (HWV : W ⊆ V) (HVU : V ⊆ U),
  res' U W (set.subset.trans HWV HVU) = res' U V HVU ≫ res' V W HWV)

open topological_space lattice

namespace topological_space.presheaf

variables {C : Type u} [𝒞 : category.{v} C]
variables {X : Type v} [topological_space X]
include 𝒞

-- I don't know why they used (U V), this changes it to {U V}
def res : ∀ (ℱ : presheaf X C) {U V : opens X} (HVU : V ⊆ U), ℱ.val U ⟶ ℱ.val V := res'

-- Simplification lemmas for Hid and Hcomp.
@[simp] theorem Hid : ∀ (ℱ : presheaf X C) (U : opens X), ℱ.res (set.subset.refl U) = 𝟙 (ℱ.val U) :=
Hid'

@[simp] theorem Hcomp : ∀ (ℱ : presheaf X C) {U V W : opens X} (HWV : W ⊆ V) (HVU : V ⊆ U),
  ℱ.res (set.subset.trans HWV HVU) = ℱ.res HVU ≫ ℱ.res HWV := Hcomp'

instance : has_coe_to_fun (topological_space.presheaf X C) :=
{ F := λ ℱ, opens X → C,
  coe := topological_space.presheaf.val}

-- simp lemma to get ℱ.val U back into ℱ U form
@[simp] lemma val_eq_coe {ℱ : presheaf X C} {U : opens X} : ℱ.val U = ℱ U := rfl

-- presheaves are a category.
structure morphism (ℱ 𝒢 : presheaf X C) :=
(map      : ∀ (U), ℱ U ⟶ 𝒢 U)
(commutes' : ∀ (U V) (HVU : V ⊆ U),
  (map U) ≫ (𝒢.res HVU) = (ℱ.res HVU) ≫ (map V))

variables {ℱ 𝒢 : presheaf X C}

-- notation
instance : has_hom (presheaf X C) := ⟨morphism⟩

namespace morphism

instance : has_coe_to_fun (morphism ℱ 𝒢) :=
{ F := λ φ, Π (U : opens X), ℱ U ⟶ 𝒢 U,
  coe := λ φ, φ.map}

@[simp] lemma commutes (φ : ℱ ⟶ 𝒢): ∀ {U V : opens X} (HVU : V ⊆ U),
  φ U ≫ 𝒢.res HVU = ℱ.res HVU ≫ φ V := φ.commutes'

@[ext] def ext (φ ψ : ℱ ⟶ 𝒢) : (φ : ∀ (U : opens X), ℱ U ⟶ 𝒢 U) = ψ → φ = ψ :=
begin
  intro h,
  cases φ, cases ψ, unfold_coes at h, dsimp at h, simp [h],
end

end morphism

-- Morphism of presheaves.
instance category_struct : category_struct (presheaf X C) :=
{ hom := morphism,--∀ ℱ 𝒢 (U), ℱ U ⟶ 𝒢 U),
  id := λ ℱ, {
    map := λ U, 𝟙 (ℱ U),
    commutes' := begin
      intros U V HVU, cases V, cases U, dsimp at *, simp at *,
    end}, -- is there a better tactic?
  comp := λ ℱ 𝒢 ℋ φ ψ, {
    map := λ U, (φ U) ≫ (ψ U),--begin sorry end,--λ U, φ U ≫ ψ U,
    commutes' := begin intros,
    -- I surely want automation to do this.
      show (φ U ≫ ψ U) ≫ ℋ.res HVU = ℱ.res HVU ≫ φ V ≫ ψ V,
      rw category.assoc,
      have X1 := φ.commutes, have Xφ := X1 HVU,
      have X2 := ψ.commutes, have Xψ := X2 HVU,
      rw ψ.commutes,
      rw ←category.assoc,
      -- tidy just makes everything explode at this point
      rw φ.commutes,
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
