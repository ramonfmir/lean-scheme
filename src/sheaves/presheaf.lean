/-
  Presheaf (of types).

  https://stacks.math.columbia.edu/tag/006D 
-/

import topology.basic

universes u v

-- Definition of a presheaf.

open topological_space lattice

structure presheaf (α : Type u) [T : topological_space α] := 
(F     : opens α → Type v)
(res   : ∀ (U V) (HVU : V ⊆ U), F U → F V)
(Hid   : ∀ (U), res U U (set.subset.refl U) = id)
(Hcomp : ∀ (U V W) (HWV : W ⊆ V) (HVU : V ⊆ U),
  res U W (set.subset.trans HWV HVU) = res V W HWV ∘ res U V HVU)

namespace presheaf

variables {α : Type u} [T : topological_space α]
include T

-- Coercing presheaves to F : U → Type.

instance : has_coe_to_fun (presheaf α) :=
{ F := λ _, opens α → Type v,
  coe := presheaf.F }

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' (F : presheaf α) :
∀ (U V W) (HWV : W ⊆ V) (HVU : V ⊆ U) (s : F U),
  (F.res U W (set.subset.trans HWV HVU)) s = 
  (F.res V W HWV) ((F.res U V HVU) s) :=
λ U V W HWV HVU s, by rw F.Hcomp U V W HWV HVU

@[simp] lemma Hid' (F : presheaf α) :
∀ (U) (s : F U),
  (F.res U U (set.subset.refl U)) s = s := 
λ U s, by rw F.Hid U; simp

-- Morphism of presheaves.

structure morphism (F G : presheaf α) :=
(map      : ∀ (U), F U → G U)
(commutes : ∀ (U V) (HVU : V ⊆ U),
  (G.res U V HVU) ∘ (map U) = (map V) ∘ (F.res U V HVU))

namespace morphism

def comp
  {F G H : presheaf α} 
  (fg : morphism F G)
  (gh : morphism G H) : 
  morphism F H :=
{ map := λ U, gh.map U ∘ fg.map U,
  commutes := λ U V HVU,
    begin
      rw [←function.comp.assoc, gh.commutes U V HVU], symmetry,
      rw [function.comp.assoc, ←fg.commutes U V HVU]
    end }

def is_identity {F : presheaf α} (ff : morphism F F) :=
  ∀ (U), ff.map U = id

def is_isomorphism {F G : presheaf α} (fg : morphism F G) :=
  ∃ gf : morphism G F, 
    is_identity (comp fg gf)
  ∧ is_identity (comp gf fg)

end morphism

-- Isomorphic presheaves of types.

def are_isomorphic (F G : presheaf α) :=
∃ (fg : morphism F G) (gf : morphism G F),
    morphism.is_identity (morphism.comp fg gf)
  ∧ morphism.is_identity (morphism.comp gf fg)

end presheaf
