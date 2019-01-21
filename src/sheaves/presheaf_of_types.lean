import topology.basic

universes u v

-- -- Lemmas about ⊆. TODO: Can this be automated?

-- @[simp, refl] lemma subset_refl {U : set α} : U ⊆ U := 
--   set.subset.refl U

-- @[simp, trans] lemma subset_trans {U V W : set α} : W ⊆ V → V ⊆ U → W ⊆ U :=
--   set.subset.trans

-- Definition of a presheaf.

structure presheaf_of_types (α : Type u) [T : topological_space α] := 
(F     : Π {U}, T.is_open U → Type v)
(res   : ∀ {U V} (OU : T.is_open U) (OV : T.is_open V) (HVU : V ⊆ U), F OU → F OV)
(Hid   : ∀ {U} (OU : T.is_open U), res OU OU (set.subset.refl U)  = id)
(Hcomp : ∀ {U V W} (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HWV : W ⊆ V) (HVU : V ⊆ U),
  res OU OW (set.subset.trans HWV HVU) = res OV OW HWV ∘ res OU OV HVU)

namespace presheaf_of_types

variables {α : Type u} [T : topological_space α]
include T

-- Coercing presheaves to F : U → Type.

instance : has_coe_to_fun (presheaf_of_types α) :=
{ F := λ _, Π {U}, T.is_open U → Type v,
  coe := presheaf_of_types.F }

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' (F : presheaf_of_types α) :
∀ {U V W} (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HWV : W ⊆ V) (HVU : V ⊆ U) (s : F OU),
  (F.res OU OW (set.subset.trans HWV HVU)) s = 
  (F.res OV OW HWV) ((F.res OU OV HVU) s) :=
λ U V W OU OV OW HWV HVU s, by rw F.Hcomp OU OV OW HWV HVU

@[simp] lemma Hid' (F : presheaf_of_types α) :
∀ {U} (OU : T.is_open U) (s : F OU),
  (F.res OU OU (set.subset.refl U)) s = s := 
λ U OU s, by rw F.Hid OU; simp

-- Morphism of presheaves.

structure morphism (F G : presheaf_of_types α) :=
(map      : ∀ {U} (OU : T.is_open U), F OU → G OU)
(commutes : ∀ {U V} (OU : T.is_open U) (OV : T.is_open V) (HVU : V ⊆ U),
  (G.res OU OV HVU) ∘ (map OU) = (map OV) ∘ (F.res OU OV HVU))

namespace morphism

def comp
  {F G H : presheaf_of_types α} 
  (fg : morphism F G)
  (gh : morphism G H) : 
  morphism F H :=
{ map := λ U OU, gh.map OU ∘ fg.map OU,
  commutes := λ U V OU OV HVU,
    begin
      rw [←function.comp.assoc, gh.commutes OU OV HVU], symmetry,
      rw [function.comp.assoc, ←fg.commutes OU OV HVU]
    end }

infixl `⊚`:80 := comp

def is_identity {F : presheaf_of_types α} (ff : morphism F F) :=
  ∀ {U} (OU : T.is_open U), ff.map OU = id

def is_isomorphism {F G : presheaf_of_types α} (fg : morphism F G) :=
  ∃ gf : morphism G F, 
    is_identity (fg ⊚ gf)
  ∧ is_identity (gf ⊚ fg)

end morphism

-- Isomorphic presheaves of types.

def are_isomorphic (F G : presheaf_of_types α) :=
∃ (fg : morphism F G) (gf : morphism G F),
    morphism.is_identity (fg ⊚ gf)
  ∧ morphism.is_identity (gf ⊚ fg)

end presheaf_of_types
