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
(res   : ∀ {U V} (H : V ⊆ U) (OU : T.is_open U) (OV : T.is_open V), F OU → F OV)
(Hid   : ∀ {U} (OU : T.is_open U), res (set.subset.refl U) OU OU = id)
(Hcomp : ∀ {U V W} (HVW : W ⊆ V) (HUV : V ⊆ U)
  (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W),
  res (set.subset.trans HVW HUV) OU OW = res HVW OV OW ∘ res HUV OU OV)

namespace presheaf_of_types

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' {α : Type u} [T : topological_space α] 
(FPT : presheaf_of_types α) :
∀ {U V W} (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HVW : W ⊆ V) (HUV : V ⊆ U) (s : FPT.F OU),
  (FPT.res (set.subset.trans HVW HUV) OU OW) s = 
  (FPT.res HVW OV OW) ((FPT.res HUV OU OV) s) :=
λ U V W OU OV OW HVW HUV s, by rw FPT.Hcomp HVW HUV OU OV OW

@[simp] lemma Hid' {α : Type u} [T : topological_space α] 
(FPT : presheaf_of_types α) :
∀ {U} (OU : T.is_open U) (s : FPT.F OU),
  (FPT.res (set.subset.refl U) OU OU) s = s := 
λ U OU s, by rw FPT.Hid OU; simp

-- Morphism of presheaves.

structure morphism {α : Type u} [T : topological_space α] 
(FPT GPT : presheaf_of_types α) :=
(map      : ∀ {U} (OU : T.is_open U), FPT.F OU → GPT.F OU)
(commutes : ∀ {U V} (HUV : V ⊆ U) (OU : T.is_open U) (OV : T.is_open V),
  (GPT.res HUV OU OV) ∘ (map OU) = (map OV) ∘ (FPT.res HUV OU OV))

namespace morphism

def comp {α : Type u} [T : topological_space α]
  {FPT GPT HPT : presheaf_of_types α} 
  (fg : morphism FPT GPT)
  (gh : morphism GPT HPT) : 
  morphism FPT HPT :=
{ map := λ U OU, gh.map OU ∘ fg.map OU,
  commutes := λ U V OU OV HUV,
    begin
      rw [←function.comp.assoc, gh.commutes OU OV HUV], symmetry,
      rw [function.comp.assoc, ←fg.commutes OU OV HUV]
    end }

infixl `⊚`:80 := comp

def is_identity {α : Type u} [T : topological_space α]
  {FPT : presheaf_of_types α} (ff : morphism FPT FPT) :=
  ∀ {U} (OU : T.is_open U), ff.map OU = id

def is_isomorphism {α : Type u} [T : topological_space α]
  {FPT GPT : presheaf_of_types α} (fg : morphism FPT GPT) :=
  ∃ gf : morphism GPT FPT, 
    is_identity (fg ⊚ gf)
  ∧ is_identity (gf ⊚ fg)

end morphism

-- Isomorphic presheaves of types.

def are_isomorphic {α : Type u} [T : topological_space α] 
(FPT GPT : presheaf_of_types α) : Prop :=
∃ (fg : morphism FPT GPT) (gf : morphism GPT FPT),
    morphism.is_identity (fg ⊚ gf)
  ∧ morphism.is_identity (gf ⊚ fg)

end presheaf_of_types
