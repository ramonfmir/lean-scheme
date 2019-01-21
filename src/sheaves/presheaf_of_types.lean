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
(res   : ∀ {U V} (OU : T.is_open U) (OV : T.is_open V) (HUV : V ⊆ U), F OU → F OV)
(Hid   : ∀ {U} (OU : T.is_open U), res OU OU (set.subset.refl U)  = id)
(Hcomp : ∀ {U V W} (HVW : W ⊆ V) (HUV : V ⊆ U)
  (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W),
  res OU OW (set.subset.trans HVW HUV) = res OV OW HVW ∘ res OU OV HUV)

variables (β : Type u) [T : topological_space β]
instance : has_coe_to_fun (presheaf_of_types β) :=
⟨λ_, Π {U}, T.is_open U → Type v, presheaf_of_types.F⟩

namespace presheaf_of_types

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' {α : Type u} [T : topological_space α] 
(F : presheaf_of_types α) :
∀ {U V W} (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HVW : W ⊆ V) (HUV : V ⊆ U) (s : F OU),
  (F.res OU OW (set.subset.trans HVW HUV)) s = 
  (F.res OV OW HVW) ((F.res OU OV HUV) s) :=
λ U V W OU OV OW HVW HUV s, by rw F.Hcomp HVW HUV OU OV OW

@[simp] lemma Hid' {α : Type u} [T : topological_space α] 
(F : presheaf_of_types α) :
∀ {U} (OU : T.is_open U) (s : F OU),
  (F.res OU OU (set.subset.refl U)) s = s := 
λ U OU s, by rw F.Hid OU; simp

-- Morphism of presheaves.

structure morphism {α : Type u} [T : topological_space α] 
(F G      : presheaf_of_types α) :=
(map      : ∀ {U} (OU : T.is_open U), F OU → G OU)
(commutes : ∀ {U V} (HUV : V ⊆ U) (OU : T.is_open U) (OV : T.is_open V),
  (G.res OU OV HUV) ∘ (map OU) = (map OV) ∘ (F.res OU OV HUV))

namespace morphism

def comp {α : Type u} [T : topological_space α]
  {F G H : presheaf_of_types α} 
  (fg : morphism F G)
  (gh : morphism G H) : 
  morphism F H :=
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
  {F G : presheaf_of_types α} (fg : morphism F G) :=
  ∃ gf : morphism G F, 
    is_identity (fg ⊚ gf)
  ∧ is_identity (gf ⊚ fg)

end morphism

-- Isomorphic presheaves of types.

def are_isomorphic {α : Type u} [T : topological_space α] 
(F G : presheaf_of_types α) : Prop :=
∃ (fg : morphism F G) (gf : morphism G F),
    morphism.is_identity (fg ⊚ gf)
  ∧ morphism.is_identity (gf ⊚ fg)

end presheaf_of_types
