import topology.basic

universes u v
variables {α : Type u} [T : topological_space α]

-- Lemmas about ⊆. TODO: Can this be automated?

@[simp, refl] lemma subset_refl {U : set α} : U ⊆ U := 
  set.subset.refl U

@[simp, trans] lemma subset_trans {U V W : set α} : W ⊆ V → V ⊆ U → W ⊆ U :=
  set.subset.trans

-- Definition of a presheaf.

structure presheaf_of_types := 
(F     : Π {U}, T.is_open U → Type v)
(res   : ∀ {U V} (H : V ⊆ U) (OU : T.is_open U) (OV : T.is_open V), F OU → F OV)
(Hid   : ∀ {U} (OU : T.is_open U), res (subset_refl) OU OU = id)
(Hcomp : ∀ {U V W} (HVW : W ⊆ V) (HUV : V ⊆ U)
  (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W),
  res (subset_trans HVW HUV) OU OW = res HVW OV OW ∘ res HUV OU OV)

namespace presheaf_of_types

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma Hcomp' (FPT : presheaf_of_types) :
∀ {U V W} (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HVW : W ⊆ V) (HUV : V ⊆ U) (s : FPT.F OU),
  (FPT.res (subset_trans HVW HUV) OU OW) s = 
  (FPT.res HVW OV OW) ((FPT.res HUV OU OV) s) :=
λ U V W OU OV OW HVW HUV s, by rw FPT.Hcomp HVW HUV OU OV OW

@[simp] lemma Hid' (FPT : presheaf_of_types) :
∀ {U} (OU : T.is_open U) (s : FPT.F OU),
  (FPT.res (subset_refl) OU OU) s = s := 
λ U OU s, by rw FPT.Hid OU; simp

-- Morphism of presheaves. TODO: Why do I have to write @presheaf_of_types α T?

structure morphism (FPT GPT : @presheaf_of_types α T) :=
(morphism : ∀ {U} (OU : T.is_open U), FPT.F OU → GPT.F OU)
(commutes : ∀ {U V} (OU : T.is_open U) (OV : T.is_open V) (HUV : V ⊆ U),
  (GPT.res HUV OU OV) ∘ (morphism OU) = (morphism OV) ∘ (FPT.res HUV OU OV))

namespace morphism

def comp
  {FPT GPT HPT : @presheaf_of_types α T} 
  (fg : presheaf_of_types.morphism FPT GPT)
  (gh : presheaf_of_types.morphism GPT HPT) : 
  presheaf_of_types.morphism FPT HPT :=
{ morphism := λ U OU, gh.morphism OU ∘ fg.morphism OU,
  commutes := λ U V OU OV HUV,
    begin
      rw [←function.comp.assoc, gh.commutes OU OV HUV], symmetry,
      rw [function.comp.assoc, ←fg.commutes OU OV HUV]
    end
}

def is_identity
  {FPT : @presheaf_of_types α T} (ff: presheaf_of_types.morphism FPT FPT) :=
  ∀ {U} (OU : T.is_open U), ff.morphism OU = id

def is_isomorphism
  {FPT GPT : @presheaf_of_types α T} (fg: presheaf_of_types.morphism FPT GPT) :=
  ∃ gf : presheaf_of_types.morphism GPT FPT, 
    presheaf_of_types.morphism.is_identity (presheaf_of_types.morphism.comp fg gf)
  ∧ presheaf_of_types.morphism.is_identity (presheaf_of_types.morphism.comp gf fg)

end morphism

-- Isomorphic presheaves.

def are_isomorphic (FPT GPT : @presheaf_of_types α T) : Prop :=
∃ (fg : presheaf_of_types.morphism FPT GPT) (gf : presheaf_of_types.morphism GPT FPT),
    presheaf_of_types.morphism.is_identity (presheaf_of_types.morphism.comp fg gf)
  ∧ presheaf_of_types.morphism.is_identity (presheaf_of_types.morphism.comp gf fg)

end presheaf_of_types
