import topology.basic
universe u 

variables {α : Type u} [T : topological_space α]

-- Lemmas about ⊆. TODO: Can this be automated better?

@[simp, refl] lemma subset_refl {U : set α} : U ⊆ U := 
  set.subset.refl U
@[simp, trans] lemma subset_trans {U V W : set α} : W ⊆ V → V ⊆ U → W ⊆ U :=
  set.subset.trans

-- Definition of a presheaf.

structure presheaf_of_types := 
(F     : Π {U}, T.is_open U → Type u)
(res   : ∀ {U V} (H : V ⊆ U) (OU : T.is_open U) (OV : T.is_open V), F OU → F OV)
(Hid   : ∀ {U} (OU : T.is_open U), res (by refl) OU OU = id)
(Hcomp : ∀ {U V W} (HUV : V ⊆ U) (HVW : W ⊆ V)
  (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W),
  res (subset_trans HVW HUV) OU OW = res HVW OV OW ∘ res HUV OU OV)

-- Simplification lemmas for Hid and Hcomp.

@[simp] lemma presheaf_of_types.Hcomp' (FPT : presheaf_of_types) :
∀ {U V W} (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HUV : V ⊆ U) (HVW : W ⊆ V) (s : FPT.F OU),
  (FPT.res (subset_trans HVW HUV) OU OW) s = (FPT.res HVW OV OW) ((FPT.res HUV OU OV) s) := 
λ U V W OU OV OW HUV HVW s, by rw FPT.Hcomp HUV HVW OU OV OW

@[simp] lemma presheaf_of_types.Hid' (FPT : presheaf_of_types) :
∀ {U} (OU : T.is_open U) (s : FPT.F OU),
  (FPT.res (by simp) OU OU) s = s := 
λ U OU s, by rw FPT.Hid OU; simp

-- Morphism of presheaves.

structure morphism_of_presheaves_of_types {α : Type u} [Tα : topological_space α] 
  (FPT : presheaf_of_types α) (GPT : presheaf_of_types α) :=
(morphism : ∀ U : set α, ∀ HU : Tα.is_open U, (FPT.F HU) → GPT.F HU)
(commutes : ∀ U V : set α, ∀ HU : Tα.is_open U, ∀ HV : Tα.is_open V, ∀ Hsub : V ⊆ U,
  (GPT.res U V HU HV Hsub) ∘ (morphism U HU) = (morphism V HV) ∘ (FPT.res U V HU HV Hsub))


def composition_of_morphisms_of_presheaves_of_types {α : Type u} [Tα : topological_space α]
  {FPT GPT HPT : presheaf_of_types α} (fg : morphism_of_presheaves_of_types FPT GPT)
  (gh : morphism_of_presheaves_of_types GPT HPT) :
morphism_of_presheaves_of_types FPT HPT :=
{ morphism := λ U HU, gh.morphism U HU ∘ fg.morphism U HU,
  commutes := λ U V HU HV Hsub, begin
    show (HPT.res U V HU HV Hsub ∘ gh.morphism U HU) ∘ fg.morphism U HU =
    gh.morphism V HV ∘ (fg.morphism V HV ∘ FPT.res U V HU HV Hsub),
    rw gh.commutes U V HU HV Hsub,
    rw ←fg.commutes U V HU HV Hsub,
  end }

def is_identity_morphism_of_presheaves_of_types {α : Type u} [Tα : topological_space α]
  {FPT : presheaf_of_types α} (phi: morphism_of_presheaves_of_types FPT FPT) :=
  ∀ (U : set α) (OU : Tα.is_open U), phi.morphism U OU = id

def is_isomorphism_of_presheaves_of_types {α : Type u} [Tα : topological_space α]
  {FPT : presheaf_of_types α} {GPT : presheaf_of_types α} (phi: morphism_of_presheaves_of_types FPT GPT) :=
  ∃ psi : morphism_of_presheaves_of_types GPT FPT, 
  is_identity_morphism_of_presheaves_of_types (composition_of_morphisms_of_presheaves_of_types phi psi)
  ∧ is_identity_morphism_of_presheaves_of_types (composition_of_morphisms_of_presheaves_of_types psi phi)

def are_isomorphic_presheaves_of_types {α : Type u} [Tα : topological_space α]
(FPT : presheaf_of_types α) (GPT : presheaf_of_types α) : Prop :=
∃ (fg : morphism_of_presheaves_of_types FPT GPT) (gf : morphism_of_presheaves_of_types GPT FPT),
  is_identity_morphism_of_presheaves_of_types (composition_of_morphisms_of_presheaves_of_types fg gf)
  ∧ is_identity_morphism_of_presheaves_of_types (composition_of_morphisms_of_presheaves_of_types gf fg)

-- Seems to me that stacks project implicitly claims presheaves form a category
-- so perhaps at some point one should check e.g. identity o phi = phi and
-- associativity of composition of morphisms. I didn't need these yet though.
