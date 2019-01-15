import analysis.topology.topological_space
universe u 

structure presheaf_of_types (α : Type u) [T : topological_space α] := 
(F : Π {U : set α}, T.is_open U → Type u)
(res : ∀ (U V : set α) (OU : T.is_open U) (OV : T.is_open V) (H : V ⊆ U), 
  (F OU) → (F OV))
(Hid : ∀ (U : set α) (OU : T.is_open U), (res U U OU _ (set.subset.refl U)) = id)  
(Hcomp : ∀ (U V W : set α) (OU : T.is_open U) (OV : T.is_open V) (OW : T.is_open W)
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res U W OU OW (set.subset.trans HVW HUV)) = (res V W OV _ HVW) ∘ (res U V _ _ HUV) )

@[simp] lemma presheaf_of_types.Hcomp' {X : Type u} [TX : topological_space X]
  (FPT : presheaf_of_types X) :
∀ {U V W : set X} (OU : TX.is_open U) (OV : TX.is_open V) (OW : TX.is_open W)
  (HUV : V ⊆ U) (HVW : W ⊆ V) (s : FPT.F OU),
  (FPT.res U W OU OW (set.subset.trans HVW HUV)) s = 
    (FPT.res V W OV OW HVW) ((FPT.res U V OU OV HUV) s) := begin
    intros U V W OU OV OW HUV HVW s,
      show _ = ((FPT.res V W OV OW HVW) ∘ (FPT.res U V OU OV HUV)) s,
      rw FPT.Hcomp,
    end

@[simp] lemma presheaf_of_types.Hid' {X : Type u} [TX : topological_space X]
  (FPT : presheaf_of_types X) :
∀ {U : set X} (OU : TX.is_open U) (s : FPT.F OU),
  (FPT.res U U OU OU (set.subset.refl U)) s = s := λ U OU s,by rw FPT.Hid U OU;simp

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
