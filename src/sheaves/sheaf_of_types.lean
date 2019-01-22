import sheaves.presheaf_of_types

universes u v

namespace presheaf_of_types

variables {α : Type u} [T : topological_space α]
include T

-- Restriction map from U to U ∩ V.

def res_to_inter_left (F : presheaf_of_types α)
  {U V} (OU : T.is_open U) (OV : T.is_open V) :
  (F OU) → (F (T.is_open_inter U V OU OV)) :=
F.res OU (T.is_open_inter U V OU OV) (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right (F : presheaf_of_types α)
  {U V} (OU : T.is_open U) (OV : T.is_open V) :
  (F OV) → (F (T.is_open_inter U V OU OV)) :=
F.res OV (T.is_open_inter U V OU OV) (set.inter_subset_right U V)

-- Sheaf condition.

structure covering := 
{γ   : Type u} -- TODO: should this be v?
(Ui  : γ → set α)
(OUi : ∀ i, T.is_open (Ui i))

def covers (OC : covering) (U : set α) :=
(⋃ i : OC.γ, OC.Ui i) = U

def locality (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering) (OCU : covers OC U) (s t : F OU), 
(∀ (i : OC.γ),
F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) s =
F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) t) → 
s = t

def gluing (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering) (OCU : covers OC U),
∀ (s : Π (i : OC.γ), F (OC.OUi i)) (i j : OC.γ),
res_to_inter_left F (OC.OUi i) (OC.OUi j) (s i) = 
res_to_inter_right F (OC.OUi i) (OC.OUi j) (s j) → 
∃ (S : F OU), ∀ (i : OC.γ),
  F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) S = s i

end presheaf_of_types

-- Definition of a sheaf of types.

structure sheaf_of_types (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_types α)
(locality : presheaf_of_types.locality F)
(gluing   : presheaf_of_types.gluing F) 

section sheaf_of_types

variables {α : Type u} [T : topological_space α]
include T

instance : has_coe (sheaf_of_types α) (presheaf_of_types α) := 
⟨λ S, S.F⟩

def is_sheaf_of_types (F : presheaf_of_types α) :=
presheaf_of_types.locality F ∧ presheaf_of_types.gluing F

-- Sanity checks.

def bijective_gluing (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : presheaf_of_types.covering) 
(OCU : presheaf_of_types.covers OC U),
∀ (s : Π (i : OC.γ), F (OC.OUi i)) (i j : OC.γ),
presheaf_of_types.res_to_inter_left F (OC.OUi i) (OC.OUi j) (s i) = 
presheaf_of_types.res_to_inter_right F (OC.OUi i) (OC.OUi j) (s j) → 
∃! (S : F OU), ∀ (i : OC.γ),
  F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) S = s i

lemma sheaf_condition_bijective_gluing (F : presheaf_of_types α) :
presheaf_of_types.locality F ∧ presheaf_of_types.gluing F → bijective_gluing F :=
begin
  intros H,
  rcases H with ⟨HL, HG⟩,
  intros U OU OC OCU s i j Heq,
  have HS : ∃ (S : F OU), ∀ (i : OC.γ), F.res OU _ _ S = s i,
    apply HG OU OC OCU s i j Heq,
  rcases HS with ⟨S, HS⟩,
  have HU : ∀ (S' : F OU), (∀ (i : OC.γ), F.res OU _ _ S' = s i) → S' = S,
    intros S' HS',
    apply HL OU OC OCU S' S,
    intros k,
    rw HS k,
    rw HS' k,
  existsi S,
  simp,
  apply and.intro HS HU,
end

end sheaf_of_types
