import sheaves.presheaf_of_types

universes u v

-- Restriction map from U to U ∩ V.

def res_to_inter_left {α : Type u} [T : topological_space α] 
  (F : presheaf_of_types α)
  {U V} (OU : T.is_open U) (OV : T.is_open V) :
  (F OU) → (F (T.is_open_inter U V OU OV)) :=
F.res OU (T.is_open_inter U V OU OV) (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right {α : Type u} [T : topological_space α]
  (F : presheaf_of_types α)
  {U V} (OU : T.is_open U) (OV : T.is_open V) :
  (F OV) → (F (T.is_open_inter U V OU OV)) :=
F.res OV (T.is_open_inter U V OU OV) (set.inter_subset_right U V)

-- Sheaf condition.

structure covering (α : Type u) [T : topological_space α] := 
{γ   : Type u} -- TODO: should this be v?
(Ui  : γ → set α)
(OUi : ∀ i, T.is_open (Ui i))

def covers {α : Type u} [T : topological_space α] (OC : covering α) (U : set α) :=
(⋃ i : OC.γ, OC.Ui i) = U

def locality {α : Type u} [T : topological_space α] (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering α) (OCU : covers OC U) (s t : F OU), 
(∀ (i : OC.γ),
F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) s =
F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) t) → 
s = t

def gluing {α : Type u} [T : topological_space α] (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering α) (OCU : covers OC U),
∀ (s : Π (i : OC.γ), F (OC.OUi i)) (i j : OC.γ),
res_to_inter_left F (OC.OUi i) (OC.OUi j) (s i) = 
res_to_inter_right F (OC.OUi i) (OC.OUi j) (s j) → 
∃ (S : F OU), ∀ (i : OC.γ),
  F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) S = s i

-- Sanity checks.

def gluing_unique {α : Type u} [T : topological_space α] (F : presheaf_of_types α) :=
∀ {U} (OU : T.is_open U) (OC : covering α) (OCU : covers OC U),
∀ (s : Π (i : OC.γ), F (OC.OUi i)) (i j : OC.γ),
res_to_inter_left F (OC.OUi i) (OC.OUi j) (s i) = 
res_to_inter_right F (OC.OUi i) (OC.OUi j) (s j) → 
∃! (S : F OU), ∀ (i : OC.γ),
  F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) S = s i

lemma locality_gluing_unique {α : Type u} [T : topological_space α] (F : presheaf_of_types α) :
locality F ∧ gluing F → gluing_unique F :=
begin
  intros H,
  rcases H with ⟨HL, HG⟩,
  intros U OU OC OCU s i j Heq,
  have HS : ∃ (S : F OU), ∀ (i : OC.γ), F.res OU _ _ S = s i,
    from HG OU OC OCU s i j Heq,
  rcases HS with ⟨S, HS⟩,
  have HU : ∀ (S' : F OU), (∀ (i : OC.γ), F.res OU _ _ S' = s i) → S' = S,
    intros S' HS',
    apply HL OU OC OCU S' S,
    intros k,
    rw HS k,
    rw HS' k,
  existsi S, simp,
  apply and.intro HS HU,
end

-- def gluing {α : Type u} [T : topological_space α] 
--   (FP : presheaf_of_types α) 
--   (U : set α)
--   [UO : T.is_open U]
--   {γ : Type v} 
--   (Ui : γ → set α)
--   [UiO : ∀ i, T.is_open (Ui i)]
--   (Hcov : (⋃ x, Ui x) = U)
--   (r : FP.F UO) :
  
--   {a : (Π (x : γ), (FP.F (UiO x))) | ∀ (x y : γ), 
--     (res_to_inter_left FP (Ui x) (Ui y) (UiO x) (UiO y)) (a x) = 
--     (res_to_inter_right FP (Ui x) (Ui y) (UiO x) (UiO y)) (a y)} :=
--     ⟨λ x, begin   end, begin end⟩ 

-- ⟨λ x,(FP.res U (Ui x) UO (UiO x) (Hcov ▸ set.subset_Union Ui x) r),
--  λ x₁ y₁, have Hopen : T.is_open ((Ui x₁) ∩ (Ui y₁)),
--      from (T.is_open_inter _ _ (UiO x₁) (UiO y₁)),
--    show ((FP.res (Ui x₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ (FP.res U (Ui x₁) _ _ _)) r =
--         ((FP.res (Ui y₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ (FP.res U (Ui y₁) _ _ _)) r,
--    by rw [← presheaf_of_types.Hcomp, ← presheaf_of_types.Hcomp]⟩

-- def is_sheaf_of_types {α : Type*} [T : topological_space α]
--   (PT : presheaf_of_types α) : Prop :=
-- ∀ (U : set α) [OU : T.is_open U] {γ : Type*} (Ui : γ → set α)
--   [UiO : ∀ x : γ, T.is_open (Ui x)] (Hcov : (⋃ (x : γ), (Ui x)) = U),
-- function.bijective (@gluing _ _ PT U OU _ Ui UiO Hcov)

-- morphism of sheaves of sets is just a morphism of presheaves so no definition
-- needed. And category of sheaves of sets implies some facts about morphisms
-- but again they are all just proved in the presheaf case.
