-- this tag is completed.

import analysis.topology.topological_space tag006E

def res_to_inter_left {α : Type*} [T : topological_space α] 
  (FT : presheaf_of_types α)
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V] :
  (FT.F OU) → (FT.F (T.is_open_inter U V OU OV)) :=
FT.res U (U ∩ V) OU (T.is_open_inter U V OU OV) (set.inter_subset_left U V)

def res_to_inter_right {α : Type*} [T : topological_space α]
  (FT : presheaf_of_types α)
  (U V : set α) [OU : T.is_open U] [OV : T.is_open V] :
  (FT.F OV) → (FT.F (T.is_open_inter U V OU OV)) :=
FT.res V (U ∩ V) OV (T.is_open_inter U V OU OV) (set.inter_subset_right U V)

def gluing {α : Type*} [T : topological_space α] (FP : presheaf_of_types α) 
  (U : set α)
  [UO : T.is_open U]
  {γ : Type*} (Ui : γ → set α)
  [UiO : ∀ i : γ, T.is_open (Ui i)]
  (Hcov : (⋃ (x : γ), (Ui x)) = U)
  (r : FP.F UO) :
  {a : (Π (x : γ), (FP.F (UiO x))) | ∀ (x y : γ), 
    (@res_to_inter_left _ _ FP (Ui x) (Ui y) (UiO x) (UiO y)) (a x) = 
    (@res_to_inter_right _ _ FP (Ui x) (Ui y) (UiO x) (UiO y)) (a y)} :=
⟨λ x,(FP.res U (Ui x) UO (UiO x) (Hcov ▸ set.subset_Union Ui x) r),
 λ x₁ y₁, have Hopen : T.is_open ((Ui x₁) ∩ (Ui y₁)),
     from (T.is_open_inter _ _ (UiO x₁) (UiO y₁)),
   show ((FP.res (Ui x₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ (FP.res U (Ui x₁) _ _ _)) r =
        ((FP.res (Ui y₁) ((Ui x₁) ∩ (Ui y₁)) _ Hopen _) ∘ (FP.res U (Ui y₁) _ _ _)) r,
   by rw [← presheaf_of_types.Hcomp, ← presheaf_of_types.Hcomp]⟩

def is_sheaf_of_types {α : Type*} [T : topological_space α]
  (PT : presheaf_of_types α) : Prop :=
∀ (U : set α) [OU : T.is_open U] {γ : Type*} (Ui : γ → set α)
  [UiO : ∀ x : γ, T.is_open (Ui x)] (Hcov : (⋃ (x : γ), (Ui x)) = U),
function.bijective (@gluing _ _ PT U OU _ Ui UiO Hcov)

-- morphism of sheaves of sets is just a morphism of presheaves so no definition
-- needed. And category of sheaves of sets implies some facts about morphisms
-- but again they are all just proved in the presheaf case.
