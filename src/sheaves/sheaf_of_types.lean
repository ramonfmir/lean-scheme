import preliminaries.covering
import sheaves.presheaf_of_types

universes u v

open topological_space
open lattice

namespace presheaf_of_types'

variables {α : Type u} [topological_space α]

-- Restriction map from U to U ∩ V.

def res_to_inter_left (F : presheaf_of_types α) (U V : opens α) 
: (F U) → (F (U ∩ V)) :=
F.res U (U ∩ V) (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right (F : presheaf_of_types α) (U V : opens α) 
: (F V) → (F (U ∩ V)) :=
F.res V (U ∩ V) (set.inter_subset_right U V)

-- Sheaf condition.

def locality (F : presheaf_of_types α) :=
∀ {U} (OC : covering U) (s t : F U), 
(∀ {Ui} (OUi : Ui ∈ OC.Uis),
F.res U Ui (subset_cover OUi) s =
F.res U Ui (subset_cover OUi) t) → 
s = t

-- def gluing' (F : presheaf_of_types α) :=
-- ∀ (U : opens α) (OC : covering U),
-- ∀ (s' : {s : (Π (i : OC.γ), F (OC.Ui i)) // ∀ (i j : OC.γ),
-- res_to_inter_left F (OC.Ui i) (OC.Ui j) (s i) = 
-- res_to_inter_right F (OC.Ui i) (OC.Ui j) (s j)}), 
-- ∃ (S : F U), ∀ (i : OC.γ),
--   F.res U (OC.Ui i) (OC.Hsub i) S = s'.val i

def gluing (F : presheaf_of_types α) :=
∀ {U} (OC : covering U),
∀ (s : Π (Ui) {H : Ui ∈ OC.Uis}, F Ui),
(∀ (Uj Uk ∈ OC.Uis),
res_to_inter_left F Uj Uk (s Uj) = 
res_to_inter_right F Uj Uk (s Uk)) → 
∀ (Ui ∈ OC.Uis), F.res U Ui (subset_cover U Ui) 

∀ (s' : {s : (Π (i : OC.γ), F (OC.Ui i)) // ∀ (i j : OC.γ),
res_to_inter_left F (OC.Ui i) (OC.Ui j) (s i) = 
res_to_inter_right F (OC.Ui i) (OC.Ui j) (s j)}), 
∃ (S : F U), ∀ (i : OC.γ),
  F.res U (OC.Ui i) (OC.Hsub i) S = s'.val i


-- Definition of a sheaf of types.

structure sheaf_of_types (α : Type u) [T : topological_space α] 
extends presheaf_of_types α :=
(locality : locality F)
(gluing   : gluing ↑F) 

end presheaf_of_types'

section sheaf_of_types

variables {α : Type u} [T : topological_space α]
include T

instance : has_coe (sheaf_of_types α) (presheaf_of_types α) := 
⟨λ S, S.F⟩

def is_sheaf_of_types (F : presheaf_of_types α) :=
presheaf_of_types.locality F ∧ presheaf_of_types.gluing F

-- Sanity checks.

-- def bijective_gluing (F : presheaf_of_types α) :=
-- ∀ {U} (OU : T.is_open U) (OC : presheaf_of_types.covering) 
-- (OCU : presheaf_of_types.covers OC U),
-- ∀ (s : Π (i : OC.γ), F (OC.OUi i)) (i j : OC.γ),
-- presheaf_of_types.res_to_inter_left F (OC.OUi i) (OC.OUi j) (s i) = 
-- presheaf_of_types.res_to_inter_right F (OC.OUi i) (OC.OUi j) (s j) → 
-- ∃! (S : F OU), ∀ (i : OC.γ),
--   F.res OU (OC.OUi i) (OCU ▸ set.subset_Union OC.Ui i) S = s i

-- lemma sheaf_condition_bijective_gluing (F : presheaf_of_types α) :
-- presheaf_of_types.locality F ∧ presheaf_of_types.gluing F → bijective_gluing F :=
-- begin
--   intros H,
--   rcases H with ⟨HL, HG⟩,
--   intros U OU OC OCU s i j Heq,
--   have HS : ∃ (S : F OU), ∀ (i : OC.γ), F.res OU _ _ S = s i,
--     apply HG OU OC OCU s i j Heq,
--   rcases HS with ⟨S, HS⟩,
--   have HU : ∀ (S' : F OU), (∀ (i : OC.γ), F.res OU _ _ S' = s i) → S' = S,
--     intros S' HS',
--     apply HL OU OC OCU S' S,
--     intros k,
--     rw HS k,
--     rw HS' k,
--   existsi S,
--   simp,
--   apply and.intro HS HU,
-- end

end sheaf_of_types
