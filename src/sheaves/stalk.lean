import topology.basic
import sheaves.presheaf_of_types 

universe u 

variables {α : Type u} [T : topological_space α] 
variables (F : presheaf_of_types α) (x : α)

open topological_space

-- An element in the stalk is a pair (U, s) under an equivalence relation 

structure stalk.elem :=
(U   : set α) 
(OU  : T.is_open U) 
(HxU : x ∈ U) 
(s   : F OU)

-- Equivalence relation on the set of pairs. (U,s) ~ (V,t) iff there exists W 
-- open s.t. x ∈ W ⊆ U ∩ V, and s|W = t|W.

def stalk.relation : stalk.elem F x → stalk.elem F x → Prop :=
λ Us Vt,
    ∃ W (OW : T.is_open W) (HxW : x ∈ W) (HWU : W ⊆ Us.U) (HWV : W ⊆ Vt.U),
    F.res Us.OU OW HWU Us.s = F.res Vt.OU OW HWV Vt.s

lemma stalk.relation.reflexive : reflexive (stalk.relation F x) :=
λ ⟨U, OU, HxU, s⟩, ⟨U, OU, HxU, set.subset.refl _, set.subset.refl _, rfl⟩

lemma stalk.relation.symmetric : symmetric (stalk.relation F x) :=
λ Us Vt ⟨W, OW, HxW, HWU, HWV, Hres⟩, ⟨W, OW, HxW, HWV, HWU, Hres.symm⟩

lemma stalk.relation.transitive : transitive (stalk.relation F x) :=
sorry

--     λ ⟨U, HU1, HU2, s⟩ ⟨V, HV1, HV2, t⟩ ⟨W, HW1, HW2, u⟩ ⟨W1, H1, H2, H3, H4, H5⟩ ⟨W2, H6, H7, H8, H9, H0⟩,
--     ⟨W1 ∩ W2, is_open_inter H1 H6, ⟨H2, H7⟩, λ z hz, H3 hz.1, λ z hz, H9 hz.2,
--     have h1 : _ := FPT.Hcomp U W1 (W1 ∩ W2) HU2 H1 (is_open_inter H1 H6) H3 (set.inter_subset_left _ _),
--     have h2 : _ := FPT.Hcomp V W1 (W1 ∩ W2) HV2 H1 (is_open_inter H1 H6) H4 (set.inter_subset_left _ _),
--     have h3 : _ := FPT.Hcomp V W2 (W1 ∩ W2) HV2 H6 (is_open_inter H1 H6) H8 (set.inter_subset_right _ _),
--     have h4 : _ := FPT.Hcomp W W2 (W1 ∩ W2) HW2 H6 (is_open_inter H1 H6) H9 (set.inter_subset_right _ _),
--     calc FPT.res U (W1 ∩ W2) HU2 _ _ s
--           = FPT.res W1 (W1 ∩ W2) H1 _ _ (FPT.res U W1 HU2 H1 H3 s) : congr_fun h1 s
--       ... = FPT.res W1 (W1 ∩ W2) H1 _ _ (FPT.res V W1 HV2 H1 H4 t) : congr_arg _ H5
--       ... = FPT.res V (W1 ∩ W2) HV2 _ _ t : (congr_fun h2 t).symm
--       ... = FPT.res W2 (W1 ∩ W2) H6 _ _ (FPT.res V W2 HV2 H6 H8 t) : congr_fun h3 t
--       ... = FPT.res W2 (W1 ∩ W2) H6 _ _ (FPT.res W W2 HW2 H6 H9 u) : congr_arg _ H0
--       ... = FPT.res W (W1 ∩ W2) HW2 _ _ u : (congr_fun h4 u).symm⟩⟩ 

instance stalk.setoid : setoid (stalk.elem F x) :=
{ r := stalk.relation F x,
  iseqv := ⟨stalk.relation.reflexive F x, 
            stalk.relation.symmetric F x,
            stalk.relation.transitive F x⟩
      }

definition stalk := quotient (stalk.setoid F x)
