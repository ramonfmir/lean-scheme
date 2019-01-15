import analysis.topology.topological_space
import tag006E -- presheaves 

section stalk

universe u 
parameters {X : Type u} [TX : topological_space X] (FPT : presheaf_of_types X) (x : X)

-- set Z is pairs (U,s) with U an open in X and x in U and s in FPT.F(U)
structure stalk.aux :=
(U : set X) (Hx : x ∈ U) (HU : TX.is_open U) (s : FPT.F HU)

-- equiv reln on Z : (U,s) tilde (V,t) iff there exists W open 
-- such that x in W, W in U, W in V, and FPT.res (U to W) s = FPT.res (V to W) t
instance stalk.setoid : setoid stalk.aux :=
{ r := λ Us Vt, ∃ W (H1 : is_open W) (H2 : x ∈ W) (H3 : W ⊆ Us.U) (H4 : W ⊆ Vt.U),
    FPT.res Us.U W Us.HU H1 H3 Us.s = FPT.res Vt.U W Vt.HU H1 H4 Vt.s,
  iseqv := ⟨λ ⟨U, HU1, HU2, s⟩, ⟨U, HU2, HU1, set.subset.refl _, set.subset.refl _, rfl⟩,
    λ Us Vt ⟨W, H1, H2, H3, H4, H5⟩, ⟨W, H1, H2, H4, H3, H5.symm⟩,
    λ ⟨U, HU1, HU2, s⟩ ⟨V, HV1, HV2, t⟩ ⟨W, HW1, HW2, u⟩ ⟨W1, H1, H2, H3, H4, H5⟩ ⟨W2, H6, H7, H8, H9, H0⟩,
    ⟨W1 ∩ W2, is_open_inter H1 H6, ⟨H2, H7⟩, λ z hz, H3 hz.1, λ z hz, H9 hz.2,
    have h1 : _ := FPT.Hcomp U W1 (W1 ∩ W2) HU2 H1 (is_open_inter H1 H6) H3 (set.inter_subset_left _ _),
    have h2 : _ := FPT.Hcomp V W1 (W1 ∩ W2) HV2 H1 (is_open_inter H1 H6) H4 (set.inter_subset_left _ _),
    have h3 : _ := FPT.Hcomp V W2 (W1 ∩ W2) HV2 H6 (is_open_inter H1 H6) H8 (set.inter_subset_right _ _),
    have h4 : _ := FPT.Hcomp W W2 (W1 ∩ W2) HW2 H6 (is_open_inter H1 H6) H9 (set.inter_subset_right _ _),
    calc FPT.res U (W1 ∩ W2) HU2 _ _ s
          = FPT.res W1 (W1 ∩ W2) H1 _ _ (FPT.res U W1 HU2 H1 H3 s) : congr_fun h1 s
      ... = FPT.res W1 (W1 ∩ W2) H1 _ _ (FPT.res V W1 HV2 H1 H4 t) : congr_arg _ H5
      ... = FPT.res V (W1 ∩ W2) HV2 _ _ t : (congr_fun h2 t).symm
      ... = FPT.res W2 (W1 ∩ W2) H6 _ _ (FPT.res V W2 HV2 H6 H8 t) : congr_fun h3 t
      ... = FPT.res W2 (W1 ∩ W2) H6 _ _ (FPT.res W W2 HW2 H6 H9 u) : congr_arg _ H0
      ... = FPT.res W (W1 ∩ W2) HW2 _ _ u : (congr_fun h4 u).symm⟩⟩ }

definition stalk := quotient stalk.setoid

end stalk