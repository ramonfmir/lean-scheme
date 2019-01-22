-- stuff mentioned in section "Bases and sheaves" (6.30; tag 009H)
-- but not in any definition etc

import sheaves.presheaf_of_types_on_basis
universe u 
-- definition after 6.30.1 and before 6.30.2

section presheaf_on_basis_stalk 

parameters {α : Type u} [TX : topological_space α] 
  {B : set (set α )}
  {HB : topological_space.is_topological_basis B}
  (FPTB : presheaf_of_types_on_basis α HB) (x : α)

structure presheaf_on_basis_stalk.aux :=
(U : set α)
(BU : U ∈ B)
(Hx : x ∈ U)
(s : FPTB.F BU)

instance presheaf_on_basis_stalk.setoid  :
   setoid (presheaf_on_basis_stalk.aux) := sorry
-- { r := λ Us Vt, ∃ (W : set X) (Hx : x ∈ W) (BW : W ∈ B) (HWU : W ⊆ Us.U) (HWV : W ⊆ Vt.U), 
--    FPTB.res Us.BU BW HWU Us.s = FPTB.res Vt.BU BW HWV Vt.s,
--   iseqv := ⟨
--     -- reflexive
--     λ Us,⟨Us.U,Us.Hx,Us.BU,set.subset.refl _,set.subset.refl _,rfl⟩,
--     -- symmetric
--     λ ⟨U,BU,Hx,s⟩ ⟨V,BV,HVx,t⟩ ⟨W,Hx,BW,HWU,HWV,H⟩,⟨W,Hx,BW,HWV,HWU,H.symm⟩,
--     -- transitive
--     λ ⟨U,BU,Hx,s⟩ ⟨V,BV,HVx,t⟩ ⟨W,BW,HWx,u⟩ ⟨W1,Hx1,BW1,HWU1,HWV1,H1⟩ ⟨W2,Hx2,BW2,HWU2,HWV2,H2⟩,
--     let ⟨W3,BW3,Hx3,H3⟩ := HB.1 W1 BW1 W2 BW2 x ⟨Hx1, Hx2⟩ in
--     have h1 : _ := FPTB.Hcomp U W1 W3 BU BW1 BW3 HWU1 (λ z hz, (H3 hz).1),
--     have h2 : _ := FPTB.Hcomp V W1 W3 BV BW1 BW3 HWV1 (λ z hz, (H3 hz).1),
--     have h3 : _ := FPTB.Hcomp V W2 W3 BV BW2 BW3 HWU2 (λ z hz, (H3 hz).2),
--     have h4 : _ := FPTB.Hcomp W W2 W3 BW BW2 BW3 HWV2 (λ z hz, (H3 hz).2),
--     ⟨W3,Hx3,BW3,λ z hz,HWU1 (H3 hz).1,λ z hz,HWV2 (H3 hz).2, calc
--             FPTB.res BU BW3 _ s
--           = FPTB.res BW1 BW3 _ (FPTB.res BU BW1 _ s) : congr_fun h1 s
--       ... = FPTB.res BW1 BW3 _ (FPTB.res BV BW1 _ t) : congr_arg _ H1
--       ... = FPTB.res BV BW3 _ t : (congr_fun h2 t).symm
--       ... = FPTB.res BW2 BW3 _ (FPTB.res BV BW2 _ t) : congr_fun h3 t
--       ... = FPTB.res BW2 BW3 _ (FPTB.res BW BW2 _ u) : congr_arg _ H2
--       ... = FPTB.res BW BW3 _ u : (congr_fun h4 u).symm⟩⟩
-- }

definition presheaf_on_basis_stalk :=
quotient (presheaf_on_basis_stalk.setoid)

-- 
-- set Z is pairs (U,s) with U in B and x in U and s in FPTB.F(U)
-- equiv reln on Z : (U,s) tilde (V,t) iff there exists W in B 
-- such that x in W, W in U, W in V, and FPT.res (U to W) s = FPT.res (V to W) t
-- note basis axiom HB.1:
-- (∀t₁∈s, ∀t₂∈s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃∈s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂)
-- Will need this for transitivity

end presheaf_on_basis_stalk
