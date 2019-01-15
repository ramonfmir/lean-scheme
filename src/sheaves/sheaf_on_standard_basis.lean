/- The lemma in this tag says that if we have a top space
and a basis with the property that the intersection of two
basis elements is in the basis, then to give a sheaf on B
is to give a "sheaf on a cofinal system of covers of B".
In the application to schemes, this means a presheaf with
the property that it satisfies the sheaf axiom for
finite covers of basic opens by basic opens, noting that
the intersection of two basis opens is a basic open.
-/

import tag009J 

universe u
-- A "standard" basis -- I just mean intersection of two basic opens is basic open.
-- Makes the sheaf axiom easier, and is satisfied in the case of Spec of a ring.
-- Below is the statement of the sheaf axiom for a given open cover in this case. 
definition sheaf_property_for_standard_basis 
  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ {U V : set X}, B U → B V → B (U ∩ V))
  (U : set X)
  (BU : B U)
  (γ : Type u)
  (Ui : γ → set X)
  (BUi : ∀ i : γ, B (Ui i))
  (Hcover: (⋃ (i : γ), (Ui i)) = U) : Prop := 
  ∀ si : Π (i : γ), FPTB.F (BUi i), 
  (∀ i j : γ, FPTB.res (BUi i) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_left _ _) (si i) = 
              FPTB.res (BUi j) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_right _ _) (si j))
  → ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) (Hcover ▸ (set.subset_Union Ui i)) s = si i 

definition basis_is_compact 
  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B) : Prop :=
  ∀ U : set X, B U →
    ∀ β : Type u, ∀ Ui : β → set X,
    (∀ i : β, B (Ui i)) → 
    (⋃ (i : β), Ui i) = U →
    ∃ γ : Type u, ∃ Hfinite : fintype γ,
    ∃ f : γ → β, 
    (⋃ (j : γ), Ui (f j)) = U 


definition sheaf_for_standard_cofinal_system  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ U V : set X, B U → B V → B (U ∩ V))
  -- cofinal system is finite covers
  (HBcompact: basis_is_compact HB)
  := 
  (∀ U : set X, ∀ BU : B U,
  ∀ γ : Type u, fintype γ → -- note fintype here
  ∀ Ui : γ → set X,
  ∀ BUi :  ∀ i : γ, B (Ui i),
  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,
  sheaf_property_for_standard_basis HB FPTB Hstandard U BU γ Ui BUi Hcover)

theorem lemma_cofinal_systems_coverings_standard_case 
  {X : Type u} [T : topological_space X] 
  {B : set (set X)} 
  (HB : topological_space.is_topological_basis B)
  (FPTB : presheaf_of_types_on_basis HB)
  (Hstandard : ∀ U V : set X, B U → B V → B (U ∩ V))
  -- cofinal system is finite covers
  (HBcompact: basis_is_compact HB)
  : sheaf_for_standard_cofinal_system HB FPTB Hstandard HBcompact → 
-- that line above is shorthand for:
--  (∀ U : set X, ∀ BU : B U,
--  ∀ γ : Type u, fintype γ → -- note fintype here
--  ∀ Ui : γ → set X,
--  ∀ BUi :  ∀ i : γ, B (Ui i),
--  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,
--  sheaf_property_for_standard_basis HB FPTB Hstandard U BU γ Ui BUi Hcover)
--  → 
  (∀ U : set X, ∀ BU : B U,
  ∀ γ : Type u, 
  ∀ Ui : γ → set X,
  ∀ BUi :  ∀ i : γ, B (Ui i),
  ∀ Hcover: (⋃ (i : γ), (Ui i)) = U,  
  sheaf_property_for_standard_basis HB FPTB Hstandard U BU γ Ui BUi Hcover)
  := 
begin
  intro Hfinite,
  intros U BU β Ui BUi Hcover,
  intros si Hsiglue,
  -- Hcover has a finite subcover
  cases HBcompact U BU β Ui BUi Hcover with γ Hγ,
  cases Hγ with HFinγ Hf,
  cases Hf with f Hfincover,
  have Huniques := Hfinite U BU γ HFinγ (Ui ∘ f) (λ j, BUi (f j)) Hfincover
    (λ i, si (f i)) (λ i j, Hsiglue (f i) (f j)),
  cases Huniques with s Hs,
  existsi s,
  split,
  { intro i,
    let Vj : γ → set X := λ j, Ui (f j) ∩ Ui i,
    have BVj : ∀ j : γ, B (Vj j) := 
      λ j, Hstandard (Ui (f j)) (Ui i) (BUi (f j)) (BUi i),
    have  HVcover : (⋃ (j : γ), Vj j) = Ui i,
    { apply set.ext,intro x,split,
      { intro HUn,
        cases HUn with Uk HUk,
        cases HUk with Ul HUl,
        cases Ul with j Hj,
        rw Hj at HUl,
        exact HUl.2
      },
      { intro Hx,
        have Hx2 : x ∈ U,
          rw ←Hcover,exact ⟨(Ui i),⟨i,rfl⟩,Hx⟩,
        rw ←Hfincover at Hx2,
        cases Hx2 with Vjj Hx3,
        cases Hx3 with Hx4 Vjjx,
        cases Hx4 with j Hj,
        existsi (Vj j),
        constructor,existsi j,refl,
        split,rw Hj at Vjjx,exact Vjjx,
        exact Hx
      }
    },
    --let x, show x = _,
    have HV := Hfinite (Ui i) (BUi i) γ HFinγ Vj BVj HVcover
      (λ j, FPTB.res BU (BVj j) 
      (set.subset.trans (set.inter_subset_right _ _) 
        (Hcover ▸ (set.subset_Union Ui i))) s) _,swap,
    { intros j1 j2,
      let Vj1 := Vj j1,
      let Vj2 := Vj j2,
      let Vj12 := Vj j1 ∩ Vj j2,
      have BVj1 := BVj j1,
      have BVj2 := BVj j2,
      have BVj12 := Hstandard _ _ BVj1 BVj2,
      show ((FPTB.res BVj1 BVj12 _) ∘ (FPTB.res BU BVj1 _)) s = 
           ((FPTB.res BVj2 BVj12 _) ∘ (FPTB.res BU BVj2 _)) s,
      rw ←(FPTB.Hcomp U Vj1 Vj12 BU BVj1 BVj12 _ _),
      rw ←(FPTB.Hcomp U Vj2 Vj12 BU BVj2 BVj12 _ _),
    },
    -- it's "exact HV" -- a fact about Ui i
    cases HV with s2 Hs2,
    refine @eq.trans _ _ s2 _ _ _,
    { -- goal is that restriction of s to Ui i is s2
      apply Hs2.2,
      intro j, -- goal is that res from U to Ui i to Vj j.
      show ((FPTB.res _ _ _) ∘ (FPTB.res BU _ _)) s 
        = FPTB.res BU _ _ s,
      rw ←(FPTB.Hcomp U (Ui i) (Vj j) BU _ _ _ _),
    },
    { -- goal is s2 = si i on Ui i
      apply eq.symm,
      apply Hs2.2,
      intro j, 
      -- goal is that si i restricted to Vj j equals s restricted to Vj j
      -- Hs.1 is the fact that 
      -- for all j, restriction of
      -- s to Ui (f j) is si (f j).
      -- now restrict to Vj j
      -- and deduce res of s to Vj j equals res of si (f j) to Vj j
      -- now Hsiglue says that on Vj j = Ui (f j) ∩ Ui i
      -- si (f j) and si i are equal.
      -- it says res si (f j) to Ui (f j) cap Ui i = res si i
      rw ←(Hsiglue), -- that was easy!
      -- goal now is that si (f j) = s on Ui (f j) cap Ui i
      have Htemp : si (f j) = _ := eq.symm (Hs.1 j),
      rw Htemp,
      show ((FPTB.res _ _ _) ∘ (FPTB.res BU _ _)) s = FPTB.res BU _ _ s,
      rw ←(FPTB.Hcomp U _ _ BU _ _ _ _),
    },
  },
  { intros s' Hs',
    apply Hs.2,
    intro i,
    exact Hs' (f i)
  }
end
