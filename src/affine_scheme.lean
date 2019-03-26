-- /- Under defintion 25.5.2 (tag 01HT) and before 25.5.3 (01HU) there is an
-- argument which defines the sheaf of rings on Spec(R), and also the
-- quasicoherent sheaf
-- of O_X-modules attached to an R-module.
-- -/

-- /- Let's just do this for rings at this point.

-- -/
-- import group_theory.submonoid  
-- import ring_theory.localization 
-- --import localization_UMP
-- import Kenny_comm_alg.Zariski 
-- import tag00E0 
-- import tag00EJ
-- import tag01HS
-- import tag009I -- presheaf of types on a basis
-- import tag00DY -- claim that D(f) form a basis
-- import tag006N -- presheaves / sheaves of rings on a basis
-- import tag00E8 -- standard basis on Spec(R) is quasi-compact 
-- import tag009P -- presheaf of rings on a basis
-- import tag009L -- sheaf for finite covers on basis -> sheaf for basis
-- import tag009N -- sheaf for basis -> sheaf 
-- import data.equiv.basic
-- import canonical_isomorphism_nonsense

-- universe u
-- --set_option profiler true

-- open localization -- should have done this ages ago



-- -- just under Definition 25.5.2

-- -- Definition of presheaf-of-sets on basis
-- definition zariski.structure_presheaf_of_types_on_basis_of_standard (R : Type u) [comm_ring R]
-- : presheaf_of_types_on_basis (D_f_form_basis R) := 
-- { F := zariski.structure_presheaf_on_standard,
--   res := λ _ _ _ _ H,localization.localize_superset (nonzero_on_U_mono H),
--   Hid := λ _ _,eq.symm (localization.localize_superset.unique_algebra_hom _ _ (λ _,rfl)),
--   Hcomp := λ _ _ _ _ _ _ _ _,eq.symm (localization.localize_superset.unique_algebra_hom _ _ (
--     λ r, by simp [localization.localize_superset.is_algebra_hom]
--   ))
-- }

-- -- now let's make it a presheaf of rings on the basis
-- definition zariski.structure_presheaf_of_rings_on_basis_of_standard (R : Type u) [comm_ring R]
-- : presheaf_of_rings_on_basis (D_f_form_basis R) :=
-- { Fring := zariski.structure_presheaf_on_standard.comm_ring,
--   res_is_ring_morphism := λ _ _ _ _ _,localization.localize_superset.is_ring_hom _,
--   ..zariski.structure_presheaf_of_types_on_basis_of_standard R,
-- }

-- instance zariski.structure_presheaf_of_types_on_basis_of_standard_sections_is_ring 
--   (R : Type u) [comm_ring R] (U : set (X R)) (BU : U ∈ standard_basis R) :
-- comm_ring ((zariski.structure_presheaf_of_types_on_basis_of_standard R).F BU) := 
-- zariski.structure_presheaf_on_standard.comm_ring U BU 

-- -- computation of stalk: I already did this for R I think.

-- /-
-- -- warm-up: I never use this.
-- -- f invertible in R implies R[1/f] uniquely R-iso to R
-- noncomputable definition localization.loc_unit {R : Type u} [comm_ring R] (f : R) (H : is_unit f) : 
-- R_alg_equiv (id : R → R) (of_comm_ring R (powers f)) := 
-- R_alg_equiv.of_unique_homs 
--   (unique_R_alg_from_R (of_comm_ring R (powers f)))
--   (away_universal_property f id H)
--   (unique_R_alg_from_R id)
--   (id_unique_R_alg_from_loc _) 

-- -/

-- lemma tag01HR.unitf {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)) (of_comm_ring R (powers f) f)) :=
-- im_unit_of_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g))) $ unit_of_in_S $ away.in_powers f 

-- lemma tag01HR.unitg {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)) (of_comm_ring R (powers f) g)) :=
-- unit_of_in_S (away.in_powers (of_comm_ring R (powers f) g))

-- lemma prod_unit {R : Type u} [comm_ring R] {f g : R} : is_unit f → is_unit g → is_unit (f * g) := λ ⟨u,Hu⟩ ⟨v,Hv⟩, ⟨u*v,by rw [mul_comm u,mul_assoc f,←mul_assoc g,Hv,one_mul,Hu]⟩

-- lemma tag01HR.unitfg {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)) (of_comm_ring R (powers f) (f * g))) :=
-- begin 
--   have H := prod_unit (tag01HR.unitf f g) (tag01HR.unitg f g),
--   let φ := of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)),
--   have Hφ : is_ring_hom φ := by apply_instance,
--   rw ←Hφ.map_mul at H,
--   let ψ := of_comm_ring R (powers f),
--   have Hψ : is_ring_hom ψ := by apply_instance,
--   rw ←Hψ.map_mul at H,
--   exact H
-- end 

-- /-
-- set_option class.instance_max_depth 93
-- -- I don't use the next theorem, it was just a test for whether I had the right universal properties.
-- noncomputable definition loc_is_loc_loc {R : Type u} [comm_ring R] (f g : R) :
-- R_alg_equiv 
--   ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g)))
--   ∘ (of_comm_ring R (powers f)))
--   (of_comm_ring R (powers (f * g))) :=
-- R_alg_equiv.of_unique_homs
--   (away_away_universal_property' f g (of_comm_ring R (powers (f * g)))
--     (unit_of_loc_more_left f g) -- proof that f is aunit in R[1/fg]
--     (unit_of_loc_more_right f g) -- proof that g is a unit in R[1/fg]
--   )
--   (away_universal_property (f*g) 
--     ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g))) 
--       ∘ (of_comm_ring R (powers f)))
--     (tag01HR.unitfg f g) -- proof that fg is a unit in R[1/f][1/g]
--   )
--   (away_away_universal_property' f g ((of_comm_ring (loc R (powers f)) (powers (of_comm_ring R (powers f) g))) ∘ (of_comm_ring R (powers f)))
--     (tag01HR.unitf f g) -- proof that f is a unit in R[1/f][1/g]
--     (tag01HR.unitg f g) -- proof that g is a unit in R[1/f][1/g]
--   )
--   (id_unique_R_alg_from_loc _)
-- -/

-- -- cover of a standard open translates into a cover of Spec(localization)
-- theorem cover_of_cover_standard {R : Type u} [comm_ring R] {r : R}
-- {γ : Type u} (f : γ → R) (Hcover : (⋃ (i : γ), Spec.D' (f i)) = Spec.D' r)
-- : (⋃ (i : γ), Spec.D' (of_comm_ring R (powers r) (f i))) = set.univ :=
-- set.eq_univ_of_univ_subset (λ Pr HPr, 
-- begin
--   let φ := Zariski.induced (of_comm_ring R (powers r)),
--   let P := φ Pr,
--   have H : P ∈ Spec.D' r,
--     rw ←(lemma_standard_open R r).2,
--     existsi Pr,simp,
--   rw ←Hcover at H,
--   cases H with Vi HVi,
--   cases HVi with HVi HP,
--   cases HVi with i Hi,
--   existsi φ ⁻¹' Vi,
--   existsi _, -- sorry Mario
--     exact HP,
--   existsi i,
--   rw Hi,
--   exact Zariski.induced.preimage_D _ _,
-- end
-- )

-- local attribute [instance] classical.prop_decidable

-- /-
-- open finset 
-- open presheaf_of_types_on_basis 
-- theorem application_of_tag00EJ {R : Type u} [comm_ring R] (r : R) {γ : Type u} {H : fintype γ}
--   (f : γ → R) (Hcover : (1 : away r) ∈ span (↑(univ.image (of_comm_ring R (powers r) ∘ f)) : set (loc R (powers r)))) :
--   let FPTB := (zariski.structure_presheaf_of_types_on_basis_of_standard R) in 
  
  
--   (si : Π (i : γ), (zariski.structure_presheaf_of_types_on_basis_of_standard R).F ⟨f i,rfl⟩)
--   (Hglue : ∀ i j : γ, res ⟨f i, rfl⟩ (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_left _ _) (si i) = 
--               FPTB.res (BUi j) (Hstandard (BUi i) (BUi j) : B (Ui i ∩ Ui j)) (set.inter_subset_right _ _) (si j))
--   → ∃! s : FPTB.F BU, ∀ i : γ, FPTB.res BU (BUi i) (Hcover ▸ (set.subset_Union Ui i)) s = si i 


-- -/

-- -- Now let's try and prove the sheaf axiom for finite covers.

-- instance alpha_is_add_group_hom {R : Type u} {γ : Type u} [comm_ring R] [fintype γ] (f : γ → R) :
-- is_add_group_hom (tag00EJ.α f) :=
-- begin
--   constructor,
--   intros a b,
--   funext,
--   unfold tag00EJ.α,
--   have H := localization.is_ring_hom R (powers (f i)),
--   apply H.map_add,
-- end 

-- instance beta_is_add_group_hom {R : Type u} {γ : Type u} [comm_ring R] [fintype γ] (f : γ → R) :
-- is_add_group_hom (@tag00EJ.β R γ _ _ f) := begin
-- --unfold is_add_group_hom,
-- constructor,
-- intros a b,
-- funext,
-- show _ = (tag00EJ.β a j k) + (tag00EJ.β b j k),
-- unfold tag00EJ.β,
-- have H1 : localize_more_left (f j) (f k) ((a + b) j) = localize_more_left (f j) (f k) (a j)
-- + localize_more_left (f j) (f k) (b j) := is_add_group_hom.add (localize_more_left (f j) (f k)) (a j) (b j),
-- rw H1,
-- have H2 : localize_more_right (f j) (f k) ((a + b) k) = localize_more_right (f j) (f k) (a k)
-- + localize_more_right (f j) (f k) (b k) := is_add_group_hom.add _ (a k) (b k),
-- rw H2,
-- simp,
-- end 

-- -- first let's check the sheaf axiom for finite covers, using the fact that 
-- -- the intersection of two basis opens is a basic open (meaning we can use
-- -- tag 009L instead of 009K).

-- lemma zariski.standard_basis_has_FIP (R : Type u) [comm_ring R] : ∀ (U V : set (X R)),
--   U ∈ (standard_basis R) → V ∈ (standard_basis R) → U ∩ V ∈ (standard_basis R) :=
-- λ U V ⟨f,Hf⟩ ⟨g,Hg⟩,⟨f*g,Hf.symm ▸ Hg.symm ▸ (tag00E0.lemma15 _ f g).symm⟩

-- -- this should follow from 
-- -- a) Chris' lemma [lemma_standard_covering₁ and ₂].
-- -- b) the fact (proved by Kenny) that localization of R at mult set of functions non-vanishing
-- --    on D(f) is isomorphic (as ring, but we will only need as ab group) to R[1/f]
-- -- c) the fact (which is probably done somewhere but I'm not sure where) that
-- --    D(f) is homeomorphic to Spec(R[1/f]) and this homeo identifies D(g) in D(f) with D(g)
-- --    in Spec(R[1/f])
-- -- 
-- -- What makes is so hard is checking that all the diagrams commute.
-- set_option class.instance_max_depth 72
-- theorem zariski.sheaf_of_types_on_standard_basis_for_finite_covers (R : Type u) [comm_ring R] :
--   ∀ (U : set (X R)) (BU : U ∈ (standard_basis R)) (γ : Type u) (Fγ : fintype γ)
--   (Ui : γ → set (X R)) (BUi :  ∀ i : γ, (Ui i) ∈ (standard_basis R))
--   (Hcover: (⋃ (i : γ), (Ui i)) = U),
--   sheaf_property_for_standard_basis (D_f_form_basis R) (zariski.structure_presheaf_of_types_on_basis_of_standard R)
--     (zariski.standard_basis_has_FIP R)
--     U BU γ Ui BUi Hcover :=
-- begin
--   intros U BU γ Hfγ Ui BUi Hcover si Hglue,
--   -- from all this data our job is to find a global section
--   cases BU with r Hr,
--   let Rr := away r, -- our job is to find an element of Rr
--   -- will get this from lemma_standard_covering₂
--   let f0 : γ → R := λ i, (classical.some (BUi i)),
--   let f : γ → Rr := λ i, of_comm_ring R (powers r) (classical.some (BUi i)),
--   let f_proof := λ i, (classical.some_spec (BUi i) : Ui i = Spec.D' (f0 i)),
--   -- need to check 1 ∈ span ↑(finset.image f finset.univ)
--   -- to apply the algebra lemma for coverings.

--   -- first let's check the geometric assertion
--   have Hcoverr : (⋃ (i : γ), Spec.D' (f i)) = set.univ,
--   { refine cover_of_cover_standard _ _,
--     rw ←Hr,
--     rw ←Hcover,
--     congr,
--     apply funext,
--     intro i,
--     rw ←(f_proof i) },

--   -- now let's deduce that the ideal of Rr gen by im f is all of Rr
--   let F : set Rr := set.range f,
--   have H2 : ⋃₀ (Spec.D' '' (set.range f)) = set.univ,
--     rw [←Hcoverr,←set.image_univ,←set.image_comp],
--     simp [set.Union_eq_sUnion_range],
--   rw [tag00E0.lemma16] at H2,
--   have H3 : Spec.V (set.range f) = ∅,
--     rw [←set.compl_univ,←H2,set.compl_compl],
--   rw ←tag00E0.lemma05 at H3,
--   have H1 : is_submodule (span (set.range f)) := by apply_instance,
--   have H1' : is_ideal (span (set.range f)) := {..H1},
--   letI := H1',
--   have H4 : span (set.range f) = set.univ := (tag00E0.lemma08 Rr _).1 H3,
--   clear F H2 H3 H1,
--   have H5 : set.range f = ↑(finset.image f finset.univ),
--     apply set.ext,intro x,split;intro H2,
--     cases H2 with i Hi,rw ←Hi,simp,existsi i,refl,
--     have : ∃ (a : γ), f a = x := by simpa using H2, exact this,
--   rw H5 at H4,
--   have H2 : (1 : Rr) ∈ span ↑(finset.image f finset.univ),
--     rw H4,trivial,
--   clear H5 H4,

--   -- H2 is one of the inputs to Chris' lemma.

--   -- What we seem to need now is a proof that if V is a standard open and V ⊆ U,
--   -- then R[1/S(V)] = R[1/r][1/f] for V = D(f), and the unique R-algebra hom is an isom.

--   -- so let's prove this.


-- -- s_proof no longer needed: we have canonical_iso.

--   -- next thing we need is (s : Π (i : γ), loc Rr (powers (f i))) .
--   -- But before we do that, let's define a function which sends i to a proof
--   -- that if Ui = D(f i) and fi = image of f i in R[1/r] then O_X(Ui) = R[1/r][1/fi]
--   -- Note that this is data -- the "=" is a given isomorphism between two totally different types
--   /-
--   let s_proof := λ i, begin
--     let sival := (zariski.structure_presheaf_of_types_on_basis_of_standard R).F (BUi i),
--     let fi := classical.some (BUi i),
--     have Hfi_proof : Ui i = Spec.D' (fi) := classical.some_spec (BUi i),
--     -- α = R[1/r][1/fi] -- ring Chris proved something about 
--     -- β = R[1/fi] -- intermediate object
--     -- γ = R[1/S(U)] -- definition of sheaf
--     let sα : R → loc (away r) (powers (of_comm_ring R (powers r) fi)) :=
--       of_comm_ring (away r) (powers (of_comm_ring R (powers r) fi)) ∘ of_comm_ring R (powers r),
--     let sβ : R → loc R (powers fi) := of_comm_ring R (powers fi),  
--     let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' fi))),
--     let Hi : R_alg_equiv sγ sβ := zariski.structure_presheaf_on_standard_is_loc fi,
--     -- rw ←Hfi_proof at Hi -- fails,
--     -- exact Hi.to_fun (si i), -- this is *supposed* to fail -- I need R[1/f][1/g] = R[1/g] here
--     -- loc R (powers fi) = loc Rr (powers (f i))
--     -- recall Rr is R[1/r] and U = D(r). We have D(fi) in U so "fi = g and r = f"
--     -- so D(fi) is a subset of D(U)
--     have Hsub : Spec.D' fi ⊆ Spec.D' r,
--       rw [←Hfi_proof,←Hr,←Hcover],
--       exact set.subset_Union Ui i,
--     let Hloc : R_alg_equiv sα sβ := localization.loc_loc_is_loc Hsub, 
--     -- now use symmetry and transitivity to deduce sα = sγ 
--     let Hαγ : R_alg_equiv sγ sα := R_alg_equiv.trans Hi (R_alg_equiv.symm Hloc),
--     exact Hαγ,
--   end,
-- -/

--   -- now in a position to apply lemma_standard_covering₂
--   have Hexact1 := lemma_standard_covering₁ H2,
--   have Hexact2 := lemma_standard_covering₂ f H2,
  
--   -- At this point we have Hexact1 and Hexact2, which together are the assertion that
--   -- if Rr = R[1/r] (with U=D(r)) and f : gamma -> Rr gives us a cover of U by U_i=D(f i)
--   -- then the comm algebra sequence 00EJ is exact.

--   -- We want to deduce an analogous statement for the global sections of O_X
--   -- defined as O_X(U) = R[1/S(U)] and O_X(U_i) = R[1/S(U_i)].
--   -- We have s_proof i : R_alg_equiv (R->R[1/S(U_i)]) (R->R[1/r]->R[1/r][1/f_i])
--   -- We will surely need R_alg_equiv (R->R[1/S(U)]) (R->R[1/r]) but we will have
--   -- this somewhere : it will be zariski.structure_presheaf_on_standard_is_loc blah
--   have HUbasic := zariski.structure_presheaf_on_standard_is_loc r,

--   -- goal currently
--   --∃! (s : (zariski.structure_presheaf_of_types_on_basis_of_standard R).F _),
--   --  ∀ (i : γ), (zariski.structure_presheaf_of_types_on_basis_of_standard R).res _ _ _ s = si i

--   -- This is the point where I want to say "done because everything is canonical".
--   -- 
--   -- A = Rr
--   -- B = prod_i Rr[1/f i]
--   -- C = prod_{j,k} Rr[1/(f j) * (f k)] 
--   -- A' = value of sheaf on U
--   -- B' = prod_i values on D(f0 i)
--   -- C' = prod j k values in D((f0 j) * (f0 k))

--   have H4exact : ∀ (b : Π (i : γ), loc Rr (powers (f i))), tag00EJ.β b = 0 → (∃! (a : Rr), tag00EJ.α f a = b),
--   { intros b Hb,
--     cases ((Hexact2 b).1 Hb) with a Ha,
--     existsi a,
--     split,exact Ha,
--     intros y Hy,
--     apply Hexact1,
--     rw Ha,
--     rw Hy
--   }, 

--   let fa : R_alg_equiv 
--               (of_comm_ring R (powers r)) 
--               (of_comm_ring R (non_zero_on_U U)) := begin 
--                 rw Hr,
--                 exact (zariski.structure_presheaf_on_standard_is_loc r).symm,
--               end, 

-- --  have : is_add_group_hom fa.to_equiv := sorry, --fa.to_is_ring_hom.map_add,

--   let fbi : ∀ i : γ, R_alg_equiv
--                ((of_comm_ring Rr (powers (f i))) ∘ (of_comm_ring R (powers r)))
--                (of_comm_ring R (non_zero_on_U (Ui i))) := begin
--                  intro i,
--                  rw f_proof i,
--                  have H : Spec.D' (f0 i) ⊆ Spec.D' r,
--                  { rw ←Hr,
--                    rw ←(f_proof i),
--                    rw ←Hcover,
--                    apply set.subset_Union Ui i,
--                  },
--       exact (canonical_iso H).symm,

--   end,

--   let fcjk : ∀ j k : γ, R_alg_equiv 
--                 ((of_comm_ring Rr (powers (f j * f k))) ∘ (of_comm_ring R (powers r)))
--                 (of_comm_ring R (non_zero_on_U (Ui j ∩ Ui k))) := begin
--                   intros j k,
--                   rw f_proof j,
--                   rw f_proof k,
--                   rw ←tag00E0.lemma15,
--                   have H : f j * f k = of_comm_ring R (powers r) (f0 j * f0 k),
--                     rw (localization.is_ring_hom R (powers r)).map_mul,
--                   rw H,
--                   have H' : Spec.D' (f0 j * f0 k) ⊆ Spec.D' r,
--                   { rw tag00E0.lemma15,
--                     apply set.subset.trans 
--                       (set.inter_subset_left (Spec.D' (f0 j)) (Spec.D' (f0 k))) (_ :
--                       (Spec.D' (f0 j)) ⊆ Spec.D' r),
--                     rw ←Hr,
--                     rw ←(f_proof j),
--                     rw ←Hcover,
--                     apply set.subset_Union Ui j,
--                   },
--                   -- now rewrite Uj ∩ Uk as D(f0j * f0k)
--                   -- and there might be an issue that f j * f k isn't
--                   -- defeq to the image of f0 j * f0 k
--                   -- Once these are fixed the below might work.
--                   exact (canonical_iso H').symm,
--                 end,

--   let H3 : ∀ (i : γ), loc Rr (powers (f i)) ≃ loc R (non_zero_on_U (Ui i)),
--     intro i,exact (fbi i).to_equiv,
--   let H3' : (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i)) := equiv.Pi_congr_right H3,

--   let H4 : ∀ (j k : γ), loc Rr (powers (f j * f k)) ≃ loc R (non_zero_on_U (Ui j ∩ Ui k)),
--     intros j k, exact (fcjk j k).to_equiv,

--   let H4' : ∀ j, (Π k, loc Rr (powers (f j * f k))) ≃ (Π k, loc R (non_zero_on_U (Ui j ∩ Ui k))),
--     intro j, exact equiv.Pi_congr_right (H4 j),
  
--   let H4'' : (Π (j k : γ), loc Rr (powers (f j * f k))) ≃ Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k)),
--     exact equiv.Pi_congr_right H4',
  
--   have Hcover' : ∀ (i : γ), Ui i ⊆ U := λ i, Hcover ▸ set.subset_Union Ui i,

--   let ab' : loc R (non_zero_on_U U) → Π (i : γ), loc R (non_zero_on_U (Ui i)) := λ Fi i,
--     localization.localize_superset (nonzero_on_U_mono (Hcover' i)) Fi,
  
--   let bc'₁ : (Π (i : γ), loc R (non_zero_on_U (Ui i))) → Π (j k : γ), loc R (non_zero_on_U (Ui j ∩ Ui k)) :=
--     λ Fi j k, localization.localize_superset (nonzero_on_U_mono $ set.inter_subset_left _ _) (Fi j),

--   let bc'₂ : (Π (i : γ), loc R (non_zero_on_U (Ui i))) → Π (j k : γ), loc R (non_zero_on_U (Ui j ∩ Ui k)) :=
--     λ Fi j k, localization.localize_superset (nonzero_on_U_mono $ set.inter_subset_right _ _) (Fi k),

--   let bc' := λ x, bc'₁ x - bc'₂ x,

--   have Hbc'_add_group_hom : is_add_group_hom bc' := ⟨_⟩,


--   have Hcanonical := fourexact_from_iso_to_fourexact 
--    (tag00EJ.α f : Rr → (Π (i : γ), away (f i)))
--    (tag00EJ.β) 
--    (H4exact) --H4exact
--    (fa.to_equiv) -- fa
-- --   (equiv.prod H3 : (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i))) -- fb
-- --   (H3' : (Π (i : γ), loc Rr (powers (f i))) ≃ Π (i : γ), loc R (non_zero_on_U (Ui i))) -- fb
-- --   H3'
-- --   (H3' : ((Π (i : γ), loc Rr (powers (f i))) ≃ (Π (i : γ), loc R (non_zero_on_U (Ui i))))) -- fb
-- --   (by exact H3')
--    (H3' : ((Π (i : γ), loc Rr (powers (f i))) ≃ (Π (i : γ), loc R (non_zero_on_U (Ui i))))) -- fb
--    (H4'' : (Π (j k : γ), loc Rr (powers (f j * f k))) ≃ Π (j k : γ),loc R (non_zero_on_U (Ui j ∩ Ui k))) -- fa : A ≃ A', fb fc
--     ab' -- ab' -- map
--     bc' -- bc' -- map 
--     _ _, -- H1 H2 -- diags commute

--   -- modulo the six extra goals which just appeared, we're nearly done!
--   show ∀ (a : Rr), (H3' ∘ (tag00EJ.α f)) a = ab' (((fa.to_ring_equiv).to_equiv) a),
--   -- map from Rr to B' = Π (i : γ), loc R (non_zero_on_U (Ui i))
--   suffices : H3' ∘ (tag00EJ.α f) = ab' ∘ fa.to_ring_equiv.to_equiv,
--     intro a,
--     rw this,
--   let F1 := H3' ∘ (tag00EJ.α f),
--   let F2 := ab' ∘ fa.to_ring_equiv.to_equiv,
--   -- the goal is to prove F1 = F2.
--   -- Let's first prove that they agree on R.
--   have HRalg : ∀ s : R, F1 (of_comm_ring R (powers r) s) = F2 (of_comm_ring R (powers r) s),
--     intro s,
--     funext i,
--     -- F1 (of_comm_ring R (powers r) s) i = F2 (of_comm_ring R (powers r) s) i
--     show (fbi i) (of_comm_ring Rr (powers (f i)) (of_comm_ring R (powers r) s)) =
--          localize_superset (nonzero_on_U_mono (Hcover' i)) (( fa.to_ring_equiv.to_equiv.to_fun ∘ (of_comm_ring R (powers r))) s),
--     show ((fbi i) ∘ (of_comm_ring Rr (powers (f i)))) (of_comm_ring R (powers r) s) = _,
--     show ((fbi i).to_ring_equiv.to_equiv.to_fun ∘ (of_comm_ring Rr (powers (f i))) ∘ (of_comm_ring R (powers r))) s = _,
--     rw ←fa.R_alg_hom,
--     rw ←(fbi i).R_alg_hom,
--     refine (localize_superset.is_algebra_hom _ s).symm,
--   -- Now some general nonsense says they agree.
--   have HH0 : is_ring_hom F1 := _,
--   refine (unique_R_alg_from_loc F2).is_unique F1 _,
--   funext s,
--   exact (HRalg s).symm,

--   have HRH1 : is_ring_hom (tag00EJ.α f) := {
--     map_add := λ a b,begin
--       funext j,
--       show of_comm_ring Rr _ (a + b) = of_comm_ring Rr _ a + of_comm_ring Rr _ b,
--       rw (localization.is_ring_hom Rr (powers (f j))).map_add,
--     end,
--     map_mul := λ a b, begin
--       funext j,
--       show of_comm_ring Rr _ (a * b) = of_comm_ring Rr _ a * of_comm_ring Rr _ b,
--       rw (localization.is_ring_hom Rr (powers (f j))).map_mul,
--     end,
--     map_one := begin 
--       funext j,
--       show of_comm_ring Rr _ 1 = 1,
--       rw (localization.is_ring_hom Rr (powers (f j))).map_one
--     end
--   },
    
--   have HRH2 : is_ring_hom H3',
--     apply_instance,

--   show is_ring_hom F1,
--     apply_instance,
  
--   show ∀ (a b : (Π (i : γ), loc R (non_zero_on_U (Ui i)))), bc' (a + b) = bc' a + bc' b,
--     have HAG1 : is_add_group_hom bc'₁,
--       constructor,
--       show ∀ (a b : Π (i : γ), loc R (non_zero_on_U (Ui i))), bc'₁ (a + b) = bc'₁ a + bc'₁ b,
--       intros a b,
--       funext j k,
--       show bc'₁ (a + b) j k = (bc'₁ a + bc'₁ b) j k,
--       show localize_superset _ (a j + b j) = localize_superset _ (a j) + localize_superset _ (b j),
--       rw (localize_superset.is_ring_hom _).map_add,

--     have HAG2 : is_add_group_hom bc'₂,
--       constructor,
--       show ∀ (a b : Π (i : γ), loc R (non_zero_on_U (Ui i))), bc'₂ (a + b) = bc'₂ a + bc'₂ b,
--       intros a b,
--       funext j k,
--       show bc'₂ (a + b) j k = (bc'₂ a + bc'₂ b) j k,
--       show localize_superset _ (a k + b k) = localize_superset _ (a k) + localize_superset _ (b k),
--       rw (localize_superset.is_ring_hom _).map_add,

--     intros a b,
--     show bc' (a + b) = (bc' a + bc' b),  
--     show bc'₁ (a + b) - bc'₂ (a + b) = (bc'₁ a - bc'₂ a) + (bc'₁ b - bc'₂ b),  
--     rw [is_add_group_hom.add bc'₁,is_add_group_hom.add bc'₂],
--     simp,
  
--   -- two goals left: one square commutes, and then the application.

--   show ∀ (b : Π (i : γ), loc Rr (powers (f i))), H4'' (tag00EJ.β b) = bc' (H3' b),
--     -- remember H3' is known to be a ring hom.
--     -- and bc' is an additive group hom
--     -- oh crap, I need that bc'₁ and 2 are ring homs!
--     -- and that beta is a difference of two ring homs.

--     -- I had better deduce the result from β₁ and β₂ commuting with bc'₁ and bc'₂.

--   have Hb1 : ∀ (b : Π (i : γ), loc Rr (powers (f i))), H4'' (tag00EJ.β₁ b) = bc'₁ (H3' b),
--   -- will also need
--   --have Hb2 : ∀ (b : Π (i : γ), loc Rr (powers (f i))), H4'' (tag00EJ.β₂ b) = bc'₂ (H3' b),
--   -- let's try and focus on one component.
--     intro Fi,
--     funext j k,
--     show H4'' (tag00EJ.β₁ Fi) j k = bc'₁ (H3' Fi) j k,
--     -- Fi : Π (i : γ), loc Rr (powers (f i)),
--     -- and equality is between elements of 
--     -- loc R (non_zero_on_U (Ui j ∩ Ui k))
--     -- show H4'' = (fcjk j k) : Rr (powers (f j * f k)) -> R (non_zero_on_U (Ui j ∩ Ui k)))
--     -- β₁ : localize_more_left (f j) (f k)
--     -- now let's figure out what we actually have to prove.
--     -- H3' = (fbi i) : Rr[1/f i] -> R[1/non-zero_on_U (Ui i)]
--     -- bc'₁ localize_superset _ (Fi j) from 1/Ui i -> 1/(Ui j ∩ Ui k)
--     show (fcjk j k) (localize_more_left (f j) (f k) (Fi j)) = _,
--     show _ = localize_superset _ ((fbi j) (Fi j)),
--     let F1₁ := (fcjk j k) ∘ (localize_more_left (f j) (f k)),
--     let F2₁ := (localize_superset (nonzero_on_U_mono (set.inter_subset_left (Ui j) (Ui k)))) ∘ (fbi j),
--     have : is_ring_hom (fbi j) := by apply_instance,
--     have : is_ring_hom (localize_superset (nonzero_on_U_mono (set.inter_subset_left (Ui j) (Ui k)))) := by apply_instance,
--     have : is_ring_hom (F2₁) := by apply_instance,
--     have : is_ring_hom (of_comm_ring Rr (powers (f j))) := by apply_instance,
--     show F1₁ (Fi j) = F2₁ (Fi j),
--     suffices : F1₁ = F2₁,
--       rw this,
--     -- these are both ring homs from loc Rr (powers (f j)) to R[1/S(Ui j ∩ Ui k)]
--     -- the strategy is to prove that they're both R-alg homs and then that there's only one.

--     --    let F2₁ := bc'₁ ∘ H3',
--     --    suffices : F1₁ = F2₁,
--     --      show ∀ (b : Π (i : γ), loc Rr (powers (f i))), F1₁ b = F2₁ b,
--     --      rw this,
--     --      intro b,refl,
--     -- as before, the strat is to show they're R-alg homs 
--     -- proof should look like : 
--     --    rw ←fa.R_alg_hom,
--     --    rw ←(fbi i).R_alg_hom,
--     --    refine (localize_superset.is_algebra_hom _ s).symm,    
--     have HRalg₁ : F1₁ ∘ (of_comm_ring Rr (powers (f j))) ∘ (of_comm_ring R (powers r))
--                         =  F2₁ ∘ (of_comm_ring Rr (powers (f j))) ∘ (of_comm_ring R (powers r)),
--       show (fcjk j k).to_ring_equiv.to_equiv.to_fun ∘ (localize_more_left (f j) (f k)) ∘ (of_comm_ring Rr (powers (f j))) ∘ (of_comm_ring R (powers r))
--         =  (localize_superset (nonzero_on_U_mono (set.inter_subset_left (Ui j) (Ui k)))) ∘ (fbi j).to_ring_equiv.to_equiv.to_fun ∘ (of_comm_ring Rr (powers (f j))) ∘ (of_comm_ring R (powers r)),
--       rw ←(fbi j).R_alg_hom,
--       -- rw ←(fcjk j k).R_alg_hom, -- (((fcjk j k).to_ring_equiv).to_equiv).to_fun ∘ of_comm_ring Rr (powers (f j * f k)) ∘ of_comm_ring R (powers r)
--       rw ←(superset_universal_property _ _ _).R_alg_hom,
--       -- what I now need is to replace
--       -- localize_more_left (f j) (f k) ∘ of_comm_ring Rr (powers (f j))
--       -- with 
--       -- of_comm_ring Rr (powers (f j * f k)) 
--       -- rw ←(loc_more_left_universal_property (f j) (f k)).R_alg_hom, -- something like this should work.
--       unfold localize_more_left,
--       show (((fcjk j k).to_ring_equiv).to_equiv).to_fun ∘
--         (away.extend_map_of_im_unit (of_comm_ring Rr (powers (f j * f k))) _ ∘
--         of_comm_ring Rr (powers (f j))) ∘ of_comm_ring R (powers r) =
--         of_comm_ring R (non_zero_on_U (Ui j ∩ Ui k)),
--         rw ←(away_universal_property (f j) (of_comm_ring Rr (powers (f j * f k))) _).R_alg_hom,
--       rw ←(fcjk j k).R_alg_hom,
--       -- done :-)
--     have HRralg₁ : F1₁ ∘ of_comm_ring Rr (powers (f j)) = F2₁ ∘ of_comm_ring Rr (powers (f j)),
--       let Htemp := unique_R_alg_from_loc (F2₁ ∘ of_comm_ring Rr (powers (f j))),
--       rw (Htemp.is_unique (F1₁ ∘ of_comm_ring Rr (powers (f j)))),
--       exact HRalg₁.symm,
--     let Htemp' := unique_R_alg_from_loc (F1₁),
--     rwa Htemp'.is_unique (F2₁),

--       -- now do it again!

--     have Hb2 : ∀ (b : Π (i : γ), loc Rr (powers (f i))), H4'' (tag00EJ.β₂ b) = bc'₂ (H3' b),
--     -- let's try and focus on one component.
--     intro Fi,
--     funext j k,
--     show H4'' (tag00EJ.β₂ Fi) j k = bc'₂ (H3' Fi) j k,
--     -- Fi : Π (i : γ), loc Rr (powers (f i)),
--     -- and equality is between elements of 
--     -- loc R (non_zero_on_U (Ui j ∩ Ui k))
--     -- show H4'' = (fcjk j k) : Rr (powers (f j * f k)) -> R (non_zero_on_U (Ui j ∩ Ui k)))
--     -- β₁ : localize_more_left (f j) (f k)
--     -- now let's figure out what we actually have to prove.
--     -- H3' = (fbi i) : Rr[1/f i] -> R[1/non-zero_on_U (Ui i)]
--     -- bc'₁ localize_superset _ (Fi j) from 1/Ui i -> 1/(Ui j ∩ Ui k)
--     show (fcjk j k) (localize_more_right (f j) (f k) (Fi k)) = _,
--     show _ = localize_superset _ ((fbi k) (Fi k)),
--     let F1₂ := (fcjk j k) ∘ (localize_more_right (f j) (f k)),
--     let F2₂ := (localize_superset (nonzero_on_U_mono (set.inter_subset_right (Ui j) (Ui k)))) ∘ (fbi k),     have : is_ring_hom (fbi j) := by apply_instance,
--     have : is_ring_hom (localize_superset (nonzero_on_U_mono (set.inter_subset_right (Ui j) (Ui k)))) := by apply_instance,
--     have : is_ring_hom (F2₂) := by apply_instance,
--     have : is_ring_hom (of_comm_ring Rr (powers (f k))) := by apply_instance,
--     have : is_ring_hom (F2₂ ∘ of_comm_ring Rr (powers (f k))) := by apply_instance,
--     show F1₂ (Fi k) = F2₂ (Fi k),
--     suffices : F1₂ = F2₂,
--       rw this,
--     -- the strategy is to prove that they're both R-alg homs and then that there's only one.

--     have HRalg₂ : F1₂ ∘ (of_comm_ring Rr (powers (f k))) ∘ (of_comm_ring R (powers r))
--                         =  F2₂ ∘ (of_comm_ring Rr (powers (f k))) ∘ (of_comm_ring R (powers r)),
--       show (fcjk j k).to_ring_equiv.to_equiv.to_fun ∘ (localize_more_right (f j) (f k)) ∘ (of_comm_ring Rr (powers (f k))) ∘ (of_comm_ring R (powers r))
--         =  (localize_superset (nonzero_on_U_mono (set.inter_subset_right (Ui j) (Ui k)))) ∘ (fbi k).to_ring_equiv.to_equiv.to_fun ∘ (of_comm_ring Rr (powers (f k))) ∘ (of_comm_ring R (powers r)),
--       rw ←(fbi k).R_alg_hom,
--       -- rw ←(fcjk j k).R_alg_hom, -- (((fcjk j k).to_ring_equiv).to_equiv).to_fun ∘ of_comm_ring Rr (powers (f j * f k)) ∘ of_comm_ring R (powers r)
--       rw ←(superset_universal_property _ _ _).R_alg_hom,
--       -- what I now need is to replace
--       -- localize_more_left (f j) (f k) ∘ of_comm_ring Rr (powers (f j))
--       -- with 
--       -- of_comm_ring Rr (powers (f j * f k)) 
--       -- rw ←(loc_more_left_universal_property (f j) (f k)).R_alg_hom, -- something like this should work.
--       unfold localize_more_right,
--       show (((fcjk j k).to_ring_equiv).to_equiv).to_fun ∘
--         (away.extend_map_of_im_unit (of_comm_ring Rr (powers (f j * f k))) _ ∘
--         of_comm_ring Rr (powers (f k))) ∘ of_comm_ring R (powers r) =
--         of_comm_ring R (non_zero_on_U (Ui j ∩ Ui k)),
--         rw ←(away_universal_property (f k) (of_comm_ring Rr (powers (f j * f k))) _).R_alg_hom,
--       rw ←(fcjk j k).R_alg_hom,
--       -- done :-)
--     have HRralg₂ : F1₂ ∘ of_comm_ring Rr (powers (f k)) = F2₂ ∘ of_comm_ring Rr (powers (f k)),
--       let Htemp₂ := unique_R_alg_from_loc (F2₂ ∘ of_comm_ring Rr (powers (f k))),
--       rw (Htemp₂.is_unique (F1₂ ∘ of_comm_ring Rr (powers (f k)))),
--       exact HRalg₂.symm,
--     let Htemp'₂ := unique_R_alg_from_loc (F1₂),
--     rwa Htemp'₂.is_unique (F2₂),

--   show ∀ (s : Π (i : γ), loc Rr (powers (f i))), H4'' (tag00EJ.β s) = bc' (H3' s),
--   intro s,
--   show H4'' (tag00EJ.β₁ s - tag00EJ.β₂ s) = bc'₁ (H3' s) - bc'₂ (H3' s),
--   rw ←(Hb1 s),
--   rw ←(Hb2 s),
--   -- ⇑H4'' (tag00EJ.β₁ s - tag00EJ.β₂ s) = ⇑H4'' (tag00EJ.β₁ s) - ⇑H4'' (tag00EJ.β₂ s)
--   show H4'' (tag00EJ.β₁ s + -tag00EJ.β₂ s) = H4'' (tag00EJ.β₁ s) + -H4'' (tag00EJ.β₂ s),
--   rw ←is_add_group_hom.neg H4'',
--   rw is_add_group_hom.add H4'',
--   have H5 : bc' si = 0, -- follows from Hglue,
--   { show bc'₁ si - bc'₂ si = 0,
--       suffices this7 : bc'₁ si = bc'₂ si,
--       rw this7,simp,
--     funext j k,
--     exact Hglue j k
--   },
--   have H6 := Hcanonical si H5,
--   cases H6 with s Hs,
--   existsi s,
--   split,
--     intro i,
--     rw ←Hs.left,
--     refl,

--   intros y Hy,
--   apply Hs.2 y,
--   funext i,
--   rw ←(Hy i),
--   refl 
-- end 
-- -- now tags 009Hff should get us home

-- -- 009L should show we have a sheaf on a basis
-- -- 009N gives us a sheaf of sets on the space

-- lemma zariski.sheaf_of_types_on_standard_basis (R : Type u) [comm_ring R] :
--   ∀ (U : set (X R)) (BU : U ∈ (standard_basis R)) (γ : Type u)
--   (Ui : γ → set (X R)) (BUi :  ∀ i : γ, (Ui i) ∈ (standard_basis R))
--   (Hcover: (⋃ (i : γ), (Ui i)) = U),
--   sheaf_property_for_standard_basis (D_f_form_basis R) (zariski.structure_presheaf_of_types_on_basis_of_standard R)
--    (zariski.standard_basis_has_FIP R) U BU γ Ui BUi Hcover :=
-- lemma_cofinal_systems_coverings_standard_case (D_f_form_basis R)
--   (zariski.structure_presheaf_of_types_on_basis_of_standard R) 
--   (zariski.standard_basis_has_FIP R)
--   (zariski.basis_is_compact R) -- standard basis is compact
--   (zariski.sheaf_of_types_on_standard_basis_for_finite_covers R)-- (zariski.sheaf_of_types_on_standard_basis_for_finite_covers )

-- lemma zariski.sheaf_of_types_on_basis (R : Type u) [comm_ring R] :
--   is_sheaf_of_types_on_basis (zariski.structure_presheaf_of_types_on_basis_of_standard R) := 
-- λ U BU γ Ui BUi Hcover β Hij Hijk Hcov2 si Hglue,
-- begin
--   refine zariski.sheaf_of_types_on_standard_basis R U BU γ Ui BUi Hcover si _,
--   intros i j,
--   have H := zariski.sheaf_of_types_on_standard_basis R (Ui i ∩ Ui j)
--     (zariski.standard_basis_has_FIP R (Ui i) (Ui j) (BUi i) (BUi j))
--     (β i j) (Hij i j) (Hijk i j) (Hcov2 i j) (λ k,(zariski.structure_presheaf_of_types_on_basis_of_standard R).res (BUi i) (Hijk i j k)
--         (is_sheaf_of_types_on_basis._proof_1 Ui Hij Hcov2 i j k)
--         (si i)) _,
--     tactic.swap,
--     intros i' j',
--     let Fres := (zariski.structure_presheaf_of_types_on_basis_of_standard R).res,
--     show ((Fres _ _ _) ∘ (Fres _ _ _)) _ = ((Fres _ _ _) ∘ (Fres _ _ _)) _,
--     rw [←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp],
--     rw [←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp],
--   cases H with s Hs,
--   have H1 := Hs.2 ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res (BUi i)
--       (sheaf_property_for_standard_basis._proof_2 (zariski.standard_basis_has_FIP R) γ (λ (i : γ), Ui i)
--          (λ (i : γ), BUi i)
--          i
--          j)
--       (sheaf_property_for_standard_basis._proof_3 γ (λ (i : γ), Ui i) i j)
--       (si i)),
--   have H2 := Hs.2 ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res (BUi j)
--       (sheaf_property_for_standard_basis._proof_4 (zariski.standard_basis_has_FIP R) γ (λ (i : γ), Ui i)
--          (λ (i : γ), BUi i)
--          i
--          j)
--       (sheaf_property_for_standard_basis._proof_5 γ (λ (i : γ), Ui i) i j)
--       (si j)),
--   rw (H1 _),
--     rw (H2 _),
--     intro k,
--     let Fres := (zariski.structure_presheaf_of_types_on_basis_of_standard R).res,
--     show ((Fres _ _ _) ∘ (Fres _ _ _)) (si j) = (Fres _ _ _) (si i),
--     rw [←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp],
--     exact (Hglue i j k).symm,
--   intro k,
--   let Fres := (zariski.structure_presheaf_of_types_on_basis_of_standard R).res,
--   show ((Fres _ _ _) ∘ (Fres _ _ _)) (si i) = (Fres _ _ _) (si i),
--     rw [←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp],
-- end

-- definition zariski.structure_presheaf_of_types (R : Type u) [comm_ring R] :
-- presheaf_of_types (X R) := 
--   extend_off_basis (zariski.structure_presheaf_of_types_on_basis_of_standard R)
--   (zariski.sheaf_of_types_on_basis R)

-- /-- structure sheaf on Spec(R) is indeed a sheaf -/
-- theorem zariski.structure_sheaf_is_sheaf_of_types (R : Type u) [comm_ring R] :
-- is_sheaf_of_types (zariski.structure_presheaf_of_types R)
-- := extension_is_sheaf 
--   (zariski.structure_presheaf_of_types_on_basis_of_standard R)
--   (zariski.sheaf_of_types_on_basis R)

-- -- still need that it's a sheaf of rings
