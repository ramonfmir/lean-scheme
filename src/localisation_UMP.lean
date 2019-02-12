-- import ring_theory.ideals
-- import ring_theory.localization

-- universes u v w uu

-- namespace localization

-- variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β]
-- variables {S : set α} [is_submonoid S] (f : α → β) [is_ring_hom f]

-- definition is_unit {R : Type u} [comm_ring R] (f : R) := ∃ finv : R, f * finv = 1

-- lemma unit_of_prod_unit {R : Type u} [comm_ring R] (f g : R) : is_unit (f * g) → is_unit f :=
-- begin
--   intro Hfgunit,cases Hfgunit with u Hu,
--   rw mul_assoc at Hu,
--   existsi g * u,
--   exact Hu
-- end

-- -- should this be in term mode?
-- lemma im_unit_of_unit {α : Type u} {β : Type u} [comm_ring α] [comm_ring β] (f : α → β)
-- [Hf : is_ring_hom f]
-- {u : α} (Hunit : is_unit u) : is_unit (f u) :=
-- begin
--   cases Hunit with v Hv,
--   existsi (f v),
--   rw [←Hf.map_mul,Hv,Hf.map_one],
-- end 

-- theorem unit_of_in_S {s : α} (Hs : s ∈ S) : ∃ y : loc α S, (of_comm_ring α S s) * y = 1 :=
-- ⟨⟦(1, ⟨s,Hs⟩)⟧, by apply quotient.sound; existsi (1:α); existsi is_submonoid.one_mem S; simp⟩

-- noncomputable def extend_map_of_im_unit
--   (H : ∀ s ∈ S, ∃ t, f s * t = 1) : loc α S → β :=
-- quotient.lift
--   (λ r, f r.1 * classical.some (H r.2.1 r.2.2) : α × S → β)
--   (λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ ⟨t, hts, ht⟩,
--      have h1 : f ((s1 * r2 - s2 * r1) * t) = 0,
--        by rw ht; simp [ht, is_ring_hom.map_zero f],
--      calc
--           f r1 * classical.some (H s1 hs1)
--         = (f r1 * 1) * classical.some (H s1 hs1) : by simp
--     ... = (f r1 * (f s2 * classical.some (H s2 hs2)) * (f t * classical.some (H t hts))) * classical.some (H s1 hs1) :
--             by simp [classical.some_spec (H t hts), classical.some_spec (H s2 hs2)]
--     ... = (f (s2 * r1 * t) * classical.some (H t hts)) * classical.some (H s1 hs1) * classical.some (H s2 hs2) :
--             by simp [is_ring_hom.map_mul f, mul_assoc, mul_comm, mul_left_comm]
--     ... = (f ((s1 * r2 - s2 * r1) * t + s2 * r1 * t) * classical.some (H t hts)) * classical.some (H s1 hs1) * classical.some (H s2 hs2) :
--             by rw ht; simp [ht]
--     ... = (f (s1 * r2 * t) * classical.some (H t hts)) * classical.some (H s1 hs1) * classical.some (H s2 hs2) :
--             by rw [sub_mul, sub_add_cancel]
--     ... = f r2 * classical.some (H s2 hs2) * (f s1 * classical.some (H s1 hs1)) * (f t * classical.some (H t hts)) :
--             by simp [is_ring_hom.map_mul f, mul_assoc, mul_comm, mul_left_comm]
--     ... = f r2 * classical.some (H s2 hs2) : by simp [classical.some_spec (H s1 hs1), classical.some_spec (H t hts)])

-- instance extend_map_of_im_unit.is_ring_hom (H : ∀ s ∈ S, ∃ t, f s * t = 1)
--   : is_ring_hom (extend_map_of_im_unit f H) :=
-- { map_add := λ x y, quotient.induction_on₂ x y $ λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩, calc
--           f (s1 * r2 + s2 * r1) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))
--         = f (s1 * r2 + s2 * r1) * (f s1 * classical.some (H s1 hs1)) * (f s2 * classical.some (H s2 hs2)) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2)) :
--             by simp [classical.some_spec (H s1 hs1), classical.some_spec (H s2 hs2)]
--     ... = (f r1 * classical.some (H s1 hs1) * (f s2 * classical.some (H s2 hs2)) + f r2 * classical.some (H s2 hs2) * (f s1 * classical.some (H s1 hs1))) * (f (s1 * s2) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))) :
--             by simp [is_ring_hom.map_add f, is_ring_hom.map_mul f]; ring SOP
--     ... = f r1 * classical.some (H s1 hs1) + f r2 * classical.some (H s2 hs2) :
--             by simp [classical.some_spec (H s1 hs1), classical.some_spec (H s2 hs2), classical.some_spec (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))],
--   map_mul := λ x y, quotient.induction_on₂ x y $ λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩, calc
--           f (r1 * r2) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))
--         = f (r1 * r2) * (f s1 * classical.some (H s1 hs1)) * (f s2 * classical.some (H s2 hs2)) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2)) :
--             by simp [classical.some_spec (H s1 hs1), classical.some_spec (H s2 hs2)]
--     ... = f r1 * classical.some (H s1 hs1) * (f r2 * classical.some (H s2 hs2)) * (f (s1 * s2) * classical.some (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))) :
--             by simp [is_ring_hom.map_mul f, mul_assoc, mul_comm, mul_left_comm]
--     ... = f r1 * classical.some (H s1 hs1) * (f r2 * classical.some (H s2 hs2)) :
--             by simp [classical.some_spec (H (s1 * s2) (is_submonoid.mul_mem hs1 hs2))],
--   map_one := classical.some_spec (H 1 (is_submonoid.one_mem _)) }

-- -- extensions are R-algebra homomorphisms
-- theorem extend_map_extends (H : ∀ s ∈ S, ∃ t, f s * t = 1) : 
--   ∀ r : α, extend_map_of_im_unit f H (of_comm_ring _ _ r) = f r :=
-- λ r, calc f r * classical.some (H 1 (of_comm_ring._proof_1 α S))
--         = f r * (f 1 * classical.some (H 1 (of_comm_ring._proof_1 α S))) : by simp [is_ring_hom.map_one f]
--     ... = f r : by simp [classical.some_spec (H 1 (of_comm_ring._proof_1 α S))]

-- -- R-algebra hom extensions are unique
-- theorem extend_map_unique (H : ∀ s ∈ S, ∃ t, f s * t = 1) (phi : loc α S → β) [is_ring_hom phi]
--   (R_alg_hom : ∀ r : α, phi (of_comm_ring _ _ r) = f r) : phi = extend_map_of_im_unit f H :=
-- funext $ quotient.ind begin
--   intro f,
--   rcases f with ⟨r, s, hs⟩,
--   dsimp [extend_map_of_im_unit],
--   rw [← localization.mul_inv_denom, is_ring_hom.map_mul phi, R_alg_hom],
--   congr,
--   have h1 : of_comm_ring α S 1 = 1 := rfl,
--   exact calc phi ⟦(1, ⟨s, hs⟩)⟧
--            = phi ⟦(1, ⟨s, hs⟩)⟧ * (f s * classical.some (H s hs)) : by simp [classical.some_spec (H s hs)]
--        ... = phi ⟦(1, ⟨s, hs⟩)⟧ * (phi (of_comm_ring _ _ s) * classical.some (H s hs)) : by rw R_alg_hom
--        ... = classical.some (H s hs) : by rw [← mul_assoc, ← is_ring_hom.map_mul phi, localization.mul_denom, h1, is_ring_hom.map_one phi, one_mul]
-- end

-- -- very common use case corollaries (proofs should be trivial consequences of the above)

-- -- start with a lemma used again and again
-- lemma away.in_powers (x : α) : x ∈ (powers x) := ⟨1,by simp⟩

-- noncomputable def away.extend_map_of_im_unit {x : α} (H : ∃ y, f x * y = 1) : away x → β :=
-- extend_map_of_im_unit f $ begin
--   intros s hs,
--   cases hs with n hxns,
--   induction n with n ih generalizing s hxns,
--   { existsi (1:β),
--     rw ← hxns,
--     simp [is_ring_hom.map_one f] },
--   { specialize ih _ rfl,
--     cases H with y hy,
--     cases ih with t ht,
--     existsi t * y,
--     rw [← hxns, pow_succ, is_ring_hom.map_mul f],
--     rw [mul_assoc, ← mul_assoc _ t, ht, one_mul, hy] }
-- end

-- instance away.extend_map_of_im_unit.is_ring_hom {x : α} (H : ∃ y, f x * y = 1) :
--   is_ring_hom (away.extend_map_of_im_unit f H) :=
-- extend_map_of_im_unit.is_ring_hom f _

-- theorem away.extend_map_extends {x : α} (H : ∃ y, f x * y = 1) :
--   ∀ r : α, away.extend_map_of_im_unit f H (of_comm_ring _ _ r) = f r :=
-- extend_map_extends f _

-- theorem away.extension_unique {x : α} (H : ∃ y, f x * y = 1) (phi : away x → β) [is_ring_hom phi]
--   (R_alg_hom : ∀ r : α, phi (of_comm_ring _ _ r) = f r) : phi = away.extend_map_of_im_unit f H :=
-- extend_map_unique f _ phi R_alg_hom



-- -- note that one could make the above definition constructive:

-- --definition inv_of_in_S (s : S) : loc α S := ⟦(1,s)⟧

-- --theorem inv_of_in_S_is_inv (s : S) : (of_comm_ring α S s) * inv_of_in_S s = 1 :=
-- --by cases s; apply quotient.sound; existsi (1:α); existsi is_submonoid.one_mem S; simp

-- -- note one could also make localization R[1/f] computable to an extent.

-- -- definition inv_of_powers (g : α) : loc α (powers g) := ⟦(1,⟨g,1,by simp⟩)⟧ 

-- -- map is determined by image of ring before localization

-- theorem unique {f g : loc α S → β} [is_ring_hom f] [is_ring_hom g] (H : ∀ x, f (of_comm_ring _ _ x) = g (of_comm_ring _ _ x)) {x : loc α S} :
--   f x = g x :=
-- quotient.induction_on x $ λ ⟨r, s, hs⟩,
-- have h1 : f ⟦(1, ⟨s, hs⟩)⟧ = g ⟦(1, ⟨s, hs⟩)⟧,
-- from calc f ⟦(1, ⟨s, hs⟩)⟧
--         = g 1 * f ⟦(1, ⟨s, hs⟩)⟧ : by simp [is_ring_hom.map_one g]
--     ... = g ⟦(1, ⟨s, hs⟩)⟧ * f (of_comm_ring _ _ s) * f ⟦(1, ⟨s, hs⟩)⟧ : by rw [H, ← is_ring_hom.map_mul g, mul_denom]; refl
--     ... = g ⟦(1, ⟨s, hs⟩)⟧ * f 1 : by rw [mul_assoc, ← is_ring_hom.map_mul f, mul_comm (of_comm_ring α S s), mul_denom]; refl
--     ... = g ⟦(1, ⟨s, hs⟩)⟧ : by simp [is_ring_hom.map_one f],
-- by rw [← mul_inv_denom, is_ring_hom.map_mul f, is_ring_hom.map_mul g, H, h1]


-- noncomputable def localize_more_left {R : Type u} [comm_ring R] (f g) : 
--   localization.loc R (powers f) → localization.loc R (powers (f * g)) :=
-- localization.away.extend_map_of_im_unit (localization.of_comm_ring R _) $
-- ⟨⟦⟨g, f * g, 1, by simp⟩⟧, by simp [localization.of_comm_ring, localization.mk_eq, localization.mul_frac]⟩

-- instance localize_more_left_is_ring_hom {R : Type u} [comm_ring R] (f g : R) :
-- is_ring_hom (localize_more_left f g) := by apply away.extend_map_of_im_unit.is_ring_hom

-- noncomputable def localize_more_right {R : Type u} [comm_ring R] (f g) :
--   localization.loc R (powers g) → localization.loc R (powers (f * g)) :=
-- localization.away.extend_map_of_im_unit (localization.of_comm_ring R _) $
-- ⟨⟦⟨f, f * g, 1, by simp⟩⟧, by simp [localization.of_comm_ring, localization.mk_eq, localization.mul_frac, mul_comm]⟩

-- instance localize_more_right_is_ring_hom {R : Type u} [comm_ring R] (f g : R) :
-- is_ring_hom (localize_more_right f g) := by apply away.extend_map_of_im_unit.is_ring_hom

-- theorem loc_commutes (f g r : α) : 
--   localize_more_left f g (localization.of_comm_ring α (powers f) r) =
--   localize_more_right f g (localization.of_comm_ring α (powers g) r) :=
-- begin
--   dsimp [localize_more_left, localize_more_right],
--   rw away.extend_map_extends,
--   rw away.extend_map_extends
-- end

-- -- localization to a bigger multiplicative set
-- definition localize_superset {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T) :
-- loc R S → loc R T := quotient.lift (λ (x : R × S), ⟦(x.1, (⟨x.2.1, H x.2.2⟩ : T))⟧) $
-- λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩, quotient.sound $ ⟨t, H hts, ht⟩

-- -- localization to a bigger multiplicative set is a ring hom
-- instance localize_superset.is_ring_hom {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T) :
--   is_ring_hom (localize_superset H) :=
-- { map_add := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl,
--   map_mul := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl,
--   map_one := rfl }

-- -- localization to a bigger multiplicative set is an R-algebra hom
-- theorem localize_superset.is_algebra_hom {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T) (r : R) :
-- localize_superset H (of_comm_ring _ _ r) = of_comm_ring _ _ r := rfl

-- -- localization to a bigger multiplicative set is the unique R-algebra map from R[1/S] to R[1/T]
-- theorem localize_superset.unique_algebra_hom {R : Type u} [comm_ring R] {S T : set R} [is_submonoid S] [is_submonoid T] (H : S ⊆ T)
-- (g : loc R S → loc R T) [is_ring_hom g] (R_alg_hom : ∀ (r : R), g (of_comm_ring _ _ r) = of_comm_ring _ _ r) : 
-- g = localize_superset H := (extend_map_unique _ (λ s Hs, unit_of_in_S (H Hs)) _ R_alg_hom).trans $ eq.symm $
-- extend_map_unique _ (λ s Hs, unit_of_in_S (H Hs)) _ $ λ _, rfl


-- -- Here is the way KMB wants to package all these things together.
-- structure is_unique_R_alg_hom {R : Type u} {α : Type v} {β : Type w} [comm_ring R] [comm_ring α] [comm_ring β] 
-- (sα : R → α) (sβ : R → β) (f : α → β) [is_ring_hom sα] [is_ring_hom sβ] [is_ring_hom f] : Prop :=
-- (R_alg_hom : sβ = f ∘ sα)
-- (is_unique : ∀ (g : α → β) [is_ring_hom g], sβ = g ∘ sα → g = f)

-- lemma comp_unique {R : Type u} {α : Type v} {β : Type w} {γ : Type uu} 
--   [comm_ring R] [comm_ring α] [comm_ring β] [comm_ring γ]
--   (sα : R → α) (sβ : R → β) (sγ : R → γ) (f : α → β) (g : β → γ) (h : α → γ)
--   [is_ring_hom sα] [is_ring_hom sβ] [is_ring_hom sγ] [is_ring_hom f] [is_ring_hom g] [is_ring_hom h] :
--   is_unique_R_alg_hom sα sβ f → is_unique_R_alg_hom sβ sγ g → is_unique_R_alg_hom sα sγ h → g ∘ f = h :=
-- λ Uf Ug Uh, Uh.is_unique (g ∘ f : α → γ) (by simp [Uf.R_alg_hom,Ug.R_alg_hom])

-- lemma unique_R_alg_from_R {R : Type u} {α : Type v} [comm_ring R] [comm_ring α] 
-- (sα : R → α) [is_ring_hom sα] : is_unique_R_alg_hom id sα sα := {
--   R_alg_hom := rfl,
--   is_unique := λ g Hg H, by simp [H]
-- }

-- /- What I want is
-- lemma id_unique_R_alg_from_loc {R : Type u} [comm_ring R] (S : set R) [is_submonoid S] :
-- is_unique_R_alg_hom (of_comm_ring R S) (of_comm_ring R S) id
-- but I prove something a bit more general first
-- -/
-- lemma unique_R_alg_from_loc {R : Type u} [comm_ring R] {S : set R} [is_submonoid S]
-- {β : Type v} [comm_ring β] (φ : loc R S → β) [Hphir : is_ring_hom φ] : 
-- is_unique_R_alg_hom (of_comm_ring R S) (φ ∘ of_comm_ring R S) φ := {
--   R_alg_hom := rfl,
--   is_unique := λ g Hg Hphi,begin
--     letI := Hg,
--     let sβ : R → β := φ ∘ of_comm_ring R S,
--     have H : ∀ s ∈ S, ∃ t, sβ s * t = 1,
--     { intros s Hs,
--       cases (unit_of_in_S Hs) with sinv Hsinv,
--       existsi (φ sinv),
--       show φ (of_comm_ring R S s) * φ sinv = 1,
--       rw ←Hphir.map_mul,
--       rw Hsinv,
--       exact Hphir.map_one
--     },
--     -- now show they're both some localization map!
--     change φ ∘ of_comm_ring R S with sβ at Hphi,
--   have Hφ1 : φ = _ := extend_map_unique sβ H φ (λ r, rfl),
--   have Hg1 : g = _ := extend_map_unique (g ∘ of_comm_ring R S) 
--     (Hphi ▸ H) g (λ r,rfl),
--   rw Hφ1,
--   rw Hg1,
--   simp [Hphi],
--   end
-- }

-- lemma id_unique_R_alg_from_loc {R : Type u} [comm_ring R] (S : set R) [is_submonoid S] :
-- is_unique_R_alg_hom (of_comm_ring R S) (of_comm_ring R S) id :=
-- unique_R_alg_from_loc id 

-- /-- universal property of localization at a multiplicative set. -/
-- theorem loc_universal_property {R : Type u} [comm_ring R] {S : set R} [is_submonoid S]
-- {β : Type v} [comm_ring β] (sβ : R → β) [is_ring_hom sβ] (H : ∀ s ∈ S, ∃ t, sβ s * t = 1) :
-- is_unique_R_alg_hom (of_comm_ring R S) sβ (extend_map_of_im_unit sβ H) := 
-- { R_alg_hom := funext (λ r, (extend_map_extends sβ H r).symm),
--   is_unique := λ g Hg HR, by exactI extend_map_unique sβ H g (λ r, by rw HR)
-- }

-- /-- universal property of localization at powers of f -/
-- theorem away_universal_property {R : Type u} [comm_ring R] (f : R)
-- {β : Type v} [comm_ring β] (sβ : R → β) [is_ring_hom sβ] (H : ∃ t, sβ f * t = 1) :
-- is_unique_R_alg_hom (of_comm_ring R (powers f)) sβ (away.extend_map_of_im_unit sβ H) := 
-- { R_alg_hom := funext (λ r, (away.extend_map_extends sβ H r).symm),
--   is_unique := λ g Hg HR, by exactI away.extension_unique sβ H g (λ r, by rw ←HR.symm)
-- }

-- /-- universal property of localization from one mult set to a  bigger mult set -/
-- theorem superset_universal_property {R : Type u} [comm_ring R] (S : set R) [is_submonoid S] 
--   (T : set R) [is_submonoid T] (H : S ⊆ T) :
-- is_unique_R_alg_hom (of_comm_ring R S) (of_comm_ring R T) (localize_superset H) :=
-- { R_alg_hom := funext (λ r, (localize_superset.is_algebra_hom H r).symm),
--   is_unique := λ g Hg HR, by exactI localize_superset.unique_algebra_hom H g (λ r,by rw HR)}

-- -- now we prove that R[1/f][1/g] has a universal property

-- -- First we introduce another tool for proving is_unique_R_alg_hom
-- -- R → α → β → γ; if induced map α → γ is unique R-alg hom and β → γ is unique α-alg hom then it's unique R-alg hom.
-- theorem unique_R_of_unique_R_of_unique_Rloc {R : Type u} {α : Type v} {β : Type w} {γ : Type uu} 
-- [comm_ring R] [comm_ring α] [comm_ring β] [comm_ring γ] 
-- (sα : R → α) [is_ring_hom sα] (fαβ : α → β) [is_ring_hom fαβ] (fβγ : β → γ) [is_ring_hom fβγ] :
-- is_unique_R_alg_hom sα (fβγ ∘ fαβ ∘ sα) (fβγ ∘ fαβ) 
-- → is_unique_R_alg_hom fαβ (fβγ ∘ fαβ) fβγ 
-- → is_unique_R_alg_hom (fαβ ∘ sα) (fβγ  ∘ fαβ ∘ sα) (fβγ) :=
-- begin
--   intros Hαβ Hβγ,
--   constructor,refl,
--   intros gβγ Hgβγ H1,
--   have Hαγ : fβγ ∘ fαβ = gβγ ∘ fαβ,
--     exactI (Hαβ.is_unique (gβγ ∘ fαβ) H1).symm,
--   exactI Hβγ.is_unique gβγ Hαγ,
-- end 

-- lemma unit_of_loc_more_left {R : Type u} [comm_ring R] (f g : R) : 
--   is_unit (of_comm_ring R (powers (f * g)) f) :=
-- begin
--   cases (unit_of_in_S (away.in_powers (f * g))) with ifg Hifg,
--   existsi ((of_comm_ring R (powers (f * g)) g))* ifg,
--   have H : is_ring_hom (of_comm_ring R (powers (f * g))) := by apply_instance,
--   rwa [←mul_assoc,←H.map_mul],
-- end 

-- lemma unit_of_loc_more_right {R : Type u} [comm_ring R] (f g : R) : is_unit (of_comm_ring R (powers (f * g)) g) :=
--   mul_comm g f ▸ unit_of_loc_more_left g f 

-- theorem loc_more_left_universal_property {R : Type u} [comm_ring R] (f g : R) :
-- is_unique_R_alg_hom (of_comm_ring R (powers f)) (of_comm_ring R (powers (f * g))) 
--   (away.extend_map_of_im_unit (of_comm_ring R (powers (f * g))) $ unit_of_loc_more_left f g) :=
-- away_universal_property f (of_comm_ring R (powers (f * g))) (unit_of_loc_more_left f g)

-- theorem loc_more_right_universal_property {R : Type u} [comm_ring R] (f g : R) :
-- is_unique_R_alg_hom (of_comm_ring R (powers g)) (of_comm_ring R (powers (f * g)))
--   (away.extend_map_of_im_unit (of_comm_ring R (powers (f * g))) $ unit_of_loc_more_right f g) :=
-- away_universal_property g (of_comm_ring R (powers (f * g))) (unit_of_loc_more_right f g)

-- -- recall that Kenny proved that the maps R -> R[1/f] -> R[1/fg] and R -> R[1/g] -> R[1/fg] coincided. 
-- -- But this is an immediate consequence of the definition above and comp_unique.

-- end localization