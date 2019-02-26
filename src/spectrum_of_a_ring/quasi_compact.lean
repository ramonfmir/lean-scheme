/-
  Spec(R) is quasi-compact.

  https://stacks.math.columbia.edu/tag/00E8
-/

import spectrum_of_a_ring.standard_basis

universe u

local attribute [instance] classical.prop_decidable

-- this next lemma will go to mathlib one day

-- lemma mem_subset_basis_of_mem_open {X : Type u} [T : topological_space X] {b : set (set X)}
--   (hb : topological_space.is_topological_basis b) {a:X} (u : set X) (au : a ∈ u)
--   (ou : _root_.is_open u) : ∃v ∈ b, a ∈ v ∧ v ⊆ u :=
-- (topological_space.mem_nhds_of_is_topological_basis hb).1 $ mem_nhds_sets ou au


-- a cover can be refined to a cover by a basis
lemma refine_cover_with_basis {X : Type u} [T : topological_space X] 
  (B : set (set X)) (HB : topological_space.is_topological_basis B) 
  (c : set (set X)) (Oc : ∀ U ∈ c, T.is_open U) (Hcov : set.sUnion c = set.univ) :
∃ (d : set (set X)), d ⊆ B ∧ (∀ V ∈ d, ∃ U ∈ c, V ⊆ U) ∧ set.sUnion d = set.univ :=
begin
  existsi λ V, V ∈ B ∧ ∃ U ∈ c, V ⊆ U,
  split,intros V HV,exact HV.1,
  split,intros V HV,exact HV.2,
  apply set.subset.antisymm,simp,
  intros x Hx,
  rw ←Hcov at Hx,
  cases Hx with U HU,
  cases HU with HU Hx,
  cases (mem_subset_basis_of_mem_open HB U Hx (Oc U HU)) with V HV,
  cases HV with HV1 HV2,
  existsi V,
  existsi _,exact HV2.1,
  split,exact HV1,
  existsi U,
  existsi HU,
  exact HV2.2
end 

-- a cover by basis elements has a finite subcover
lemma basis_quasi_compact {R : Type u} [comm_ring R] :
∀ F : set R, @set.univ (X R) = set.Union (λ fF : {f // f ∈ F}, Spec.D' fF.val) →
∃ G : set R, G ⊆ F ∧ set.finite G ∧ 
  @set.univ (X R) = set.Union (λ gG : {g // g ∈ G}, Spec.D' gG.val) :=
begin
  intros F Hcover,
  -- first let's show that the union of D(f), f in F, is all Spec(R)
  have H : @set.univ (X R) = ⋃₀(Spec.D' '' F),
    rw Hcover,
    apply set.ext,
    intro x,simp,
  -- now let's deduce that V(F) is empty.
  rw tag00E0.lemma16 at H,
  have H2 : Spec.V F = ∅,
    rw [←set.compl_compl (Spec.V F),←H,set.compl_univ],
  -- now let's deduce that the ideal gen by F is all of R.
  rw ←tag00E0.lemma05 at H2,
  letI : is_ideal (span F) := is_ideal_span,
  have H3 : span F = set.univ := (tag00E0.lemma08 _ _).1 H2,
  -- now let's write 1 as a finite linear combination of elements of F
  have H4 : (1 : R) ∈ span F := by simp [H3],
  cases H4 with f Hf, -- f is a function R -> R supported on a finite subset of F
  -- now let's build G, finite, with 1 in span G, and then let's run the entire argument backwards.
  let G : set R := {r | r ∈ f.support},
  existsi G, -- need to prove G in F, G finite, and D(g) covers for g in G
  split,
  { show G ⊆ F,
    intros g Hg,
    cases classical.em (g ∈ F) with H5 H5,assumption,
    exfalso,
    have H6 : f g = 0 := Hf.1 g H5,
    exact (f.mem_support_to_fun g).1 Hg H6
  },
  split,
  { show set.finite G, -- G = f.support which is a finset
    exact set.finite_mem_finset _,
  },
  -- goal now to show that union of D(g) is Spec(R)
  -- first reformulate so we can apply lemma16
  suffices H' : @set.univ (X R) = ⋃₀(Spec.D' '' G),
    apply set.ext,simp [H'],
  -- now reduce goal to complement of V(G) is everything
  rw tag00E0.lemma16,
  -- now reduce to V(G) empty
  rw ←set.compl_empty,
  congr,
  -- now reduce to span(G) = R
  rw ←tag00E0.lemma05,
  apply eq.symm,
  letI : is_ideal (span G) := is_ideal_span,
  rw tag00E0.lemma08,
  -- now reduce to 1 in span(G)
  apply is_submodule.univ_of_one_mem (span G),
  -- now prove this
  rw Hf.2,
  existsi f,
  split,swap,refl,
  intros x Hx,
  cases classical.em (f x = 0) with H4 H4,assumption,
  exfalso,
  exact Hx ((f.mem_support_to_fun x).2 H4),
end

-- now deduce main result from compact basis result
lemma lemma_quasi_compact {R : Type u} [comm_ring R] : compact (@set.univ (X R)) :=
begin
  rw compact_iff_finite_subcover,
  intros c HOc Hccov,
  let B := {U : set (X R) | ∃ (f : R), U = Spec.D' f},
  have HB : topological_space.is_topological_basis B := D_f_form_basis R,
  cases (refine_cover_with_basis B HB c HOc (set.subset.antisymm (by simp) Hccov)) with d Hd,
  have HdB : ∀ V ∈ d, ∃ f : R, V = Spec.D' f := λ _ HV,Hd.1 HV,
  have H := basis_quasi_compact (λ f, (Spec.D' f) ∈ d),
  have Hdcov : (⋃ (fHf : {f // Spec.D' f ∈ d}), Spec.D' (fHf.val)) = set.univ,
  { apply set.subset.antisymm,simp,
    rw ←Hd.2.2,
    intros x Hx,cases Hx with V HV,cases HV with HVd HxV,
    existsi V,
    existsi _,
    exact HxV,
    cases Hd.1 HVd with f Hf,
    rw Hf at HVd,
    existsi (⟨f,HVd⟩ : {f // Spec.D' f ∈ d}),
    exact Hf
  },
  cases H (eq.symm Hdcov) with G HG,
  let m : {g // g ∈ G} → set (X R) := λ gG,classical.some (Hd.2.1 (Spec.D' gG.val) (HG.1 gG.property)),
  have mH : ∀ (gG : {g // g ∈ G}), ∃ (H : (m gG) ∈ c), Spec.D' (gG.val) ⊆ (m gG)
      := λ (gG : {g // g ∈ G}), classical.some_spec (Hd.2.1 (Spec.D' gG.val) (HG.1 gG.property)),
  existsi set.range m,
  existsi _,split,
  { have HGfin : set.finite G := HG.2.1,
    exact let ⟨HF⟩ := HGfin in ⟨@set.fintype_range _ _ _ m HF⟩,
  },
  { rw HG.2.2,
    intros x Hx,
    cases Hx with U HU,cases HU with HU HxU,cases HU with gG HU,
    change U = Spec.D' (gG.val)  at HU,
    cases mH gG with H1 H2,
    existsi m gG,
    existsi _,
    { apply H2,
      rw ←HU,
      exact HxU },
    existsi gG,refl
  },
  intros U HU,cases HU with gG HU,
  cases (mH gG) with Hc,
  rw HU at Hc,exact Hc,
end


