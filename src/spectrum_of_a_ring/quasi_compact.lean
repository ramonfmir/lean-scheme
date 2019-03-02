/-
  Spec(R) is quasi-compact.

  https://stacks.math.columbia.edu/tag/00E8
-/

import topology.basic
import linear_algebra.linear_combination
import preliminaries.opens
import preliminaries.covering
import spectrum_of_a_ring.standard_basis

noncomputable theory

local attribute [instance] classical.prop_decidable

universe u

open topological_space lattice

section facts

-- I need this but I really wish I didn't.

lemma ideal.span_mem_finset {R : Type u} [comm_ring R] (S : finset R) (f : R → R)
: finset.sum S (λ a, f a * a) ∈ (@ideal.span R _ ↑S) :=
begin
  unfold ideal.span,
  apply finset.induction_on S,
  { simp, },
  { intros a S Ha IH,
    rw finset.coe_insert,
    rw submodule.mem_span_insert',
    rw finset.sum_insert Ha,
    use [-f a],
    simp [IH], }
end

end facts

variables {α : Type u} [comm_ring α]

section quasi_compact

local attribute [instance] classical.prop_decidable

parameters (X : Type u) [T : topological_space X]
parameters (B : set (opens X)) [HB : opens.is_basis B]

include T HB

lemma refine_cover_with_basis (OC : covering opens.univ) 
: ∃ (D : set (opens X)),
    (D ⊆ B)
  ∧ (∀ V ∈ D, ∃ i, V ⊆ OC.Uis i)
  ∧ (Sup D = opens.univ) :=
begin
  existsi [λ V, V ∈ B ∧ ∃ i : OC.γ, V ⊆ OC.Uis i],
  refine ⟨_, _, _⟩,
  { intros U HU,
    exact HU.1, },
  { intros V HV,
    exact HV.2, },
  { apply opens.ext,
    apply set.ext,
    intros x,
    split,
    { intros Hx,
      simp [opens.univ], },
    { intros Hx,
      rw ←OC.Hcov at Hx,
      rcases Hx with ⟨U, HU, HxU⟩,
      rcases HU with ⟨OU, HOU, HOUval⟩,
      rcases HOU with ⟨i, HOU⟩,
      rw ←HOUval at HxU,
      have HU' := opens.is_basis_iff_nbhd.1 HB HxU,
      rcases HU' with ⟨U', ⟨BU', HxU', HU'OU⟩⟩,
      use U',
      simp,
      refine ⟨⟨_, _⟩, _⟩,
      { exact U'.2, },
      { rw ←HOU at HU'OU,
        exact ⟨BU', ⟨i, HU'OU⟩⟩, },
      { exact HxU', } } }
end

-- A cover by basis elements has a finite subcover.

parameters (R : Type u) [comm_ring R]

lemma D_fs_quasi_compact : 
∀ S : set R, (Spec.D' '' S) ⊆ D_fs R ∧ ⋃₀ (Spec.D' '' S) = Spec.univ R →
∃ F ⊆ S, 
    set.finite F 
  ∧ ⋃₀ (Spec.D' '' F) = Spec.univ R :=
begin
  rintros S ⟨HSDfs, HScov⟩,
  -- We get that V(S) = ∅.
  have HVS : Spec.V S = ∅,
    rw Spec.basic_opens_union at HScov,
    rw ←set.compl_compl (Spec.V S),
    rw HScov,
    exact set.compl_univ,
  rw Spec.V.set_eq_span at HVS,
  -- It follows that (S) = R.
  have HST := (Spec.V.empty_iff_ideal_top _).1 HVS,
  have Hone : (1 : R) ∈ ideal.span S := by simp [HST],
  -- Deduce that 1 = Σrᵢfᵢ for some {f₁, ..., fₙ}.
  have Hlc := mem_span_iff_lc.1 Hone,
  rcases Hlc with ⟨lc, Hlc, H⟩,
  have Hfs := (@_root_.lc.mem_supported _ _ _ _ _ _ _).1 Hlc,
  use ↑lc.support,
  refine ⟨_, _, _⟩,
  { -- {f₁, ..., fₙ} ⊆ S.
    exact Hfs, },
  { -- Prove it's finite.
    apply set.finite_mem_finset, },
  { -- ⋃ D(fᵢ) = Spec(R)
    rw Spec.basic_opens_union,
    simp [Spec.univ],
    rw ←set.compl_empty,
    congr,
    rw Spec.V.set_eq_span,
    rw Spec.V.empty_iff_ideal_top,
    suffices Hsuff : (1:R) ∈ ideal.span (↑(lc.support) : set R),
      rw ((ideal.eq_top_iff_one _).2 Hsuff),
    rw lc.total_apply at H,
    rw ←H,
    simp [finsupp.sum],
    apply ideal.span_mem_finset, }
end


-- -- now deduce main result from compact basis result
-- lemma lemma_quasi_compact {R : Type u} [comm_ring R] : compact (@set.univ (X R)) :=
-- begin
--   rw compact_iff_finite_subcover,
--   intros c HOc Hccov,
--   let B := {U : set (X R) | ∃ (f : R), U = Spec.D' f},
--   have HB : topological_space.is_topological_basis B := D_f_form_basis R,
--   cases (refine_cover_with_basis B HB c HOc (set.subset.antisymm (by simp) Hccov)) with d Hd,
--   have HdB : ∀ V ∈ d, ∃ f : R, V = Spec.D' f := λ _ HV,Hd.1 HV,
--   have H := basis_quasi_compact (λ f, (Spec.D' f) ∈ d),
--   have Hdcov : (⋃ (fHf : {f // Spec.D' f ∈ d}), Spec.D' (fHf.val)) = set.univ,
--   { apply set.subset.antisymm,simp,
--     rw ←Hd.2.2,
--     intros x Hx,cases Hx with V HV,cases HV with HVd HxV,
--     existsi V,
--     existsi _,
--     exact HxV,
--     cases Hd.1 HVd with f Hf,
--     rw Hf at HVd,
--     existsi (⟨f,HVd⟩ : {f // Spec.D' f ∈ d}),
--     exact Hf
--   },
--   cases H (eq.symm Hdcov) with G HG,
--   let m : {g // g ∈ G} → set (X R) := λ gG,classical.some (Hd.2.1 (Spec.D' gG.val) (HG.1 gG.property)),
--   have mH : ∀ (gG : {g // g ∈ G}), ∃ (H : (m gG) ∈ c), Spec.D' (gG.val) ⊆ (m gG)
--       := λ (gG : {g // g ∈ G}), classical.some_spec (Hd.2.1 (Spec.D' gG.val) (HG.1 gG.property)),
--   existsi set.range m,
--   existsi _,split,
--   { have HGfin : set.finite G := HG.2.1,
--     exact let ⟨HF⟩ := HGfin in ⟨@set.fintype_range _ _ _ m HF⟩,
--   },
--   { rw HG.2.2,
--     intros x Hx,
--     cases Hx with U HU,cases HU with HU HxU,cases HU with gG HU,
--     change U = Spec.D' (gG.val)  at HU,
--     cases mH gG with H1 H2,
--     existsi m gG,
--     existsi _,
--     { apply H2,
--       rw ←HU,
--       exact HxU },
--     existsi gG,refl
--   },
--   intros U HU,cases HU with gG HU,
--   cases (mH gG) with Hc,
--   rw HU at Hc,exact Hc,
-- end


