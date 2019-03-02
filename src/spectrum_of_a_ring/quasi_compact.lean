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

section refinement

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

end refinement

-- A cover by basis elements has a finite subcover.

section quasi_compact

parameters (R : Type u) [comm_ring R]

lemma D_fs_quasi_compact : 
∀ S : set R, ⋃₀ (Spec.D' '' S) = Spec.univ R →
∃ F ⊆ S, 
    set.finite F 
  ∧ ⋃₀ (Spec.D' '' F) = Spec.univ R :=
begin
  rintros S HScov,
  -- We get that V(S) = ∅.
  have HVS : Spec.V S = ∅,
    rw Spec.D'.union at HScov,
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
    rw Spec.D'.union,
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

lemma D_fs.subset : ∀ {D}, D ⊆ D_fs R → ∃ S, (Spec.DO R '' S) = D :=
begin
  intros D HD,
  use {f : R | ∃ U : opens (Spec R), U ∈ D ∧ U.1 = Spec.D' f },
  apply set.ext,
  intros x,
  split,
  { intros Hx,
    rcases Hx with ⟨f, ⟨Hf, Hx⟩⟩,
    rcases Hf with ⟨Df, ⟨HDf, HDfval⟩⟩,
    rw ←Hx,
    have Heq : Df = Spec.DO R f,
      apply opens.ext,
      exact HDfval,
    rw ←Heq,
    exact HDf, },
  { intros Hx,
    have HxD := HD Hx,
    rcases HxD with ⟨f, Hf⟩,
    simp,
    use [f, x],
    { exact ⟨Hx, Hf⟩, },
    { apply opens.ext,
      exact Hf.symm, } }
end

lemma Spec.DO.val_eq_D' : subtype.val ∘ Spec.DO R = Spec.D' :=
begin
  rw function.funext_iff,
  intros f,
  simp [Spec.DO],
end

lemma Spec.quasi_compact.aux : compact (Spec.univ R) :=
begin
  rw compact_iff_finite_subcover,
  intros C HC Hcov,
  replace Hcov := set.subset.antisymm Hcov (λ x Hx, trivial),
  let OC := covering.from_cover (@opens.univ (Spec R) _) C HC Hcov,
  have BDfs : opens.is_basis (D_fs R) := D_fs_basis R,
  have BC := @refine_cover_with_basis (Spec R) _ (D_fs R) BDfs OC,
  rcases BC with ⟨D, ⟨BD, HDUi, HUD⟩⟩,
  have HS := D_fs.subset BD,
  rcases HS with ⟨S, HS⟩,
  rw ←HS at HUD,
  replace HUD := subtype.ext.1 HUD,
  rw opens.Sup_s at HUD,
  rw ←set.image_comp at HUD,
  rw Spec.DO.val_eq_D' at HUD,
  have HF := D_fs_quasi_compact S HUD,
  rcases HF with ⟨F, HFS, ⟨HFfin, HFcov⟩⟩,
  have HUD : ∀ {U}, U ∈ Spec.DO R '' F → U ∈ D,
    intros U HU,
    rcases HU with ⟨f, ⟨Hf, HU⟩⟩,
    replace Hf := HFS Hf,
    rw ←HS,
    exact ⟨f, ⟨Hf, HU⟩⟩,
  let Fisaux : ∀ {U}, U ∈ (Spec.DO R '' F) → set (Spec R) :=
    λ U HU, (OC.Uis (classical.some (HDUi U (HUD HU)))).1,
  let Finsprop := λ U HU, classical.some_spec (HDUi U (HUD HU)),
  let Fis : { f // f ∈ F } → set (Spec R) :=
    λ U, Fisaux ⟨U, ⟨U.2, rfl⟩⟩,
  use [set.range Fis],
  have HFis : set.range Fis ⊆ C,
    intros U HU,
    rcases HU with ⟨f, Hf⟩,
    rw ←Hf,
    simp [Fis],
    apply covering.from_cover.Uis,
  use [HFis],
  split,
  { constructor,
    replace HFfin := set.finite.fintype HFfin,
    apply @set.fintype_range _ _ _ Fis HFfin, },
  { intros x Hx,
    have Hx' := Hx,
    have HUis : (⋃OC.Uis).val = Spec.univ R := (subtype.ext.1 OC.Hcov),
    rw ←HFcov at Hx,
    rcases Hx with ⟨U, ⟨⟨f, ⟨Hf, HDf⟩⟩, HxU⟩⟩,
    rw ←HDf at HxU,
    use [Fis ⟨f, Hf⟩],
    use [⟨f, Hf⟩],
    have HDfUi := Finsprop ⟨Spec.D' f, D_fs_open R f⟩ ⟨f, ⟨Hf, rfl⟩⟩,
    simp [Fis],
    exact HDfUi HxU, },
end

lemma Spec.compact : compact_space (Spec R) :=
begin
  constructor,
  apply Spec.quasi_compact.aux,
end

end quasi_compact
