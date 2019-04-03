/-
  Properties of Spec(R).

  https://stacks.math.columbia.edu/tag/00E0
-/

import to_mathlib.ideals
import spectrum_of_a_ring.spectrum

open lattice

noncomputable theory

local attribute [instance] classical.prop_decidable

universe u

section properties

variables {R : Type u} [comm_ring R]

-- Lemma 1.
-- The spectrum of a ring R is empty if and only if R is the zero ring.

lemma Spec.empty_iff_zero_ring : (Spec R → false) ↔ subsingleton R :=
begin
  split,
  { intros H,
    constructor,
    intros a b,
    have Hzo : (0 : R) = 1,
    { by_contra Hzno,
      replace Hzno : (0 : R) ≠ 1 := λ H, (Hzno H),
      have HTnB : (⊥ : ideal R) ≠ ⊤ := zero_ne_one_bot_ne_top Hzno,
      rcases (ideal.exists_le_maximal ⊥ HTnB) with ⟨M, ⟨HM, HBM⟩⟩,
      have MP : ideal.is_prime _ := ideal.is_maximal.is_prime HM,
      apply H,
      exact ⟨M, MP⟩, },
    calc a = a * 0 : by rw [Hzo, mul_one]
      ...  = b * 0 : by simp
      ...  = b     : by rw [Hzo, mul_one], },
  { intros Hsub X,
    cases Hsub,
    rcases X with ⟨X, ⟨HC, PX⟩⟩,
    apply HC,
    apply ideal.ext,
    intros x,
    split,
    { intros Hx,
      trivial, },
    { intros Hx,
      rw (Hsub x 0),
      exact X.2, } }
end

-- Lemma 5.
-- V(S) = V((S)).

lemma Spec.V.set_eq_span (S : set R) : Spec.V S = Spec.V (ideal.span S).1 :=
set.ext $ λ ⟨I, PI⟩,
⟨λ HI x Hx,
  begin 
    have HxI := (ideal.span_mono HI) Hx, 
    rw ideal.span_eq at HxI,
    exact HxI,
  end,
 λ HI x Hx, HI (ideal.subset_span Hx)⟩

-- Lemma 8.
-- V(I) = ∅ iff I = R.

lemma Spec.V.empty_iff_ideal_top (I : ideal R) : Spec.V I.1 = ∅ ↔ I = ⊤ :=
begin
  split,
  { intros HI,
    by_contradiction HC,
    suffices Hsuff : ∃ x, x ∈ Spec.V I.1,
      cases Hsuff with x Hx,
      rw set.eq_empty_iff_forall_not_mem at HI,
      exact HI x Hx,
    rcases (ideal.exists_le_maximal I HC) with ⟨M, ⟨HM, HBM⟩⟩,
    have MP : ideal.is_prime M := ideal.is_maximal.is_prime HM,
    use [⟨M, MP⟩],
    exact HBM, },
  { intros HI,
    rw [HI, set.eq_empty_iff_forall_not_mem],
    rintros ⟨J, PJ⟩ HnJ,
    have HJ : J = ⊤ := le_antisymm (λ x Hx, trivial) HnJ,
    exact PJ.1 HJ, }
end

-- Lemma 15.
-- If f,g ∈ R, then D(fg) = D(f) ∩ D(g).

lemma Spec.V'.product_eq_union (f g : R) : Spec.V' (f * g) = Spec.V' f ∪ Spec.V' g :=
begin
  unfold Spec.V',
  apply set.ext,
  rintros ⟨x, Px⟩,
  split,
  { intros Hx,
    have Hfg : f * g ∈ x := Hx,
    have Hforgx := Px.2 Hfg,
    cases Hforgx,
    { left,
      apply Hforgx, },
    { right,
      apply Hforgx, } },
  { intros Hx,
    cases Hx,
    { have Hf : f ∈ x := Hx,
      apply ideal.mul_mem_right x Hf, },
    { have Hg : g ∈ x := Hx,
      apply ideal.mul_mem_left x Hg, } }
end

lemma Spec.D'.product_eq_inter (f g : R) : Spec.D' (f * g) = Spec.D' f ∩ Spec.D' g :=
begin
  unfold Spec.D',
  rw Spec.V'.product_eq_union,
  rw set.compl_union,
end

-- Lemma 16.
-- ⋃D(fi) is the complement of V({fi}).

lemma Spec.D'.union (F : set R) : ⋃₀ ((Spec.D') '' F) = -Spec.V F :=
begin
  apply set.ext,
  intros x,
  split,
  { intros Hx HC,
    rcases Hx with ⟨Df, HDf, Hx⟩,
    rcases HDf with ⟨f, Hf, HDf⟩,
    rw ←HDf at Hx,
    apply Hx,
    exact HC Hf, },
  { intros Hx,
    have Hf := not_forall.1 Hx,
    rcases Hf with ⟨f, Hf⟩,
    rw not_imp at Hf,
    rcases Hf with ⟨HfF, Hfnx⟩,
    use [Spec.D' f, ⟨f, HfF, rfl⟩], }
end

end properties
