/-
  Properties of Spec(R).

  https://stacks.math.columbia.edu/tag/00E0
-/

import algebra.module
import ring_theory.localization
import to_mathlib.ideals
import to_mathlib.localization.localization_alt
import spectrum_of_a_ring.spec

open lattice

noncomputable theory

local attribute [instance] classical.prop_decidable

universe u

section properties

variables {R : Type u} [comm_ring R]

open Spec

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

lemma Spec.V.set_eq_span (S : set R) : Spec.V S = Spec.V (ideal.span S) :=
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

lemma Spec.V.empty_iff_ideal_top (I : ideal R) : V(I.1) = ∅ ↔ I = ⊤ :=
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

lemma Spec.V'.product_eq_union (f g : R) : V'(f * g) = V'(f) ∪ V'(g) :=
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

lemma Spec.D'.product_eq_inter (f g : R) : D'(f * g) = D'(f) ∩ D'(g) :=
begin
  unfold Spec.D',
  rw Spec.V'.product_eq_union,
  rw set.compl_union,
end

-- Lemma 16.
-- ⋃D(fi) is the complement of V({fi}).

lemma Spec.D'.union (F : set R) : ⋃₀ (D' '' F) = -V(F) :=
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


-- D(g) ⊆ D(f) → f ∈ R[1/g]*.

--set_option trace.class_instances true

lemma inverts.of_Dfs_subset {f g : R} (H : D'(g) ⊆ D'(f)) 
: localization_alt.inverts (powers f) (localization.of : R → localization R (powers g)) :=
begin
  rintros ⟨fn, Hfn⟩,
  suffices Hsuff : ∃ si, (localization.of : R → localization R (powers g)) f * si = 1,
    rcases Hsuff with ⟨si, Hsi⟩,
    show ∃ si, localization.of fn * si = 1,
    rcases Hfn with ⟨n, Hfn⟩,
    rw ←Hfn,
    clear Hfn,
    induction n with n Hn,
    { simp, },
    { rw pow_succ,
      rw (@is_ring_hom.map_mul _ _ _ _ localization.of localization.of.is_ring_hom),
      rcases Hn with ⟨sin, Hn⟩,
      existsi (si * sin),
      rw ←mul_assoc,
      rw mul_assoc _ _ si,
      rw mul_comm _ si,
      rw ←mul_assoc,
      rw Hsi,
      rw one_mul,
      exact Hn, },
  unfold Spec.D' at H,
  rw set.compl_subset_compl at H,
  unfold Spec.V' at H,
  by_contra Hne,
  rw not_exists at Hne,
  have Hnu : ¬is_unit ((localization.of : R → localization R (powers g)) f),
    intros HC,
    simp [is_unit] at HC,
    rcases HC with ⟨u, HC⟩,
    apply (Hne u.inv),
    rw HC,
    exact u.3,
  letI Rgr : comm_ring (localization.away g) := by apply_instance, 
  let F : ideal (localization.away g) := ideal.span {(localization.of f)},
  rcases (ideal.exists_le_maximal F (λ HC, Hnu (ideal.span_singleton_eq_top.1 HC))) with ⟨S, ⟨HMS, HFS⟩⟩,
  have HfF : (localization.of f : localization.away g) ∈ F,
    suffices Hsuff : localization.of f ∈ {localization.of f},
      refine ideal.subset_span Hsuff,
    exact set.mem_singleton _,
  have HfM : localization.of f ∈ S := HFS HfF,
  have PS := ideal.is_maximal.is_prime HMS,
  have PS' : ideal.is_prime (ideal.comap localization.of S)
    := @ideal.is_prime.comap _ _ _ _ localization.of _ _ PS,
  let S' : Spec R := ⟨ideal.comap localization.of S, PS'⟩,
  have HfS' : f ∈ S'.val,
    erw ideal.mem_comap,
    exact HfM,
  replace HfS' : S' ∈ {P : Spec R | f ∈ P.val} := HfS',
  have HgS' : g ∈ ideal.comap localization.of S := H HfS',
  rw ideal.mem_comap at HgS',
  rcases (localization.coe_is_unit R (powers g) ⟨g, ⟨1, pow_one g⟩⟩) with ⟨w, Hw⟩,
  rcases w with ⟨w, winv, Hwwinv, Hwinvw⟩,
  change localization.of g = w at Hw,
  have HC : localization.of g * winv ∈ S := ideal.mul_mem_right S HgS',
  erw [Hw, Hwwinv] at HC,
  exact ((ideal.ne_top_iff_one S).1 PS.1) HC,
end

-- D(g) ⊆ D(f) → ∃ a e, g^e = a * f.

lemma pow_eq.of_Dfs_subset {f g : R} (H : D'(g) ⊆ D'(f)) 
: ∃ (a : R) (e : ℕ), g^e = a * f :=
begin 
  have Hinv := inverts.of_Dfs_subset H,
  rcases (Hinv ⟨f, ⟨1, pow_one f⟩⟩) with ⟨w, Hw⟩,
  dsimp only [subtype.coe_mk] at Hw,
  rcases (quotient.exists_rep w) with ⟨⟨a, ⟨gn, ⟨n, Hn⟩⟩⟩, Hagn⟩,
  erw [←Hagn, quotient.eq] at Hw,
  rcases Hw with ⟨gm, ⟨⟨m, Hm⟩, Hw⟩⟩,
  simp [-sub_eq_add_neg] at Hw,
  rw [sub_mul, sub_eq_zero, mul_assoc, mul_comm f, ←Hn, ←Hm, ←pow_add] at Hw,
  existsi [a * g ^ m, n + m],
  exact Hw,
end

end properties
