/-
  Properties of Spec(R).

  https://stacks.math.columbia.edu/tag/00E0
-/

import spectrum_of_a_ring.spectrum
import commutative_algebra.find_maximal_ideal

noncomputable theory

local attribute [instance] classical.prop_decidable

universe u

namespace tag00E0

variables {R : Type u} [comm_ring R]

-- These should be obvious.

section facts

lemma zero_ne_one_bot_ne_top : (0 : R) ≠ 1 → (⊥ : ideal R) ≠ ⊤ :=
begin
  intros Hzno,
  have Honz : (1:R) ∉ ({0} : set R),
    intros HC,
    rw set.mem_singleton_iff at HC,
    exact Hzno HC.symm,
  intros HC,
  replace HC := (ideal.eq_top_iff_one ⊥).1 HC,
  exact (Honz HC),
end

end facts

-- The spectrum of a ring R is empty if and only if R is the zero ring.

lemma lemma01 : (Spec R → false) ↔ subsingleton R :=
begin
  split,
  { intros H,
    constructor,
    intros a b,
    have Hzo : (0 : R) = 1,
    { by_contra Hzno,
      replace Hzno : (0 : R) ≠ 1 := λ H, (Hzno H),
      apply H,
      have HTnB : (⊥ : ideal R) ≠ ⊤ := zero_ne_one_bot_ne_top Hzno,
      let M := find_maximal_ideal ⊥ HTnB,
      have MP : ideal.is_prime _ := find_maximal_ideal.is_prime ⊥ HTnB,
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

-- Every nonzero ring has a maximal ideal.

lemma lemma02 : (0 : R) ≠ 1 → ∃ S : ideal R, ideal.is_maximal S :=
begin
  intros Hzno,
  have HTnB : (⊥ : ideal R) ≠ ⊤ := zero_ne_one_bot_ne_top Hzno,
  use [find_maximal_ideal ⊥ HTnB],
  exact find_maximal_ideal.is_maximal_ideal ⊥ HTnB,
end

-- Every nonzero ring has a minimal prime ideal.

-- lemma lemma03 : (0:R) ≠ 1 → ∃ S:set R, is_prime_ideal S ∧ ∀ T, is_prime_ideal T → T ⊆ S → T = S :=
-- λ hzo, let M := is_ideal.find_maximal_ideal.of_zero_ne_one hzo in
-- have hm : is_maximal_ideal M := is_ideal.find_maximal_ideal.of_zero_ne_one.is_maximal_ideal hzo,
-- let S := @is_ideal.find_minimal_prime_ideal' R _ {0} _ M hm.to_is_prime_ideal
--   (λ z hz, by simp at hz; rw hz; exact @is_ideal.zero R _ _ hm.1.1) in
-- have h1 : is_prime_ideal S := @is_ideal.find_minimal_prime_ideal'.is_prime_ideal R _ {0} _ M hm.to_is_prime_ideal
--   (λ z hz, by simp at hz; rw hz; exact @is_ideal.zero R _ _ hm.1.1),
-- have h2 : ∀ T, is_prime_ideal T → {(0:R)} ⊆ T → T ⊆ S → T = S := @is_ideal.find_minimal_prime_ideal'.minimal R _ {0} _ M hm.to_is_prime_ideal
--   (λ z hz, by simp at hz; rw hz; exact @is_ideal.zero R _ _ hm.1.1),
-- ⟨S, h1, λ T ht hts, h2 T ht (λ z hz, by simp at hz; rw hz; exact ht.1.1.1.1) hts⟩

-- lemma lemma04 (I P : set R) [is_ideal I] [is_prime_ideal P] (hip : I ⊆ P) :
--   ∃ Q:set R, is_prime_ideal Q ∧ I ⊆ Q ∧ Q ⊆ P ∧ ∀ S, is_prime_ideal S → I ⊆ S → S ⊆ Q → S = Q :=
-- let Q := is_ideal.find_minimal_prime_ideal I P hip in
-- have h1 : is_prime_ideal Q := is_ideal.find_minimal_prime_ideal.is_prime_ideal I P hip,
-- have h2 : I ⊆ Q := is_ideal.find_minimal_prime_ideal.ideal_contains I P hip,
-- have h3 : Q ⊆ P := is_ideal.find_minimal_prime_ideal.contains_prime I P hip,
-- have h4 : ∀ S, is_prime_ideal S → I ⊆ S → S ⊆ Q → S = Q,
--   from is_ideal.find_minimal_prime_ideal.minimal I P hip,
-- ⟨Q, h1, h2, h3, h4⟩

-- lemma 5

lemma Spec.V.set_eq_span (S : set R) : Spec.V S = Spec.V (ideal.span S) :=
set.ext $ λ ⟨I, PI⟩,
⟨λ HI x Hx,
  begin 
    have HxI := (ideal.span_mono HI) Hx, 
    rw ideal.span_eq at HxI,
    exact HxI,
  end,
 λ HI x Hx, HI (ideal.subset_span Hx)⟩

-- lemma lemma05 (T : set R) : Spec.V (span T) = Spec.V T :=
-- set.ext $ λ x,
-- ⟨λ hx z hz, hx $ subset_span hz,
--  λ hx z hz, span_minimal x.2.1.1.1 hx hz⟩

-- lemma lemma06 (I : set R) [is_ideal I] : Spec.V I = Spec.V (is_ideal.radical I) :=
-- set.ext $ λ x,
-- ⟨λ hx z ⟨n, hz⟩, @@is_prime_ideal.mem_of_pow_mem _ x.2 $ hx hz,
--  λ hx z hz, hx $ is_ideal.subset_radical I hz⟩

-- lemma lemma07 (I : set R) [is_ideal I] : is_ideal.radical I = ⋂₀ {x | is_prime_ideal x ∧ I ⊆ x} :=
-- set.ext $ λ f,
-- ⟨λ ⟨n, hf⟩ x ⟨hx, hix⟩, @@is_prime_ideal.mem_of_pow_mem _ hx $ hix hf,
--  λ hf, classical.by_contradiction $ λ hnf,
--    have h1 : ∀ n : ℕ, f^n ∉ I,
--      from λ n, nat.rec_on n
--        (λ hfz, hnf ⟨0, is_ideal.mul_left hfz⟩)
--        (λ n _ hfni, hnf ⟨n, hfni⟩),
--    let P := is_ideal.avoid_powers f I h1 in
--    have h2 : is_prime_ideal P,
--      from is_ideal.avoid_powers.is_prime_ideal f I h1,
--    have h3 : I ⊆ P,
--      from is_ideal.avoid_powers.contains f I h1,
--    have h4 : ∀ n, f^n ∉ P,
--      from is_ideal.avoid_powers.avoid_powers f I h1,
--    h4 1 $ by simpa using hf P ⟨h2, h3⟩⟩

lemma ideal.ext' {I J : ideal R} : I = J ↔ I.1 = J.1 :=
begin
  split,
  { intros H,
    rw H, },
  { intros H,
    apply ideal.ext,
    intros x,
    split,
    { intros Hx,
      exact (H ▸ Hx : x ∈ J.1), },
    { intros Hx,
      exact (H.symm ▸ Hx : x ∈ I.1), } }
end

lemma lemma08 (I : ideal R) : Spec.V I.1 = ∅ ↔ I = ⊤ :=
begin
  split,
  { intros HI,
    by_contradiction HC,
    suffices Hsuff : ∃ x, x ∈ Spec.V I.1,
      cases Hsuff with x Hx,
      rw set.eq_empty_iff_forall_not_mem at HI,
      exact HI x Hx,
    let M := find_maximal_ideal I HC,
    have MM : ideal.is_maximal M := find_maximal_ideal.is_maximal_ideal I HC,
    have MP : ideal.is_prime M := ideal.is_maximal.is_prime MM,
    use [⟨M, MP⟩],
    exact (find_maximal_ideal.contains I HC), },
  { intros HI,
    rw [HI, set.eq_empty_iff_forall_not_mem],
    rintros ⟨J, PJ⟩ HnJ,
    have HTJ : ⊤ ⊆ J := HnJ,
    have HJT : J ⊆ ⊤ := λ x Hx, trivial,
    have HJ : J = ⊤ := ideal.ext'.2 (set.eq_of_subset_of_subset HJT HTJ),
    exact PJ.1 HJ, }
end

-- lemma lemma08 (I : set R) [is_ideal I] : Spec.V I = ∅ ↔ I = set.univ :=
-- ⟨λ h, set.eq_univ_of_forall $ classical.by_contradiction $ λ hn,
--    let ⟨f, hf⟩ := not_forall.1 hn in
--    have h1 : is_proper_ideal I,
--      from ⟨λ hi, by rw set.eq_univ_iff_forall at hi; cc⟩,
--    suffices ∃ x, x ∈ Spec.V I,
--      by rw [set.eq_empty_iff_forall_not_mem] at h; cases this with x hx; exact h x hx,
--    ⟨⟨@is_ideal.find_maximal_ideal R _ I h1,
--     (@is_ideal.find_maximal_ideal.is_maximal_ideal R _ I h1).to_is_prime_ideal⟩,
--     @is_ideal.find_maximal_ideal.contains R _ I h1⟩,
--  λ h, set.eq_empty_of_subset_empty $ λ z hz,
--    @is_proper_ideal.ne_univ R _ z.1 z.2.1 $
--    set.eq_univ_of_univ_subset $ h ▸ hz⟩

-- lemma lemma09 (I J : set R) [is_ideal I] [is_ideal J] : Spec.V I ∪ Spec.V J = Spec.V (I ∩ J) :=
-- have h1 : generate I = I,
--   from set.eq_of_subset_of_subset
--     (λ z hz, hz I $ set.subset.refl I)
--     (subset_generate I),
-- have h2 : generate J = J,
--   from set.eq_of_subset_of_subset
--     (λ z hz, hz J $ set.subset.refl J)
--     (subset_generate J),
-- have h3 : Spec.V (generate I ∩ generate J) = Spec.V I ∪ Spec.V J,
--   from set.ext (Zariski._match_6 R _ _ I rfl J rfl), --hack level ≥ 9000
-- by rw [← h3, h1, h2]

-- -- we don't even need the fact that they are ideals
-- lemma lemma10 (SS : set (set R)) : ⋂₀ (Spec.V '' SS) = Spec.V ⋃₀ SS :=
-- set.ext $ λ x,
-- ⟨λ hx f ⟨I, his, hfi⟩, hx _ ⟨I, his, rfl⟩ hfi,
--  λ hx S ⟨I, his, hi⟩, hi ▸ λ f hfi, hx ⟨I, his, hfi⟩⟩

-- lemma lemma11a (f : R) : Spec.D' f ∪ Spec.V' f = set.univ :=
-- by finish [set.ext_iff]

-- lemma lemma11b (f : R) : Spec.D' f ∩ Spec.V' f = ∅ :=
-- by finish [set.ext_iff]

-- lemma lemma12 (f : R) : Spec.D' f = ∅ ↔ ∃ n : ℕ, f^n = 0 :=
-- ⟨λ h, classical.by_contradiction $ λ hf,
--    have h1 : ∀ (n : ℕ), f ^ n ∉ ({0} : set R),
--      from λ n hfn, not_exists.1 hf n $ set.mem_singleton_iff.1 hfn,
--    let x := is_ideal.avoid_powers f {0} h1 in
--    have h2 : is_prime_ideal x,
--      from is_ideal.avoid_powers.is_prime_ideal f {0} h1,
--    have h3 : ∀ n, f^n ∉ x,
--      from is_ideal.avoid_powers.avoid_powers f {0} h1,
--    have h4 : f ∉ x,
--      by simpa using h3 1,
--    set.eq_empty_iff_forall_not_mem.1 h ⟨x, h2⟩ h4,
--  λ ⟨n, hfn⟩, set.eq_empty_of_subset_empty $
--    λ x hx, hx $ @@is_prime_ideal.mem_of_pow_mem _ x.2
--    (set.mem_of_eq_of_mem hfn $
--     @@is_ideal.zero _ x.1 x.2.1.1)⟩

-- -- slightly modified
-- lemma lemma13 (f g u v : R) (hf : f = g * u) (hg : g = f * v)
--   (huv : u * v = 1) : Spec.D' f = Spec.D' g :=
-- set.ext $ λ x, not_iff_not.2
-- ⟨assume hfx : f ∈ x.val,
--    have h1 : g * u ∈ x.val,
--      from set.mem_of_eq_of_mem hf.symm hfx,
--    or.cases_on
--      (@@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 h1)
--      id (λ hu, false.elim $
--        @@is_proper_ideal.not_mem_of_mul_right_one _ x.2.1 huv hu),
--  assume hgx : g ∈ x.val,
--    have h1 : f * v ∈ x.val,
--      from set.mem_of_eq_of_mem hg.symm hgx,
--    or.cases_on
--      (@@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 h1)
--      id (λ hv, false.elim $
--        @@is_proper_ideal.not_mem_of_mul_left_one _ x.2.1 huv hv),⟩

-- -- people need to stop abstracting things by existentials
-- lemma lemma14 (f : R) (I : set R) [is_ideal I] (hfi : f ∈ I) :
--   Spec.D' f ∩ Spec.V I = ∅ :=
-- set.eq_empty_of_subset_empty $ λ z ⟨hzf, hzi⟩, hzf $ hzi hfi

-- If f,g ∈ R, then D(fg) = D(f) ∩ D(g).

lemma lemma15.aux (f g : R) : Spec.V' (f * g) = Spec.V' f ∪ Spec.V' g :=
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

lemma lemma15 (f g : R) : Spec.D' (f * g) = Spec.D' f ∩ Spec.D' g :=
begin
  unfold Spec.D',
  rw lemma15.aux,
  rw set.compl_union,
end


-- ⟨λ hx, ⟨λ hfx, hx $ @@is_ideal.mul_right _ x.2.1.1 hfx,
--    λ hgx, hx $ @@is_ideal.mul_left _ x.2.1.1 hgx⟩,
--  λ ⟨hfx, hgx⟩ hx, or.cases_on
--    (@@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 hx)
--    hfx hgx⟩

-- lemma lemma16 (F : set R) : ⋃₀ ((Spec.D') '' F) = -Spec.V F :=
-- set.ext $ λ x,
-- ⟨λ ⟨S, ⟨f, hff, hfs⟩, hx⟩ h,
--    have h1 : x ∈ Spec.D' f, by rwa ← hfs at hx,
--    h1 $ h hff,
--  λ hx, let ⟨f, hf⟩ := not_forall.1 hx in
--    let ⟨hff, hfx⟩ := not_imp.1 hf in
--    ⟨_, ⟨f, hff, rfl⟩, hfx⟩⟩

-- lemma lemma17 (f : R) (hf : Spec.D' f = set.univ) : ∃ g, f * g = 1 :=
-- have h1 : Spec.V' f = ∅,
--   from set.eq_empty_of_subset_empty $
--     λ x hx, by rw [set.eq_univ_iff_forall] at hf; specialize hf x; exact hf hx,
-- have h2 : Spec.V {f} = Spec.V' f,
--   by simp [Spec.V, Spec.V'],
-- have h3 : _,
--   from @lemma05 R _ {f},
-- have h4 : _,
--   from @lemma08 R _ (span {f}) is_ideal_span,
-- have h5 : _,
--   from (set.eq_univ_iff_forall.1 $ h4.1 $ h3.trans $ h2.trans h1) 1,
-- begin
--   rw span_singleton at h5,
--   cases h5 with g hg,
--   existsi g,
--   rw mul_comm,
--   exact hg
-- end

-- -- corollary of 14

-- lemma cor_to_14 (T : set R) (U : set (X R)) (HT : Spec.V T = -U) (P : X R) (HPU : P ∈ U) :
--   ∃ h : R, P ∈ Spec.D' h ∧ Spec.D' h ⊆ U :=
-- have h1 : P ∉ Spec.V T, by rw HT; simp [HPU],
-- let ⟨h, h2, h3⟩ := set.not_subset.1 h1 in
-- ⟨h, h3, λ f hf, have h3 : f ∉ Spec.V T, from λ h4, hf $ h4 h2, by rw HT at h3; simpa using h3⟩

end tag00E0