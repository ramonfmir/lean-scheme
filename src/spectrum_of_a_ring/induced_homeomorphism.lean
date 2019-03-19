/-
  The map R → R[1/f] induces a homeomorphism Spec(R[1/f]) → D(f).

  https://stacks.math.columbia.edu/tag/00E4
-/

import topology.basic
import ring_theory.localization
import preliminaries.localisation
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.induced_continuous_map
import tactic.find

universes u

--section move

-- TODO : should be somewhere else.

-- lemma ideal.mem_succ_pow {R : Type u} [comm_ring R] (I : ideal R) :
-- ∀ x : R, (x ∈ I → ∀ n : ℕ, x ^ nat.succ n ∈ I) :=
-- begin
--   intros x Hx n,
--   induction n with n Hn,
--   { simp [Hx], },
--   { rw pow_succ,
--     apply ideal.mul_mem_left I Hn, }
-- end

-- end move

open localization_alt

section homeomorphism

#check nonempty 
#check subsingleton
#print subsingleton

parameters {R : Type u} [comm_ring R] 
parameters {Rf : Type u} [comm_ring Rf] {h : R → Rf} [is_ring_hom h]
parameters {f : R} (HL : is_localization (powers f) h) 

def φ : Spec Rf → Spec R := Zariski.induced h

-- There is no f^n in h⁻¹(I).

include HL

#check submodule.span_induction

lemma powers_f_not_preimage (I : ideal Rf) (PI : ideal.is_prime I)
: ∀ fn ∈ powers f, fn ∉ ideal.preimage h I :=
begin
  have PIinv := ideal.is_prime.preimage h I PI,
  intros fn Hfn HC,
  replace HC : h fn ∈ I := HC,
  have Hinvfn := HL.1 ⟨fn, Hfn⟩,
  rcases Hinvfn with ⟨s, Hs⟩,
  simp at Hs,
  have Hone := @ideal.mul_mem_right _ _ I _ s HC,
  rw Hs at Hone,
  apply PI.1,
  exact (ideal.eq_top_iff_one _).2 Hone,
end

lemma h_powers_f_not_mem (I : ideal Rf) (PI : ideal.is_prime I)
: ∀ fn ∈ powers f, h fn ∉ I :=
λ fn Hfn HC, (powers_f_not_preimage I PI) fn Hfn HC

lemma phi_injective : function.injective φ :=
begin
  intros x y Hxy,
  rcases x with ⟨I, PI⟩,
  rcases y with ⟨J, PJ⟩,
  simp [φ, Zariski.induced] at Hxy,
  have HhfnI := h_powers_f_not_mem I PI,
  have HhfnJ := h_powers_f_not_mem J PJ,
  rcases HL with ⟨Hinv, Hden, Hker⟩,
  -- TODO : very similar branches.
  simp,
  apply ideal.ext,
  intros x,
  split,
  { intros Hx,
    have Hdenx := Hden x,
    rcases Hdenx with ⟨⟨fn, r⟩, Hhr⟩,
    simp at Hhr,
    have Hinvfn := Hinv fn,
    rcases Hinvfn with ⟨s, Hfn⟩,
    have H := @ideal.mul_mem_left _ _ I (h fn) _ Hx,
    rw Hhr at H,
    replace H : r ∈ ideal.preimage h I := H,
    rw Hxy at H, 
    replace H : h r ∈ J := H,
    rw ←Hhr at H,
    replace H := PJ.2 H,
    cases H,
    { exfalso,
      exact HhfnJ fn.1 fn.2 H, },
    { exact H, } },
  { intros Hx,
    have Hdenx := Hden x,
    rcases Hdenx with ⟨⟨fn, r⟩, Hhr⟩,
    simp at Hhr,
    have Hinvfn := Hinv fn,
    rcases Hinvfn with ⟨s, Hfn⟩,
    have H := @ideal.mul_mem_left _ _ J (h fn) _ Hx,
    rw Hhr at H,
    replace H : r ∈ ideal.preimage h J := H,
    rw ←Hxy at H, 
    replace H : h r ∈ I := H,
    rw ←Hhr at H,
    replace H := PI.2 H,
    cases H,
    { exfalso,
      exact HhfnI fn.1 fn.2 H, },
    { exact H, } },
end

-- Random stuff.

lemma ring_hom.pow {A : Type u} [comm_ring A] {B : Type u} [comm_ring B]
(m : A → B) [is_ring_hom m] (a : A)
: ∀ (n : ℕ), m (a ^ n) = (m a) ^ n :=
begin
  intros n,
  induction n,
  { simp,
    exact is_ring_hom.map_one m, },
  { rw pow_succ,
    rw pow_succ,
    rw is_ring_hom.map_mul m,
    rw n_ih, }
end

lemma localization.zero (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : (0 : R) ∈ powers f)
: (ideal.map h I : ideal Rf) = ⊥  :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  apply ideal.ext,
  intros x,
  split,
  swap,
  { intros H,
    simp at H,
    rw H,
    rw ←is_ring_hom.map_zero h,
    apply ideal.mem_map_of_mem,
    simp, },
  { intros Hx,
    rcases (Hden x) with ⟨⟨a, b⟩, Hab⟩,
    simp at Hab,
    rcases (Hinv a) with ⟨w, Hw⟩,
    have Hall : ∀ (y : R), y ∈ submonoid_ann (powers f),
      intros y,
      simp [submonoid_ann, set.range, ann_aux],
      use [⟨y, ⟨0, Hfn⟩⟩],
      simp,
    have Htop : submonoid_ann (powers f) = ⊤,
      apply ideal.ext,
      intros x,
      split,
      { intros Hx,
        cases Hx,
        unfold ann_aux at Hx_w, },
      { intros Hx,
        exact (Hall x), },
    unfold ker at Hker,
    rw Htop at Hker,
    have Hx : (1 : R) ∈ (⊤ : ideal R),
      trivial,
    rw ←Hker at Hx,
    replace Hx : h 1 = 0 := Hx,
    rw (is_ring_hom.map_one h) at Hx,
    rw ←mul_one x,
    rw Hx,
    simp, },
end

#check function.surjective_iff_has_right_inverse
#check ideal.map

lemma lll (Hz : (0 : R) ∉ powers f) : ∀ a, h a = 1 → a = 1 :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  -- have Hz : (0 : R) ∉ powers f,
  --   intros H,
  --   have := Hfn 0 H,
  --   apply this,
  --   simp,
  intros a Ha,
  rw ←is_ring_hom.map_one h at Ha,
  have : h a - h 1 = 0,
    rw Ha,
    simp,
  rw ←(is_ring_hom.map_sub h) at this,
  have : a - 1 ∈ ker h := this,
  rw Hker at this,
  cases this with w Hw,
  cases w with w Huv,
  cases w with u v,
  simp at Huv,
  simp at Hw,
  rw Hw at Huv,
end

lemma localisation_map_ideal.not_top (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: ideal.map h I ≠ ⊤ :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  intros HI,
  have : (0 : R) ∉ powers f,
    intros H,
    have := Hfn 0 H,
    apply this,
    simp,
  
  rcases (Hden 1) with ⟨⟨a, b⟩, Hab⟩,
  simp at Hab,
  have : h a - h b = 0,
    rw Hab,
    simp,
  rw ←(is_ring_hom.map_sub h) at this,
  have : ↑a - b ∈ ker h := this,
  rw Hker at this,
  cases this with w Hw,
  cases w with w Huv,
  cases w with u v,
  simp at Huv,
  simp at Hw,
  rw Hw at Huv,

  -- h(1) ∈ h(I)R[1/S]
  -- 
  -- x - y = z
  -- z * f^n = 0
  -- f^n * (x - y) = 0
  -- f^n * x = f^n * y

    -- assume not zero ring?????
  --simp [ideal.map, ideal.span, submodule.span] at Hone, 
end

#check @submodule.span_induction

lemma localisation_map_ideal.is_prime (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: ideal.is_prime (ideal.map h I) :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  constructor,
  { intros HC,
    rw ideal.eq_top_iff_one at HC,
    apply PI.1,
    rw ideal.eq_top_iff_one,
    suffices Hsuff : 1 ∈ h '' I,
      cases Hsuff with a Ha,
      cases Ha with Ha Hb,

    simp [ideal.map, ideal.span] at HC,
    have := @submodule.span_induction _ _ _ _ _ _ _ (λ y, y ∈ h '' I) HC,
    eapply submodule.span_induction HC,
    
    -- a/f^n, ...
    },
  { sorry, }
end

lemma phi_opens : ∀ U : set (Spec Rf), is_open U ↔ is_open (φ '' U) :=
begin
  intros U,
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  split,
  { intros OU,
    cases OU with E HE,
    have HU : U = Spec.D E,
      simp [Spec.D],
      rw HE, 
      rw set.compl_compl,
    rw HU,
    let S := { x | ∃ (r) (s ∈ powers f) (y ∈ E), x = f * r ∧ h s * y = h r },
    existsi S,
    apply set.ext,
    rintros ⟨I, PI⟩,
    split,
    swap,
    { intros HI,
      simp at HI,
      replace HI : ∀ (J : ideal Rf) (PJ : ideal.is_prime J), 
        (⟨J, PJ⟩ : Spec Rf) ∈ -Spec.V E → ¬φ ⟨J, PJ⟩ = ⟨I, PI⟩
        := λ J PJ, HI ⟨J, PJ⟩,
      have HI' : ∀ (J : ideal Rf) [PJ : ideal.is_prime J], 
        φ ⟨J, PJ⟩ = ⟨I, PI⟩ → (⟨J, PJ⟩ : Spec Rf) ∈ Spec.V E := sorry,

      intros x Hx,
      apply classical.by_contradiction,
      intros HC,
      simp at HC,
      
       

      -- rcases Hx with ⟨r, s, Hspow, y, HyE, ⟨Hx, Hy⟩⟩,
      -- have hI : ideal Rf := localisation_map_ideal I,
      -- have HI' := HI hI PI,
      sorry,
      },


    { intros HSJinv HC,
      rcases HC with ⟨⟨J, PJ⟩, HP, HφP⟩,
      rw ←HφP at HSJinv,
      simp [φ, Zariski.induced, Spec.V, ideal.preimage] at HSJinv,
      replace HSJinv : S ⊆ h ⁻¹' J.1 := HSJinv,
      apply HP,
      intros x Hx,
      rcases (Hden x) with ⟨⟨fn, r⟩, Hhr⟩,
      simp at Hhr,
      rcases (Hinv fn) with ⟨s, Hfn⟩,
      have HfrS : f * r ∈ S := ⟨r, fn.1, fn.2, x, Hx, ⟨rfl, Hhr⟩⟩,
      replace HfrS := HSJinv HfrS,
      have HhfrJ : h (f * r) ∈ J := HfrS,
      rw is_ring_hom.map_mul h at HhfrJ,
      replace HhfrJ := PJ.2 HhfrJ, 
      have Hfpow : f ∈ powers f := ⟨1, by simp⟩,
      have : h f ∉ J := h_powers_f_not_mem J PJ f Hfpow,
      have : h fn ∉ J := h_powers_f_not_mem J PJ fn fn.2,
      cases HhfrJ,
      { contradiction, },
      { rw ←Hhr at HhfrJ,
        replace HhfrJ := PJ.2 HhfrJ,
        cases HhfrJ,
        { contradiction, },
        { exact HhfrJ, } } },
     },
  { sorry, }
end

lemma phi_image_Df : φ '' Spec.univ Rf = Spec.D'(f) :=
begin
  sorry,
end

end homeomorphism
