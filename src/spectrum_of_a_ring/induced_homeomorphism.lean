/-
  The map R → R[1/f] induces a homeomorphism Spec(R[1/f]) → D(f).

  https://stacks.math.columbia.edu/tag/00E4
-/

import topology.basic
import ring_theory.localization
import preliminaries.localisation
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.induced_continuous_map

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

parameters {R : Type u} [comm_ring R] 
parameters {Rf : Type u} [comm_ring Rf] {h : R → Rf} [is_ring_hom h]
parameters {f : R} (HL : is_localization (powers f) h) 

def φ : Spec Rf → Spec R := Zariski.induced h

-- There is no f^n in h⁻¹(I).

include HL

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

-- Map from I → h(I)Rf.

lemma localisation_map_ideal (I : ideal R) : ideal Rf :=
{ carrier := { x | ∃ (y ∈ h '' I) (r : Rf), x = y * r },
  zero := -- ⟨0, ⟨I.2, is_ring_hom.map_zero h⟩⟩
    begin
      use [h 0, 0],
      exact ⟨I.2, rfl⟩,
      use 1,
      rw mul_one,
      rw ←is_ring_hom.map_zero h,
    end,
  add := 
    begin
      intros x y Hx Hy,
      rcases Hx with ⟨a, ⟨Ha, ⟨r, Hx⟩⟩⟩,
      rcases Hy with ⟨b, ⟨Hb, ⟨t, Hy⟩⟩⟩,
      rcases Ha with ⟨v, ⟨Hv, Ha⟩⟩,
      rcases Hb with ⟨w, ⟨Hw, Hb⟩⟩,
      rw ←Ha at Hx,
      rw ←Hb at Hy,
      rw [Hx, Hy],
      rcases HL with ⟨Hinv, Hden, Hker⟩,
      rcases (Hden r) with ⟨⟨fn, l⟩, Hl⟩,
      rcases (Hinv fn) with ⟨hfninv, Hfn⟩,
      simp at Hl,
      rw mul_comm at Hfn,
      rcases (Hden t) with ⟨⟨fm, k⟩, Hk⟩,
      rcases (Hinv fm) with ⟨hfminv, Hfm⟩,
      simp at Hk,
      rw mul_comm at Hfm,
      -- Get rid of r.
      rw ←one_mul (_ + _),
      rw ←Hfn,
      rw mul_assoc,
      rw mul_add,
      rw mul_comm _ r,
      rw ←mul_assoc _ r _,
      rw Hl,
      -- Get rid of t.
      rw ←one_mul (_ * _),
      rw ←Hfm,
      rw mul_assoc,
      rw ←mul_assoc (h _) _ _,
      rw mul_comm (h _),
      rw mul_assoc _ (h _) _,
      rw mul_add,
      rw ←mul_assoc _ _ t,
      rw add_comm,
      rw ←mul_assoc (h fm) _ _,
      rw mul_comm (h fm),
      rw mul_assoc _ _ t,
      rw Hk,
      -- Rearrange.
      repeat { rw ←is_ring_hom.map_mul h, },
      rw ←mul_assoc _ _ v,
      rw mul_assoc ↑fn,
      rw mul_comm w,
      rw ←mul_assoc ↑fn,
      rw ←is_ring_hom.map_add h,
      rw ←mul_assoc,
      rw mul_comm,
      -- Ready to prove it.
      have HyI : ↑fn * k * w + ↑fm * l * v ∈ ↑I,
        apply I.3,
        { apply I.4,
          exact Hw, },
        { apply I.4,
          exact Hv, },
      use [h (↑fn * k * w + ↑fm * l * v)],
      use [⟨↑fn * k * w + ↑fm * l * v, ⟨HyI, rfl⟩⟩],
      use [hfminv * hfninv],
    end,
  smul := 
    begin
      intros c x Hx,
      rcases Hx with ⟨a, ⟨Ha, ⟨r, Hx⟩⟩⟩,
      rcases Ha with ⟨v, ⟨Hv, Ha⟩⟩,
      rw [Hx, ←Ha],
      rw mul_comm _ r,
      unfold has_scalar.smul,
      rw mul_comm r,
      rw mul_comm c,
      rw mul_assoc,
      use [h v],
      use [⟨v, ⟨Hv, rfl⟩⟩],
      use [r * c],
    end, }



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
      replace HI : ∀ (J : ideal Rf) [PJ : ideal.is_prime J], 
        (⟨J, PJ⟩ : Spec Rf) ∈ Spec.D E → ¬φ ⟨J, PJ⟩ = ⟨I, PI⟩
        := λ J PJ, HI ⟨J, PJ⟩,
      intros x Hx,
      apply classical.by_contradiction,
      intros HC,
      simp at HC,
      rcases Hx with ⟨r, s, Hspow, y, HyE, ⟨Hx, Hy⟩⟩,
      have hI : ideal Rf := localisation_map_ideal I,
      have HI' := HI hI PI,
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

#exit

lemma lemma_standard_open (R : Type u) [comm_ring R] (f : R) : 
  let φ := Zariski.induced (localization.away R (powers f)) in
  function.injective φ ∧ φ '' set.univ = Spec.D'(f) :=
⟨⟨Zariski.induced.continuous _,
  λ x y hxy, subtype.eq $ set.ext $ λ z,
    quotient.induction_on z $ λ ⟨r, s, hs⟩,
    ⟨λ hr, 

        have h1 : _ := localization.mul_denom R _ r s hs,
       have h2 : localization.of_comm_ring R (powers f) r ∈ x.val,
         from eq.rec (@@is_ideal.mul_right _ x.2.1.1 hr) h1,
       have h3 : r ∈ (Zariski.induced (localization.of_comm_ring R (powers f)) y).1,
         from eq.rec h2 hxy,
       have h4 : localization.of_comm_ring R (powers f) r ∈ y.val,
         from h3,
       have h5 : _ := localization.mul_inv_denom R _ r s hs,
       eq.rec (@@is_ideal.mul_right _ y.2.1.1 h4) h5,
     λ hr, have h1 : _ := localization.mul_denom R _ r s hs,
       have h2 : localization.of_comm_ring R (powers f) r ∈ y.val,
         from eq.rec (@@is_ideal.mul_right _ y.2.1.1 hr) h1,
       have h3 : r ∈ (Zariski.induced (localization.of_comm_ring R (powers f)) x).1,
         from eq.rec h2 hxy.symm,
       have h4 : localization.of_comm_ring R (powers f) r ∈ x.val,
         from h3,
       have h5 : _ := localization.mul_inv_denom R _ r s hs,
       eq.rec (@@is_ideal.mul_right _ x.2.1.1 h4) h5⟩,
  λ S hs, let ⟨F, hsf⟩ := hs in
    let F' := {fr | ∃ (r) (s ∈ powers f), fr = f * r ∧ ⟦(⟨r, s, H⟩ : R × powers f)⟧ ∈ F} in
    ⟨F', set.ext $ λ z,
     ⟨λ hz ⟨x, hxs, hnz⟩, have h1 : x ∈ Spec.V F,
        from λ g, quotient.induction_on g $ λ ⟨r, s, hsg⟩ hg,
          have h2 : f * r ∈ F', from ⟨r, s, hsg, rfl, hg⟩,
          have h3 : _, from hz h2,
          have h4 : f * s ∈ powers f, from
            let ⟨n, hfns⟩ := hsg in
            ⟨nat.succ n, by rw ← hfns; refl⟩,
          have h5 : ⟦((r, ⟨s, hsg⟩) : R × powers f)⟧ = ⟦(f * r, ⟨f * s, h4⟩)⟧,
            from quotient.sound ⟨1, is_submonoid.one_mem _, by simp [mul_left_comm, mul_assoc]⟩,
          begin
            rw h5,
            rw ← localization.mul_inv_denom,
            rw ← hnz at h3,
            exact @@is_ideal.mul_right _ x.2.1.1 h3
          end,
        by rw hsf at h1; exact h1 hxs,
      λ hz g ⟨r, s, hsg, hgfr, hrs⟩,
      classical.by_contradiction $ λ hngz,
        have h1 : f ∉ z.1, by intro hn; apply hngz; rw hgfr;
          exact @@is_ideal.mul_right _ z.2.1.1 hn,
        let z' : set (localization.loc R (powers f)) :=
          {f | quotient.lift_on f
             (λ g, g.1 ∈ z.1) $ begin
               intros f1 f4 h2,
               rcases f1 with ⟨f1, f2, f3⟩,
               rcases f4 with ⟨f4, f5, f6⟩,
               rcases h2 with ⟨h2, h3, h4⟩,
               simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at h4 ⊢,
               apply propext,
               show f1 ∈ z.val ↔ f4 ∈ z.val,
               split,
               { intro h5,
                 have h6 : f5 * f1 * h2 ∈ z.val,
                 { apply @@is_ideal.mul_right _ z.2.1.1,
                   exact @@is_ideal.mul_left _ z.2.1.1 h5 },
                 rw ← h4 at h6,
                 cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ z.2 h6 with h7 h7,
                 cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ z.2 h7 with h8 h8,
                 { exfalso,
                   apply h1,
                   cases f3 with f7 f8,
                   apply @@is_prime_ideal.mem_of_pow_mem _ z.2,
                   rw ← f8 at h8,
                   exact h8 },
                 { exact h8 },
                 { exfalso,
                   apply h1,
                   cases h3 with f7 f8,
                   apply @@is_prime_ideal.mem_of_pow_mem _ z.2,
                   rw ← f8 at h7,
                   exact h7 } },
               { intro h5,
                 have h6 : f2 * f4 * h2 ∈ z.val,
                 { apply @@is_ideal.mul_right _ z.2.1.1,
                   exact @@is_ideal.mul_left _ z.2.1.1 h5 },
                 rw h4 at h6,
                 cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ z.2 h6 with h7 h7,
                 cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ z.2 h7 with h8 h8,
                 { exfalso,
                   apply h1,
                   cases f6 with f7 f8,
                   apply @@is_prime_ideal.mem_of_pow_mem _ z.2,
                   rw ← f8 at h8,
                   exact h8 },
                 { exact h8 },
                 { exfalso,
                   apply h1,
                   cases h3 with f7 f8,
                   apply @@is_prime_ideal.mem_of_pow_mem _ z.2,
                   rw ← f8 at h7,
                   exact h7 } }
             end} in
        have h2 : is_prime_ideal z', from
        { zero_ := by simp [localization.zero_frac]; exact @@is_ideal.zero _ _ z.2.1.1,
          add_  := λ f1 f2, quotient.induction_on₂ f1 f2 $
            λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ hg1 hg2,
            by simp [localization.mk_eq, localization.add_frac] at hg1 hg2 ⊢;
            exact @@is_ideal.add _ z.2.1.1
              (@@is_ideal.mul_left _ z.2.1.1 hg2)
              (@@is_ideal.mul_left _ z.2.1.1 hg1),
          smul  := λ c x, quotient.induction_on₂ c x $
            λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ hg2,
            by simp [localization.mk_eq, localization.mul_frac] at hg2 ⊢;
            exact @@is_ideal.mul_left _ z.2.1.1 hg2,
          ne_univ := λ h2, h1 $ by rw set.eq_univ_iff_forall at h2;
            exact h2 (localization.of_comm_ring _ _ f),
          mem_or_mem_of_mul_mem := λ f1 f2, quotient.induction_on₂ f1 f2 $
            λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ hg2,
            by simp [localization.mk_eq, localization.mul_frac] at hg2 ⊢;
            exact @@is_prime_ideal.mem_or_mem_of_mul_mem _ z.2 hg2 },
        have h3 : (⟨z', h2⟩ : X (localization.loc R (powers f))) ∉ Spec.V F,
          from λ h3, hngz $ by rw hgfr; exact @@is_ideal.mul_left _ z.2.1.1 (h3 hrs),
      hz ⟨⟨z', h2⟩, by rw hsf at h3; exact classical.by_contradiction h3,
        begin
          apply subtype.eq,
          apply set.ext,
          intro r1,
          simp [Zariski.induced, localization.of_comm_ring]
        end⟩⟩⟩⟩,
 set.ext $ λ x,
 ⟨λ ⟨y, _, hyx⟩ hfx, have h1 : localization.of_comm_ring R (powers f) f ∈ y.val,
    by rwa ← hyx at hfx,
    @@is_prime_ideal.one_not_mem _ y.1 y.2 $
    begin
      rw ← @localization.div_self _ _ (powers f) _ f ⟨1, by simp⟩,
      unfold localization.mk,
      rw ← localization.mul_inv_denom _ (powers f),
      exact @@is_ideal.mul_right _ y.2.1.1 h1
    end,
  λ hx, let y : set (localization.loc R (powers f)) :=
    {f | quotient.lift_on f
       (λ g, g.1 ∈ x.1) $ begin
         intros f1 f4 h2,
         rcases f1 with ⟨f1, f2, f3⟩,
         rcases f4 with ⟨f4, f5, f6⟩,
         rcases h2 with ⟨h2, h3, h4⟩,
         simp [-sub_eq_add_neg, sub_mul, sub_eq_zero] at h4 ⊢,
         apply propext,
         show f1 ∈ x.val ↔ f4 ∈ x.val,
         split,
         { intro h5,
           have h6 : f5 * f1 * h2 ∈ x.val,
           { apply @@is_ideal.mul_right _ x.2.1.1,
             exact @@is_ideal.mul_left _ x.2.1.1 h5 },
           rw ← h4 at h6,
           cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 h6 with h7 h7,
           cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 h7 with h8 h8,
           { exfalso,
             apply hx,
             cases f3 with f7 f8,
             apply @@is_prime_ideal.mem_of_pow_mem _ x.2,
             rw ← f8 at h8,
             exact h8 },
           { exact h8 },
           { exfalso,
             apply hx,
             cases h3 with f7 f8,
             apply @@is_prime_ideal.mem_of_pow_mem _ x.2,
             rw ← f8 at h7,
             exact h7 } },
         { intro h5,
           have h6 : f2 * f4 * h2 ∈ x.val,
           { apply @@is_ideal.mul_right _ x.2.1.1,
             exact @@is_ideal.mul_left _ x.2.1.1 h5 },
           rw h4 at h6,
           cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 h6 with h7 h7,
           cases @@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 h7 with h8 h8,
           { exfalso,
             apply hx,
             cases f6 with f7 f8,
             apply @@is_prime_ideal.mem_of_pow_mem _ x.2,
             rw ← f8 at h8,
             exact h8 },
           { exact h8 },
           { exfalso,
             apply hx,
             cases h3 with f7 f8,
             apply @@is_prime_ideal.mem_of_pow_mem _ x.2,
             rw ← f8 at h7,
             exact h7 } }
       end} in
  have h2 : is_prime_ideal y, from
  { zero_ := by simp [localization.zero_frac]; exact @@is_ideal.zero _ _ x.2.1.1,
    add_  := λ f1 f2, quotient.induction_on₂ f1 f2 $
      λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ hg1 hg2,
      by simp [localization.mk_eq, localization.add_frac] at hg1 hg2 ⊢;
      exact @@is_ideal.add _ x.2.1.1
        (@@is_ideal.mul_left _ x.2.1.1 hg2)
        (@@is_ideal.mul_left _ x.2.1.1 hg1),
    smul  := λ c z, quotient.induction_on₂ c z $
      λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ hg2,
      by simp [localization.mk_eq, localization.mul_frac] at hg2 ⊢;
      exact @@is_ideal.mul_left _ x.2.1.1 hg2,
    ne_univ := λ h2, hx $ by rw set.eq_univ_iff_forall at h2;
      exact h2 (localization.of_comm_ring _ _ f),
    mem_or_mem_of_mul_mem := λ f1 f2, quotient.induction_on₂ f1 f2 $
      λ ⟨r1, s1, hs1⟩ ⟨r2, s2, hs2⟩ hg2,
      by simp [localization.mk_eq, localization.mul_frac] at hg2 ⊢;
      exact @@is_prime_ideal.mem_or_mem_of_mul_mem _ x.2 hg2 },
 ⟨⟨y, h2⟩, trivial, subtype.eq $ set.ext $ λ r1, by simp [Zariski.induced, localization.of_comm_ring]⟩⟩⟩