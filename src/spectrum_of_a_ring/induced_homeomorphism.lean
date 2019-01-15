/-
Lemma 10.16.6. Let R be a ring. Let f∈R. The map R→Rf induces via the functoriality of Spec a homeomorphism
Spec(Rf)⟶D(f)⊂Spec(R).
The inverse is given by 𝔭↦𝔭⋅Rf.

Proof. This is a special case of Lemma 10.16.5 (=tag 00E3)
-/

import analysis.topology.topological_space analysis.topology.continuity tag00E2 localization
import Kenny_comm_alg.Zariski
import mathlib_someday.topology 

universes u

/-- tag 00E4 -/
-- note: this should be in mathlib as a structure

lemma lemma_standard_open (R : Type u) [comm_ring R] (f : R) : 
  let φ := Zariski.induced $ localization.of_comm_ring R (powers f) in
  topological_space.open_immersion' φ ∧ φ '' set.univ = Spec.D'(f) :=
⟨⟨Zariski.induced.continuous _,
  λ x y hxy, subtype.eq $ set.ext $ λ z,
    quotient.induction_on z $ λ ⟨r, s, hs⟩,
    ⟨λ hr, have h1 : _ := localization.mul_denom R _ r s hs,
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