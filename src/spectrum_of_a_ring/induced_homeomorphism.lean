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

def localisation_map_ideal (I : ideal R) : ideal Rf :=
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

-- Localisation map preserves primes.

lemma localisation_map_ideal.is_prime (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: ideal.is_prime (localisation_map_ideal I) :=
begin
  constructor,
  { intros HC,
    rw ideal.eq_top_iff_one at HC,
    have HC' := HC,
    rcases HC with ⟨a, ⟨Ha, ⟨r, Hone⟩⟩⟩,
    rcases Ha with ⟨v, ⟨Hv, Ha⟩⟩,
    rcases HL with ⟨Hinv, Hden, Hker⟩,
    rcases (Hden r) with ⟨⟨fn, l⟩, Hl⟩,
    rcases (Hinv fn) with ⟨hfninv, Hfn⟩,
    simp at Hl,

    rw ←Hfn at HC',
    rcases HC' with ⟨b, ⟨Hb, ⟨t, Hy⟩⟩⟩,
    rcases Hb with ⟨w, ⟨Hw, Hb⟩⟩,
    rcases (Hden t) with ⟨⟨fm, k⟩, Hk⟩,
    rcases (Hinv fm) with ⟨hfminv, Hfm⟩,
    simp at Hk,
    
    apply PI.1,
    rw ideal.eq_top_iff_one,
    sorry,
    --ideal.eq_top_of_unit_mem, 
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
