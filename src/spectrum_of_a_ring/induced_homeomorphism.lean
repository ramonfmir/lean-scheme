/-
  The map R → R[1/f] induces a homeomorphism Spec(R[1/f]) → D(f).

  https://stacks.math.columbia.edu/tag/00E4
-/

import topology.basic
import ring_theory.localization
import to_mathlib.localization.localization_alt
import to_mathlib.localization.localization_ideal
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.induced_continuous_map

universes u

local attribute [instance] classical.prop_decidable

open localization_alt

section homeomorphism

parameters {R : Type u} [comm_ring R] 
parameters {Rf : Type u} [comm_ring Rf] {h : R → Rf} [is_ring_hom h]
parameters {f : R} (HL : is_localization_data (powers f) h) 

def φ : Spec Rf → Spec R := Zariski.induced h

-- There is no f^n in h⁻¹(I).

include HL

lemma powers_f_not_preimage (I : ideal Rf) (PI : ideal.is_prime I)
: ∀ fn ∈ powers f, fn ∉ ideal.comap h I :=
begin
  have PIinv := @ideal.is_prime.comap _ _ _ _ h _ I PI,
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

-- Now we prove that φ is an open immersion. 

-- First, injectivity.

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
    have H := @ideal.mul_mem_left _ _ I (h fn) _ Hx,
    rw Hhr at H,
    replace H : r ∈ ideal.comap h I := H,
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
    replace H : r ∈ ideal.comap h J := H,
    rw ←Hxy at H, 
    replace H : h r ∈ I := H,
    rw ←Hhr at H,
    replace H := PI.2 H,
    cases H,
    { exfalso,
      exact HhfnI fn.1 fn.2 H, },
    { exact H, } },
end

-- Also, sends opens to opens. Some work is needed to assert this.

lemma localisation_map_ideal.not_top (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: ideal.map h I ≠ ⊤ :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  intros HC,
  rw localisation_map_ideal.eq HL at HC,
  rw ideal.eq_top_iff_one at HC,
  rcases HC with ⟨x, ⟨y, ⟨HyI, Hyx⟩⟩, ⟨r, Hr⟩⟩,
  rcases (Hden x) with ⟨⟨q, p⟩, Hpq⟩,
  simp at Hpq,
  rw ←Hyx at Hpq,
  have Hz : h (q * y - p) = 0,
    rw (is_ring_hom.map_sub h),
    rw (is_ring_hom.map_mul h),
    rw Hpq,
    simp,
  replace Hz : ↑q * y - p ∈ ker h := Hz,
  replace Hz := Hker Hz,
  rcases Hz with ⟨⟨⟨u, v⟩, Huv⟩, Hz⟩,
  simp at Hz,
  simp at Huv,
  rw Hz at Huv,
  have HzI : (0 : R) ∈ I := ideal.zero_mem I,
  rw ←Huv at HzI,
  replace HzI := PI.2 HzI,
  cases HzI,
  { have HqyI : ↑q * y ∈ I := ideal.mul_mem_left I HyI,
    have HpI := (ideal.neg_mem_iff I).1 ((ideal.add_mem_iff_left I HqyI).1 HzI), 
    rcases (Hden r) with ⟨⟨b, a⟩, Hab⟩,
    simp at Hab,
    rw Hyx at Hpq,
    have Hz2 : h (q * b - p * a) = 0,
      rw (is_ring_hom.map_sub h),
      repeat { rw (is_ring_hom.map_mul h), },
      rw [←Hab, ←Hpq],
      rw ←mul_comm r,
      rw mul_assoc,
      rw ←mul_assoc x,
      rw ←Hr,
      simp,
    replace Hz2 : ↑q * ↑b - p * a ∈ ker h := Hz2,
    replace Hz2 := Hker Hz2,
    rcases Hz2 with ⟨⟨⟨w, z⟩, Hwz⟩, Hz2⟩,
    simp at Hz2,
    simp at Hwz,
    rw Hz2 at Hwz,
    have HzI : (0 : R) ∈ I := ideal.zero_mem I,
    rw ←Hwz at HzI,
    replace HzI := PI.2 HzI,
    cases HzI with HzI HzI,
    { have HnpaI : -(p * a) ∈ I 
        := (ideal.neg_mem_iff I).2 (ideal.mul_mem_right I HpI),
      have HC := (ideal.add_mem_iff_right I HnpaI).1 HzI,
      replace HC := PI.2 HC,
      cases HC,
      { exact Hfn q q.2 HC, },
      { exact Hfn b b.2 HC, }, },
    { exact Hfn z z.2 HzI, } },
  { exact Hfn v v.2 HzI, }
end

lemma localisation_map_ideal.is_prime (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: ideal.is_prime (ideal.map h I) :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  constructor,
  { exact localisation_map_ideal.not_top I Hfn, },
  { intros x y Hxy,
    rw localisation_map_ideal.eq HL at Hxy,
    rcases Hxy with ⟨w, ⟨z, ⟨HzI, Hwz⟩⟩, ⟨r, Hr⟩⟩,
    rw ←Hwz at Hr,
    rcases (Hden r) with ⟨⟨q, p⟩,  Hpq⟩,
    rcases (Hden x) with ⟨⟨b₁, a₁⟩, Ha₁b₁⟩,
    rcases (Hden y) with ⟨⟨b₂, a₂⟩, Ha₂b₂⟩,
    simp at Hpq,
    simp at Ha₁b₁,
    simp at Ha₂b₂,
    have Hzpb₁b₂I : -(z * p * b₁ * b₂) ∈ I,
      rw mul_assoc,
      rw mul_assoc,
      rw ideal.neg_mem_iff I,
      exact ideal.mul_mem_right I HzI,
    have Hz : h (a₁ * a₂ * q - z * p * b₁ * b₂) = 0,
      rw (is_ring_hom.map_sub h),
      repeat { rw (is_ring_hom.map_mul h), },
      rw [←Hpq, ←Ha₁b₁, ←Ha₂b₂],
      rw ←mul_comm y,
      rw ←mul_assoc,
      rw mul_assoc _ x y,
      rw Hr,
      ring,
    replace Hz : a₁ * a₂ * q - z * p * b₁ * b₂ ∈ ker h := Hz,
    replace Hz := Hker Hz,
    rcases Hz with ⟨⟨⟨u, v⟩, Huv⟩, Hz⟩,
    simp at Hz,
    simp at Huv,
    rw Hz at Huv,
    have H0I : (0 : R) ∈ I := ideal.zero_mem I,
    rw ←Huv at H0I,
    replace H0I := PI.2 H0I,
    cases H0I,
    { have Ha₁a₂q := (ideal.add_mem_iff_left I Hzpb₁b₂I).1 H0I,
      replace Ha₁a₂q := PI.2 Ha₁a₂q,
      cases Ha₁a₂q with Ha₁a₂ Hq,
      { replace Ha₁a₂ := PI.2 Ha₁a₂,
        cases Ha₁a₂ with Ha₁ Ha₂,
        { left,
          replace Ha₁ := @ideal.mem_map_of_mem _ _ _ _ h _ _ _ Ha₁,
          rcases (Hinv b₁) with ⟨w₁, Hw₁⟩,
          have Hx : x = h a₁ * w₁,
            rw [←(one_mul x), ←Hw₁, ←mul_comm w₁, mul_assoc, Ha₁b₁],
            ring,
          rw Hx,
          exact ideal.mul_mem_right _ Ha₁, },
        { right,
          replace Ha₂ := @ideal.mem_map_of_mem _ _ _ _ h _ _ _ Ha₂,
          rcases (Hinv b₂) with ⟨w₂, Hw₂⟩,
          have Hy : y = h a₂ * w₂,
            rw [←(one_mul y), ←Hw₂, ←mul_comm w₂, mul_assoc, Ha₂b₂],
            ring,
          rw Hy,
          exact ideal.mul_mem_right _ Ha₂, } },
      { exfalso,
        exact Hfn q q.2 Hq, }, },
    { exfalso,
      exact Hfn v v.2 H0I, }, }
end

lemma phi_of_map (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: φ ⟨ideal.map h I, @localisation_map_ideal.is_prime I PI Hfn⟩ = ⟨I, PI⟩ :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  simp [φ, Zariski.induced],
  -- Goal : h⁻¹ (h(I)Rf) = I.
  apply le_antisymm,
  { intros z Hz,
    replace Hz : z ∈ ideal.comap h (ideal.map h I) := Hz,
    rw ideal.mem_comap at Hz,
    rw (localisation_map_ideal.eq HL I) at Hz,
    rcases Hz with ⟨w, ⟨a, ⟨HaI, Hwa⟩⟩, ⟨t, Ht⟩⟩,
    rw ←Hwa at Ht,
    rcases (Hden t) with ⟨⟨q, p⟩,  Hpq⟩,
    simp at Hpq,
    have H0 : h (z * q - a * p) = 0,
      rw (is_ring_hom.map_sub h),
      repeat { rw (is_ring_hom.map_mul h), },
      rw ←Hpq, 
      rw mul_comm _ t,
      rw ←mul_assoc,
      rw ←Ht,
      ring,
    replace H0 : z * q - a * p ∈ ker h := H0,
    replace H0 := Hker H0,
    rcases H0 with ⟨⟨⟨u, v⟩, Huv⟩, H0⟩,
    simp at H0,
    simp at Huv,
    rw H0 at Huv,
    have H0I : (0 : R) ∈ I := ideal.zero_mem I,
    rw ←Huv at H0I,
    replace H0I := PI.2 H0I,
    cases H0I,
    { have HnzpI : -(a * p) ∈ I 
        := (ideal.neg_mem_iff I).2 (ideal.mul_mem_right I HaI),
      replace H0I := (ideal.add_mem_iff_right I HnzpI).1 H0I,
      replace H0I := PI.2 H0I,
      cases H0I,
      { exact H0I, },
      { exfalso,
        exact Hfn q q.2 H0I, }, },
    { exfalso,
      exact Hfn v v.2 H0I, }, },
  { rw ←ideal.map_le_iff_le_comap,
    exact (le_refl _), }, 
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
    { intros HI x Hx,
      simp,
      apply classical.by_contradiction,
      intros HC,
      rcases Hx with ⟨r, s, Hspow, y, HyE, ⟨Hx, Hy⟩⟩,
      have Hfs : f * s ∈ powers f,
        rcases Hspow with ⟨n, Hn⟩,
        use [nat.succ n],
        rw pow_succ,
        rw Hn,
      have HnfI : f ∉ I,
        intros HCfI,
        replace HCfI : f * r ∈ I := ideal.mul_mem_right I HCfI,
        rw ←Hx at HCfI,
        exact HC HCfI,
      have HnfnI : ∀ fn, fn ∈ powers f → fn ∉ I,
        intros fn Hfn HfnI,
        rcases Hfn with ⟨n, Hfn⟩,
        rw ←Hfn at HfnI,
        exact HnfI (ideal.is_prime.mem_of_pow_mem PI n HfnI),
      simp at HI,
      let hI : Spec Rf := ⟨ideal.map h I, @localisation_map_ideal.is_prime I PI HnfnI⟩,
      replace HI := HI hI,
      have HnrI : r ∉ I,
        intros Hr,
        replace Hr : f * r ∈ I := ideal.mul_mem_left I Hr,
        rw ←Hx at Hr,
        exact (HC Hr),
      have HnhIVE : hI ∉ Spec.V E,
        intros HhI,
        simp [Spec.V] at HhI,
        have HyhI : h s * y ∈ ideal.map h I := ideal.mul_mem_left _ (HhI HyE),
        rw Hy at HyhI,
        rw (@localisation_map_ideal.eq R _ Rf _ h _ f HL I PI) at HyhI,
        rcases HyhI with ⟨w, ⟨z, ⟨HzI, Hwz⟩⟩, ⟨t, Ht⟩⟩,
        rcases (Hden t) with ⟨⟨q, p⟩, Hpq⟩,
        simp at Hpq,
        rw ←Hwz at Ht,
        have Hz : h (r * q - z * p) = 0,
          rw (is_ring_hom.map_sub h),
          repeat { rw (is_ring_hom.map_mul h), },
          rw [←Hpq, mul_comm _ t, ←mul_assoc, ←Ht],
          ring,
        replace Hz : r * q - z * p ∈ ker h := Hz,
        replace Hz := Hker Hz,
        rcases Hz with ⟨⟨⟨u, v⟩, Huv⟩, Hz⟩,
        simp at Hz,
        simp at Huv,
        rw Hz at Huv,
        have H0I : (0 : R) ∈ I := ideal.zero_mem I,
        rw ←Huv at H0I,
        replace H0I := PI.2 H0I,
        cases H0I,
        { have HnzpI : -(z * p) ∈ I 
            := (ideal.neg_mem_iff I).2 (ideal.mul_mem_right I HzI), 
          replace H0I := (ideal.add_mem_iff_right I HnzpI).1 H0I,
          replace H0I := PI.2 H0I,
          cases H0I,
          { exact (HnrI H0I), },
          { exact HnfnI q q.2 H0I, }, },
        { exact HnfnI v v.2 H0I, },
      replace HI := HI HnhIVE,
      apply HI,
      exact @phi_of_map I PI HnfnI, },
    { intros HSJinv HC,
      rcases HC with ⟨⟨J, PJ⟩, HP, HφP⟩,
      rw ←HφP at HSJinv,
      simp [φ, Zariski.induced, Spec.V, ideal.comap] at HSJinv,
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
        { exact HhfrJ, } } }, },
  { intros H,
    have Hcts : continuous φ := Zariski.induced.continuous h,
    have Hinv := Hcts _ H, 
    rw ←(set.preimage_image_eq U phi_injective),
    exact Hinv, }
end

-- Finally we show that φ(Spec(Rf)) = D(f). In particular this shows that there is
-- a homeomorphism between Spec(Rf) and D(f).

lemma phi_image_Df : φ '' Spec.univ Rf = Spec.D'(f) :=
begin
  apply set.ext,
  rintros ⟨I, PI⟩,
  split,
  { intros HI,
    rcases HI with ⟨⟨J, PJ⟩, ⟨HJ, HIJ⟩⟩,
    show f ∉ I,
    have HnhfnJ := h_powers_f_not_mem J PJ f ⟨1, by simp⟩,
    simp [φ, Zariski.induced] at HIJ,
    intros HC,
    rw ←HIJ at HC,
    rw ideal.mem_comap at HC,
    exact (HnhfnJ HC), },
  { intros HI,
    replace HI : f ∉ I := HI,
    have Hfn : ∀ fn, fn ∈ powers f → fn ∉ I,
      intros fn Hfn HC,
      rcases Hfn with ⟨n, Hfn⟩,
      rw ←Hfn at HC,
      exact HI (ideal.is_prime.mem_of_pow_mem PI n HC),
    let hI : Spec Rf := ⟨ideal.map h I, @localisation_map_ideal.is_prime I PI Hfn⟩,
    use hI,
    split,
    { trivial, },
    { exact @phi_of_map I PI Hfn, }, }
end

end homeomorphism
