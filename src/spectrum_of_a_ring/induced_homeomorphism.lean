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

local attribute [instance] classical.prop_decidable

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
: (ideal.map h I : ideal Rf) = ⊥ :=
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

lemma localisation_map_ideal.eq (I : ideal R) [PI : ideal.is_prime I] 
: ideal.map h I = localisation_map_ideal I :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  apply le_antisymm,
  { have Hgen : h '' I ⊆ localisation_map_ideal I,
      intros x Hx,
      use [x, Hx, 1],
      simp,
    replace Hgen := ideal.span_mono Hgen,
    rw ideal.span_eq at Hgen,
    exact Hgen, },
  { intros x Hx,
    rcases Hx with ⟨y, ⟨z, ⟨HzI, Hzy⟩⟩, ⟨r, Hr⟩⟩,
    rw [Hr, ←Hzy],
    exact ideal.mul_mem_right _ (ideal.mem_map_of_mem HzI), }
end

lemma localisation_map_ideal.not_top (I : ideal R) [PI : ideal.is_prime I] 
(Hfn : ∀ fn, (fn ∈ powers f) → fn ∉ I)
: ideal.map h I ≠ ⊤ :=
begin
  have HL' := HL,
  rcases HL' with ⟨Hinv, Hden, Hker⟩,
  intros HC,
  rw localisation_map_ideal.eq at HC,
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
  rw Hker at Hz,
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
    rw Hker at Hz2,
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
    rcases (Hden x) with ⟨⟨s₁, r₁⟩, H1⟩,
    rcases (Hden y) with ⟨⟨s₂, r₂⟩, H2⟩,
    rcases (Hden (x * y)) with ⟨⟨s₃, r₃⟩, H3⟩,
    simp at H1,
    simp at H2,
    simp at H3,
    -- x ∈ I → h x ∈ ideal.map h I
    -- h x ∉ ideal.map h I → x ∉ I
    have Hzero : h (s₁ * s₂ * r₃ - s₃ * r₁ * r₂) = 0,
      rw (is_ring_hom.map_sub h),
      repeat { rw (is_ring_hom.map_mul h),},
      rw [←H1, ←H2, ←H3],
      ring,
    replace Hzero : (s₁ * s₂ * r₃ - s₃ * r₁ * r₂ : R) ∈ ker h := Hzero,
    rw Hker at Hzero,
    rcases Hzero with ⟨⟨⟨k, t⟩, Hzero⟩, Hk⟩,
    simp at Hzero,
    simp only [ann_aux] at Hk,
    rw Hk at Hzero,
    have HI : (0 : R) ∈ I, 
      simp,
    rw ←Hzero at HI,
    replace HI := PI.2 HI,
    cases HI,
    { -- R/I
      rw ←(submodule.quotient.eq I) at HI,
      -- φ : Rf → R/I surjective. (because R → Rf → R/I surjective)
      -- First, well defined....
      -- We show ker φ = h(I)Rf
      -- Isomorphism Rf/h(I)Rf and R/I
      -- Integral domain iso.
      -- h(I)Rf prime.
      have : inverts_data (powers f) (ideal.quotient.mk I),
        intros s,
        rcases (classical.indefinite_description _ (Hinv s)) with ⟨w, Hw⟩,
       },
    { sorry, } }
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
