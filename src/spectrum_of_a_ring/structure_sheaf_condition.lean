/-
  The sequene R → Π R[1/fᵢ] → Π R[1/fᵢfⱼ] is exact.

  https://stacks.math.columbia.edu/tag/00EJ
-/

import ring_theory.localization
import algebra.pi_instances
import linear_algebra.linear_combination
import preliminaries.localisation
import to_mathlib.finset_range

universes u v w

local attribute [instance] classical.prop_decidable

open localization_alt
open finset

lemma finset.sum_of_mem_span 
{α : Type u} {β : Type v} [comm_ring α] [add_comm_group β] [module α β]
{S : finset β} {x : β} 
: x ∈ submodule.span α S.to_set → 
  ∃ r : β → α, x = finset.sum S (λ y, r y • y) :=
begin
  intros Hx,
  rw mem_span_iff_lc at Hx,
  rcases Hx with ⟨l, Hls, Hlt⟩,
  rw lc.total_apply at Hlt,
  rw lc.mem_supported at Hls,
  rw ←Hlt,
  simp [finsupp.sum],
  use (λ x, if x ∈ S then l.to_fun x else 0),
  apply finset.sum_bij_ne_zero (λ x _ _, x),
  { intros a H₁ H₂,
    exact Hls H₁, },
  { intros a₁ a₂ H₁₁ H₁₂ H₂₁ H₂₂ H, 
    exact H, },
  { intros b HbS Hb,
    use b,
    erw (if_pos HbS) at Hb,
    have Hlbnz : l.to_fun b ≠ 0,
      intros HC,
      rw HC at Hb,
      rw zero_smul at Hb,
      exact (Hb rfl),
    use [(finsupp.mem_support_iff.2 Hlbnz), Hb], },
  { intros a H₁ H₂,
    have HaS : a ∈ S := Hls H₁,
    rw (if_pos HaS),
    refl, }, 
end

lemma finset.image_sum_of_mem_span
{α : Type u} {β : Type v} [comm_ring α] [comm_ring β] [module α β] 
{γ : Type w} {S : finset γ} {f : γ → β} {x : β} 
: x ∈ submodule.span α (finset.image f S).to_set → 
  ∃ r : γ → α, x = finset.sum S (λ b, r b • f b) :=
begin
  intros Hx,
  rcases (finset.sum_of_mem_span Hx) with ⟨r, Hr⟩,
  have Hz : ∀ y ∈ S, ∃ z ∈ S, f z = f y := λ y hy, ⟨y, hy, rfl⟩,
  use (λ y, if ∃ Hy : y ∈ S, y = classical.some (Hz y Hy) then r (f y) else 0),
  rw Hr,
  apply finset.sum_bij_ne_zero (λ a Ha _, classical.some (finset.mem_image.1 Ha)),
  { intros a H₁ H₂,
    rcases (classical.some_spec (finset.mem_image.1 H₁)) with ⟨Ha, Hf⟩,
    exact Ha, },
  { intros a₁ a₂ H₁₁ H₁₂ H₂₁ H₂₂ H,
    rcases (classical.some_spec (finset.mem_image.1 H₁₁)) with ⟨Ha₁, Hf₁⟩,
    rcases (classical.some_spec (finset.mem_image.1 H₂₁)) with ⟨Ha₂, Hf₂⟩,
    rw [←Hf₁, ←Hf₂],
    congr,
    exact H, },
  { intros b HbS Hb,
    have Hfb : f b ∈ finset.image f S := finset.mem_image.2 ⟨b, HbS, rfl⟩,
    have Hbeq : b = classical.some (finset.mem_image.1 Hfb),
      apply classical.by_contradiction,
      intros HC,
      replace HC := not_exists.2 (λ Hy : b ∈ S, HC),
      rw if_neg HC at Hb,
      rw zero_smul at Hb,
      exact (Hb rfl),
    have Hbex :  ∃ (Hy : b ∈ S), b = classical.some _ := ⟨HbS, Hbeq⟩,
    rw if_pos Hbex at Hb,
    use [f b, Hfb, Hb],
    exact Hbeq, },
  { intros a H₁ H₂,
    rcases (classical.some_spec (finset.mem_image.1 H₁)) with ⟨Ha, Hf⟩,
    rw [if_pos, Hf],
    use Ha,
    simp only [Hf], }
end

lemma sum_pow_mem_span_pow 
{α : Type u} {β : Type v} [comm_ring α]
(f r : β → α) (n : β → ℕ) {S : finset β}
: (S.sum (λ a, r a • f a)) ^ ((S.sum n) + 1) 
  ∈ submodule.span α (↑(S.image (λ a, f a ^ n a)) : set α) :=
begin
  apply finset.induction_on S,
  { simp, },
  { intros a T HanT IH,
    repeat { rw finset.sum_insert HanT, },
    rw [finset.image_insert, finset.coe_insert, submodule.mem_span_insert],
    have H := add_pow_sum (r a * f a) (sum T (λ a, r a • f a)) (n a) (sum T n + 1),
    rcases H with ⟨x, y, H⟩,
    have Hx := @submodule.smul_mem _ _ _ _ _ _ _ x IH,
    use [y * (r a) ^ (n a), x • sum T (λ (a : β), r a • f a) ^ (sum T n + 1), Hx],
    repeat { rw smul_eq_mul, },
    rw [add_assoc, H, add_comm, mul_pow, mul_assoc], }
end

lemma one_mem_span_pow_of_mem_span 
{α : Type u} {β : Type v} [comm_ring α] 
(f : β → α) (n : β → ℕ) {S : finset β}
(Hx : (1 : α) ∈ submodule.span α (↑(S.image f) : set α))
: (1 : α) ∈ submodule.span α (↑(S.image (λ x, f x ^ n x)) : set α) :=
begin
  rcases (finset.image_sum_of_mem_span Hx) with ⟨r, Hr⟩,
  rw [←one_pow ((S.sum n) + 1), Hr],
  apply sum_pow_mem_span_pow,
end

section alpha_injective

-- Ring R.
parameters (R : Type u) [comm_ring R] 
-- f1, ..., fn
parameters {γ : Type v} [fintype γ] {f : γ → R}
-- R[1/f1], ..., R[1/fn]
parameters {Rfs : γ → Type w} [Π i, comm_ring (Rfs i)]
-- α1 : R → R[1/f1], ...., αn → R[1/fn]
parameters {αᵢ : Π i, R → (Rfs i)} [Π i, is_ring_hom (αᵢ i)]
parameters (Hloc : Π i, is_localization (powers (f i)) (αᵢ i))

@[reducible] def α : R → Π i, Rfs i := λ r i, αᵢ i r

instance PRfs.comm_ring : comm_ring (Π i, Rfs i) :=
pi.comm_ring

instance α.is_ring_hom : is_ring_hom α :=
pi.is_ring_hom_pi αᵢ

include Hloc

-- First part of the lemma.

lemma standard_covering₁ (H : (1 : R) ∈ ideal.span (set.range f)) 
: function.injective α := 
begin
  rw ←@is_ring_hom.inj_iff_trivial_ker _ _ _ _ α α.is_ring_hom,
  intros x Hx,
  replace Hx := congr_fun Hx,
  have Hn : ∀ i, ∃ n : ℕ, f i ^ n * x = 0,
    intros i,
    replace Hx : x ∈ ker (αᵢ i) := Hx i,
    replace Hloc := Hloc i,
    rcases Hloc with ⟨Hinv, Hden, Hker⟩,
    rw Hker at Hx,
    rcases Hx with ⟨⟨⟨u, ⟨fn, ⟨n, Hfn⟩⟩⟩, Hufn⟩, Hx⟩,
    existsi n,
    rw [Hfn, ←Hx, mul_comm],
    exact Hufn,
  let e : γ → ℕ := λ i, classical.some (Hn i),
  have He : ∀ i, f i ^ e i * x = 0 := λ i, classical.some_spec (Hn i),
  rw ←one_mul x,
  -- Σ ai * (f i) = 1
  rw finset.coe_image_univ at H,
  cases finset.image_sum_of_mem_span (one_mem_span_pow_of_mem_span f e H) with r Hone,
  rw [Hone, finset.sum_mul, ←@finset.sum_const_zero γ _ finset.univ],
  apply finset.sum_congr rfl (λ i _, _),
  rw [smul_eq_mul, mul_assoc, He i, mul_zero],
end

end alpha_injective

section beta_kernel_image_alpha

-- lemma standard_covering₂
--     (H : (1:R) ∈ span (↑(univ.image f) : set R)) (s : Π i, loc R (powers (f i))) :
--     β s = 0 ↔ ∃ r : R, α f r = s := 

end beta_kernel_image_alpha
