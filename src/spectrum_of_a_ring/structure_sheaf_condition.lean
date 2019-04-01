import ring_theory.localization
import algebra.pi_instances
import linear_algebra.linear_combination
import preliminaries.localisation

import tactic.find

universes u v w

local attribute [instance] classical.prop_decidable

open localization_alt

-- This is now : mem_span_iff_lc

lemma finsum_of_mem_span 
{α : Type u} {β : Type v} [comm_ring α] [add_comm_group β] [module α β]
{S : finset β} {x : β} 
: x ∈ submodule.span α S.to_set → ∃ r : β → α, x = finset.sum S (λ y, r y • y) :=
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
      apply Hb,
      refl,
    use [(finsupp.mem_support_iff.2 Hlbnz), Hb], },
  { intros a H₁ H₂,
    have HaS : a ∈ S := Hls H₁,
    rw (if_pos HaS),
    refl, }, 
end

-- lemma exists_sum_iff_mem_span_image_finset 
-- {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] {x : β} [module α β] 
-- {γ : Type w} [fintype γ] {f : γ → β} 
-- : x ∈ submodule.span α (set.range f) ↔ 
--   ∃ r : γ → α, x = finset.sum finset.univ (λ b, r b • f b) :=
-- begin
--   split,
--   { intros Hx,
--     --unfold ideal.span at Hx,
--     rw mem_span_iff_lc at Hx,
--     rcases Hx with ⟨l, Hls, Hlt⟩,
--     rw lc.total_apply at Hlt,
--     use (λ x, if f x ∈ l.support then l.to_fun (f x) else 0),
--     rw ←Hlt,
--     simp [finsupp.sum],
--     rw lc.mem_supported at Hls,
--     apply finset.sum_bij,
--     apply finset.sum
--     sorry, },
--   { sorry, }
-- end

#check @set.union_singleton
#check finset.coe_insert

open finset

lemma sum_pow_mem_span 
{α : Type u} {β : Type v} [comm_ring α] [add_comm_group β] [module α β]
(f r : β → α) (n : β → ℕ) {S : finset β}
: (S.sum (λ a, r a • f a)) ^ ((S.sum n) + 1) 
  ∈ submodule.span α (↑(S.image (λ a, f a ^ n a)) : set α) :=
begin
  apply finset.induction_on S,
  { simp, },
  { intros a T HanT IH,
    repeat { rw finset.sum_insert HanT, },
    rw finset.image_insert,
    rw finset.coe_insert,
    rw add_pow,
    rw submodule.mem_span_insert,
    refine ⟨_, _, IH, _⟩,
    
     }
end

section alpha_injective

#print lc

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

-- M = (Σ ni) + 1
-- (Σ (ai * fi))^M ∈ ⟨fi ^ ni⟩

-- First part of the lemma.

lemma standard_covering₁ (h : (1 : R) ∈ ideal.span (set.range f)) 
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
  have r : γ → R := sorry,
  have Hone : (1 : R) = finset.sum finset.univ (λ (b : γ), r b • f b ^ e b) := sorry,
  --
  rw Hone,
  rw finset.sum_mul,
  rw ←@finset.sum_const_zero γ _ finset.univ,
  apply finset.sum_congr rfl (λ i _, _),
  rw smul_eq_mul,
  rw mul_assoc,
  rw He i,
  rw mul_zero,
end

end alpha_injective

section beta_kernel_image_alpha

-- lemma standard_covering₂
--     (H : (1:R) ∈ span (↑(univ.image f) : set R)) (s : Π i, loc R (powers (f i))) :
--     β s = 0 ↔ ∃ r : R, α f r = s := 

end beta_kernel_image_alpha
