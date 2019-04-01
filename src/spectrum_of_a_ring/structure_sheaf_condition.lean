import ring_theory.localization
import algebra.pi_instances
import linear_algebra.linear_combination
import preliminaries.localisation

import tactic.find

universes u v w

local attribute [instance] classical.prop_decidable

open localization_alt

-- This is now : mem_span_iff_lc

lemma finset.sum_of_mem_span 
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

open finset

@[simp] lemma finset.range_not_mem : ∀ n : ℕ, n ∉ range n :=
λ n Hn, (lt_irrefl n) (finset.mem_range.1 Hn)

lemma finset.sum_range_eq {α : Type u} [comm_ring α] {f g : ℕ → α} 
: ∀ n, (∀ m, m < n → f m = g m) → sum (range n) f = sum (range n) g :=
begin
  intros n Hn,
  induction n with n IH,
  { simp, },
  { repeat { rw finset.range_succ, },
    repeat { rw finset.sum_insert; try { apply finset.range_not_mem _, } },
    rw Hn n (nat.lt_succ_self n),
    rw IH,
    intros m Hm,
    exact Hn m (nat.lt_succ_of_lt Hm), }
end

lemma finset.sum_range_add {α : Type u} [comm_ring α] (f : ℕ → α) 
: ∀ n m : ℕ, sum (range (n + m)) f = sum (range n) f + sum (range m) (λ i, f (i + n)) :=
begin
  intros n m,
  revert n,
  induction m with m IH,
  { simp, },
  { intros n,
    rw nat.add_succ,
    repeat { rw finset.range_succ, },
    repeat { rw finset.sum_insert; try { apply finset.range_not_mem _, } },
    rw IH n,
    simp, }
end

private lemma sum_pow_mem_span.aux
{α : Type u} [comm_ring α] 
: ∀ (a b : α), ∀ (n m : ℕ), ∃ (x y : α), 
  (a + b) ^ (n + m) = x * (b ^ m) + y * (a ^ n) :=
begin
  intros a b n m,
  rw add_pow,
  use [sum (range n) (λ i, a ^ i * b ^ (n - i) * (choose (n + m) i))],
  use [sum (range (nat.succ m)) (λ i, a ^ i * b ^ (m - i) * (choose (n + m) (i + n)))],
  repeat { rw finset.sum_mul, },
  repeat { rw finset.range_succ, },
  repeat { rw finset.sum_insert; try { apply finset.range_not_mem, }, },
  simp,
  congr,
  { rw [pow_add, mul_comm], },
  rw finset.sum_range_add,
  congr' 1,
  { apply finset.sum_range_eq,
    intros z Hz,
    rw [mul_assoc _ _ (b ^ m), mul_comm _ (b ^ m), ←mul_assoc _ (b ^ m) _],
    rw [mul_assoc _ _ (b ^ m), ←pow_add, add_comm n _, add_comm (n - z) _], 
    rw [←nat.add_sub_assoc],
    exact nat.le_of_lt Hz, },
  { apply finset.sum_range_eq,
    intros z Hz,
    rw [mul_assoc _ _ (a ^ n), mul_comm _ (a ^ n), ←mul_assoc _ (a ^ n) _],
    rw [mul_assoc _ _ (a ^ n), mul_comm _ (a ^ n), ←mul_assoc _ (a ^ n) _],
    rw [←pow_add, add_comm n, nat.add_sub_add_right, add_comm z], }
end

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
    rw [finset.image_insert, finset.coe_insert, submodule.mem_span_insert],
    have H := sum_pow_mem_span.aux (r a * f a) (sum T (λ a, r a • f a)) (n a) (sum T n + 1),
    rcases H with ⟨x, y, H⟩,
    have Hx := @submodule.smul_mem _ _ _ _ _ _ _ x IH,
    use [y * (r a) ^ (n a), x • sum T (λ (a : β), r a • f a) ^ (sum T n + 1), Hx],
    repeat { rw smul_eq_mul, },
    rw [add_assoc, H, add_comm, mul_pow, mul_assoc], }
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
