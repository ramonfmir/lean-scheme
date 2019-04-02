/-
  If (fᵢ) = R, the sequene R → Π R[1/fᵢ] → Π R[1/fᵢfⱼ] is exact.

  https://stacks.math.columbia.edu/tag/00EJ
-/

import ring_theory.localization
import algebra.pi_instances
import linear_algebra.linear_combination
import preliminaries.localisation
import to_mathlib.finset_range

--import tactic.find

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

section exact_sequence 

-- Ring R.
parameters (R : Type u) [comm_ring R] 
-- f1, ..., fn
parameters {γ : Type v} [fintype γ] {f : γ → R}
-- R[1/f1], ..., R[1/fn]
parameters {Rfi : γ → Type w} [Π i, comm_ring (Rfi i)]
-- α1 : R → R[1/f1], ...., αn → R[1/fn]
parameters {αi : Π i, R → (Rfi i)} [Π i, is_ring_hom (αi i)]
parameters (Hlocα : Π i, is_localization (powers (f i)) (αi i))
parameters (Hlocα' : Π i, is_localization_data (powers (f i)) (αi i))

def α : R → Π i, Rfi i := λ r i, (αi i) r

-- R[1/f1f1], ..., R[1/fnfn]
parameters {Rfij : γ → γ → Type w} [Π i j, comm_ring (Rfij i j)]
parameters {φij : Π i j, R → (Rfij i j)} [Π i j, is_ring_hom (φij i j)]
parameters (Hlocφ : Π i j, is_localization (powers ((f i)*(f j))) (φij i j))
parameters (Hlocφ' : Π i j, is_localization_data (powers ((f i)*(f j))) (φij i j))

section alpha_injective

instance PRfs.comm_ring : comm_ring (Π i, Rfi i) :=
pi.comm_ring

instance α.is_ring_hom : is_ring_hom α :=
pi.is_ring_hom_pi αi

-- First part of the lemma.

include Hlocα

lemma standard_covering₁ (H : (1 : R) ∈ ideal.span (set.range f)) 
: function.injective α := 
begin
  rw ←@is_ring_hom.inj_iff_trivial_ker _ _ _ _ α α.is_ring_hom,
  intros x Hx,
  replace Hx := congr_fun Hx,
  have Hn : ∀ i, ∃ n : ℕ, f i ^ n * x = 0,
    intros i,
    replace Hx : x ∈ ker (αi i) := Hx i,
    replace Hloc := Hlocα i,
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

include Hlocφ'

-- fj is invertible in R[1/fifj].

noncomputable def inverts_powers1 : Π i j, inverts_data (powers (f j)) (φij i j) :=
λ i j r,
begin
  rcases r with ⟨r, Hr⟩,
  rcases (classical.indefinite_description _ Hr) with ⟨n, Hn⟩,
  rcases ((Hlocφ' i j).inverts ⟨((f i)*(f j))^n, ⟨n , by simp⟩⟩) with ⟨w, Hw⟩,
  use ((φij i j ((f i)^n)) * w),
  simp,
  simp at Hw,
  rw [←Hn, ←mul_assoc, ←is_ring_hom.map_mul (φij i j), ←mul_pow, mul_comm (f j)],
  exact Hw,
end

-- fi is invertible in R[1/fifj].

noncomputable def inverts_powers2 : Π i j, inverts_data (powers (f i)) (φij i j) :=
λ i j r,
begin
  cases r with r Hr,
  cases (classical.indefinite_description _ Hr) with n Hn,
  cases ((Hlocφ' i j).inverts ⟨((f i)*(f j))^n, ⟨n , by simp⟩⟩) with w Hw,
  use ((φij i j ((f j)^n)) * w),
  simp,
  simp at Hw,
  rw [←Hn, ←mul_assoc, ←is_ring_hom.map_mul (φij i j), ←mul_pow],
  exact Hw,
end

noncomputable def β1 : (Π i, Rfi i) → (Π i j, Rfij i j)
:= λ ri i j, (is_localization_initial (powers (f j)) (αi j) (Hlocα' j) (φij i j) (inverts_powers1 i j)) (ri j)

noncomputable def β2 : (Π i, Rfi i) → (Π i j, Rfij i j)
:= λ ri i j, (is_localization_initial (powers (f i)) (αi i) (Hlocα' i) (φij i j) (inverts_powers2 i j)) (ri i)

noncomputable def β : (Π i, Rfi i) → (Π i j, Rfij i j) := λ r, (β1 r) - (β2 r) 

lemma standard_covering₂.aux (s : Π i, Rfi i)
: ∀ i j, (β1 s i j = β2 s i j → 
  ∃ n : ℕ,
    (((Hlocα' j).has_denom (s j)).1.2 * ((Hlocα' i).has_denom (s i)).1.1 -
     ((Hlocα' i).has_denom (s i)).1.2 * ((Hlocα' j).has_denom (s j)).1.1) *
     ((f i) * (f j))^n = 0) := 
begin
  intros i j,
  simp [β1, β2, is_localization_initial],
  rcases ((Hlocα' i).has_denom (s i)) with ⟨⟨q1, p1⟩, Hp1q1⟩,
  rcases ((Hlocα' j).has_denom (s j)) with ⟨⟨q2, p2⟩, Hp2q2⟩,
  simp at Hp1q1,
  simp at Hp2q2,
  dsimp [subtype.coe_mk],
  rcases ((Hlocα' i).inverts q1) with ⟨w1, Hw1⟩,
  rcases ((Hlocα' j).inverts q2) with ⟨w2, Hw2⟩,
  rcases (inverts_powers2 i j q1) with ⟨v1, Hv1⟩,
  rcases (inverts_powers1 i j q2) with ⟨v2, Hv2⟩,
  dsimp [subtype.coe_mk],
  intros H,
  have Hker : φij i j (p2 * q1 - p1 * q2) = 0,
    rw is_ring_hom.map_sub (φij i j),
    iterate 2 { rw is_ring_hom.map_mul (φij i j), },
    rw [sub_eq_zero, ←one_mul (_ * _), ←Hv2, ←mul_assoc, mul_assoc _ v2 _, mul_comm v2],
    rw [H, ←mul_assoc, mul_assoc _ v1 _, mul_comm v1],
    rw [Hv1, mul_one, mul_comm],
  replace Hker : _ ∈ ker (φij i j) := Hker,
  replace Hker := (Hlocφ' i j).ker_le Hker,
  rcases Hker with ⟨⟨⟨u, v⟩, Huv⟩, Hzer⟩,
  dsimp at Huv,
  dsimp only [subtype.coe_mk] at Hzer,
  rw Hzer at Huv,
  rcases v with ⟨v, ⟨n, Hn⟩⟩,
  dsimp only [subtype.coe_mk] at Huv,
  rw ←Hn at Huv,
  use n,
  exact Huv,
end

lemma standard_covering₂.aux₂ (s : Π i, Rfi i)
: (∀ i j, β1 s i j = β2 s i j) → 
  ∃ N : ℕ, ∀ i j,
    (((Hlocα' j).has_denom (s j)).1.2 * ((Hlocα' i).has_denom (s i)).1.1 -
     ((Hlocα' i).has_denom (s i)).1.2 * ((Hlocα' j).has_denom (s j)).1.1) *
     ((f i) * (f j))^N = 0 := 
begin
  intros Hs,
  let n : γ × γ → ℕ := λ ij, classical.some (standard_covering₂.aux s ij.1 ij.2 (Hs ij.1 ij.2)),
  let N := finset.sum (@finset.univ (γ × γ) _) n,
  use N,
  intros i j,
  have Hn : ∀ i j, n (i, j) ≤ N,
    intros i j,
    exact finset.single_le_sum (λ _ _, nat.zero_le _) (finset.mem_univ (i, j)),
  rw ←nat.sub_add_cancel (Hn i j),
  rw add_comm,
  rw pow_add,
  rw ←mul_assoc,
  rw classical.some_spec (standard_covering₂.aux s i j (Hs i j)),
  rw zero_mul,
end

lemma standard_covering₂
(Hone : (1:R) ∈ submodule.span R (↑(univ.image f) : set R)) (s : Π i, Rfi i)
: β s = 0 ↔ ∃ r : R, α r = s := 
begin
  split,
  { intros H,
    suffices Hsuff : ∃ (r : R), ∀ i, α r i = s i,
      rcases Hsuff with ⟨r, Hr⟩,
      use r,
      apply funext,
      exact Hr,
    simp [α],
    replace H := sub_eq_zero.1 H,
    replace H := congr_fun H,
    replace H := λ i j, (congr_fun (H i)) j,
    rcases (standard_covering₂.aux₂ s H) with ⟨N, HN⟩,
    have r := λ i, classical.some ((Hlocα' i).has_denom (s i)).1.1.2,
    have t := λ i, ((Hlocα' i).has_denom (s i)).1.2,
    have Hone' := (one_mem_span_pow_of_mem_span f (λ i, r i + N) Hone),
    rcases (finset.image_sum_of_mem_span Hone') with ⟨a, Ha⟩,
    use [finset.univ.sum (λ i, a i * (t i) * (f i) ^ N)],
    intros i,
    simp at Ha,
    have w := λ x, ((Hlocα' i).inverts ⟨(f i)^(r x), ⟨r x, by simp⟩⟩),
    rw @is_ring_hom.map_finset_sum _ _ _ _ (αi i),
    simp,
    rcases ((Hlocα' i).has_denom (s i)) with ⟨⟨⟨q, ⟨n, Hn⟩⟩, p⟩, Hpq⟩,
    dsimp only [subtype.coe_mk] at Hpq,
    suffices Hsuff : sum univ (λ (x : γ), αi i (a x * t x * f x ^ (n + N))) = αi i p,
    { sorry, },
    sorry,
    },
  { rintros ⟨r, Hr⟩,
    rw ←Hr,
    erw sub_eq_zero,
    apply funext,
    intros i,
    apply funext,
    intros j,
    simp [β, α, β1, β2],
    iterate 2 { rw is_localization_initial_comp, }, }
end

end beta_kernel_image_alpha

end exact_sequence
