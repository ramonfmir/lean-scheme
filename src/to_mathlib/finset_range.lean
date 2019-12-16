/-
  Some basic results about ranges over finite sets that I found useful.

  TODO : Check how much of this isn't actually somehwere in the mathlib.
-/

import data.finset
import data.finsupp
import data.nat.choose

universes u v w

open finset

section basics

-- range(f) = f '' {γ1, ..., γn}.

lemma finset.coe_image_univ {α : Type u} {β : Type v} [fintype α] [decidable_eq β] {f : α → β}
: set.range f = ↑(finset.image f finset.univ) :=
by rw [finset.coe_image, finset.coe_univ, ←set.image_univ]

-- f (Σi=1..n ai) = Σi=1..n f (ai).

lemma is_ring_hom.map_finset_sum 
{A : Type u} {B : Type v} [comm_ring A] [comm_ring B] (f : A → B) [is_ring_hom f] 
{C : Type w} [decidable_eq C] (s : C → A) (X : finset C)
: f (finset.sum X s) = finset.sum X (f ∘ s) :=
begin
  apply finset.induction_on X,
  { iterate 2 { rw finset.sum_empty, },
    exact is_ring_hom.map_zero f, },
  { intros a T HanT IH,
    iterate 2 { rw finset.sum_insert HanT, },
    rw is_ring_hom.map_add f,
    rw IH, }
end

-- Obvious: n ∉ {0, ..., n-1}.

@[simp] lemma finset.range_not_mem : ∀ n : ℕ, n ∉ range n :=
λ n Hn, (lt_irrefl n) (finset.mem_range.1 Hn)

-- If f(i) = g(i) for i=0..n then Σi=0..n f(i) = Σi=0..n g(i).

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

-- Σi=0..(n+m) f(i) = (Σi=0..n f(i)) + (Σi=0..m f(i+n)).

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

end basics

-- (a + b)^(n + m) = x * b ^ m + y * a ^ n
--  where x = Σi=0..(n-1) ((n+m), i) * a^i * b^(n-i),
--        y = Σi=0..m ((n+m), (i+n)) * a^i * b^(m-i).

-- Note: This might be way too specific.

lemma add_pow_sum
{α : Type u} [comm_ring α] 
: ∀ (a b : α), ∀ (n m : ℕ), ∃ (x y : α), 
  (a + b) ^ (n + m) = x * (b ^ m) + y * (a ^ n) :=
begin
  intros a b n m,
  rw add_pow,
  let cnmi : ℕ → α := λ i, ((nat.choose (n+m) i):α), 
  use [finset.sum (range n) (λ i, a ^ i * b ^ (n - i) * (nat.choose (n + m) i))],
  use [sum (range (nat.succ m)) (λ i, a ^ i * b ^ (m - i) * (nat.choose (n + m) (i + n)))],
  rw add_comm (_ * _),
  repeat { rw finset.sum_mul, },
  repeat { rw finset.range_succ, },
  repeat { rw finset.sum_insert; try { apply finset.range_not_mem, }, },
  rw add_assoc,
  congr' 1,
  { rw [mul_assoc _ _ (a ^ n), mul_comm _ (a ^ n), ←mul_assoc _ (a ^ n) _],
    rw [mul_assoc _ _ (a ^ n), mul_comm _ (a ^ n), ←mul_assoc _ (a ^ n) _],
    rw [←pow_add, add_comm m],
    simp, },
  rw finset.sum_range_add,
  rw add_comm,
  congr' 1,
  { apply finset.sum_range_eq,
    intros z Hz,
    rw [mul_assoc _ _ (a ^ n), mul_comm _ (a ^ n), ←mul_assoc _ (a ^ n) _],
    rw [mul_assoc _ _ (a ^ n), mul_comm _ (a ^ n), ←mul_assoc _ (a ^ n) _],
    rw [←pow_add, add_comm n, nat.add_sub_add_right, add_comm z], },
  { apply finset.sum_range_eq,
    intros z Hz,
    rw [mul_assoc _ _ (b ^ m), mul_comm _ (b ^ m), ←mul_assoc _ (b ^ m) _],
    rw [mul_assoc _ _ (b ^ m), ←pow_add, add_comm n _, add_comm (n - z) _], 
    rw [←nat.add_sub_assoc],
    exact nat.le_of_lt Hz, },
end
