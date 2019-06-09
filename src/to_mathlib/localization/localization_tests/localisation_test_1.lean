/-
  First localization test. R[1/a][1/b] ≅ R[1/ab].
-/

import ring_theory.localization
import to_mathlib.localization.localization_alt

universes u v w

open localization_alt

-- Define localisation on a set of generators.

section localization_on_generators 

parameters {A : Type u} {B : Type v} {C : Type w} 
parameters [comm_ring A] [comm_ring B] [comm_ring C]
parameters (G : set A) (f : A → B) [is_ring_hom f]

def S : set A := monoid.closure G
instance S_submonoid : is_submonoid S := monoid.closure.is_submonoid G

def is_localization' := is_localization S f
def is_localization_data' := is_localization_data S f

end localization_on_generators

-- We show that R[1/a][1/b] = R[1/ab], i.e. is_localization' R[1/a][1/b] (a*b).

section localization_ab

parameters {R : Type u} [comm_ring R]
parameters (a b : R)

-- I need this because localization on generators is defined using monoid.closure.

lemma powers_closure_eq : ∀ x : R, powers x = S {x} :=
begin
  intros x,
  apply set.eq_of_subset_of_subset,
  { rintros y ⟨n, Hy⟩,
    revert x y,
    induction n with n Hn,
    { intros x y Hx,
      simp at Hx,
      rw ←Hx,
      exact monoid.in_closure.one {x}, },
    { intros x y Hx,
      rw pow_succ at Hx,
      have Hxx : x ∈ {x} := set.mem_singleton x,
      have Hxclo := monoid.in_closure.basic Hxx,
      have Hxnclo := Hn x (eq.refl (x ^ n)),
      rw ←Hx,
      apply monoid.in_closure.mul Hxclo Hxnclo, } },
  { intros y Hy,
    induction Hy,
    case monoid.in_closure.basic : z Hz 
    { cases Hz, 
      { rw Hz,
        exact ⟨1, by simp⟩, },
      { cases Hz, } },
    case monoid.in_closure.one
    { exact (powers.is_submonoid x).one_mem, },
    case monoid.in_closure.mul : x y HxS HyS Hx Hy
    { rcases Hx with ⟨n, Hx⟩,
      rcases Hy with ⟨m, Hy⟩,
      rw [←Hx, ←Hy, ←pow_add],
      exact ⟨n + m, by simp⟩, } }
end

-- Definition of R[1/a].

@[reducible] def Ra := localization.away a

instance Ra_comm_ring : comm_ring Ra := by apply_instance
instance powers_a_submonoid : is_submonoid (powers a) := powers.is_submonoid a

lemma one_powers_a : (1:R) ∈ powers a := powers_a_submonoid.one_mem

-- Definition of R[1/a][1/b].

def b1 : Ra := ⟦⟨b, 1, one_powers_a⟩⟧ 

@[reducible] def Rab := localization Ra (powers b1)

instance Afg_comm_ring : comm_ring Rab := by apply_instance
instance powers_b1_submonoid : is_submonoid (powers b1) := powers.is_submonoid b1

lemma one_powers_b1 : (1:Ra) ∈ powers b1 := powers_b1_submonoid.one_mem

-- Basically saying that b1 is b/1.

lemma elem_powers_b1_bn
: ∀ {x : Ra}, x ∈ powers b1 ↔ ∃ n : ℕ, x = ⟦⟨b ^ n, 1, one_powers_a⟩⟧ :=
begin
  intros x,
  split,
  { intros Hx,
    rcases Hx with ⟨n, Hx⟩,
    existsi n,
    revert x,
    induction n with n Hn,
    { simp, apply quotient.sound; use [1, one_powers_a]; simp, },
    { intros x Hx,
      rw pow_succ at *,
      rw ←Hx,
      rw @Hn (b1 ^ n); try { refl },
      apply quotient.sound; use [1, one_powers_a]; simp, } },
  { rintros ⟨n, Hx⟩,
    existsi n,
    revert x,
    induction n with n Hn,
    { simp, apply quotient.sound; use [1, one_powers_a]; simp, },
    { intros x Hx,
      rw pow_succ at *,
      rw Hx,
      rw @Hn (⟦(b ^ n, ⟨1, _⟩)⟧); try { refl },
      apply quotient.sound; use [1, one_powers_a]; simp, } }
end

lemma elem_powers_b1
: ∀ {x : Ra}, x ∈ powers b1 ↔ ∃ y ∈ powers b, x = ⟦⟨y, 1, one_powers_a⟩⟧ :=
begin
  intros x,
  split,
  { intros Hx,
    have Hbn := elem_powers_b1_bn.1 Hx,
    rcases Hbn with ⟨n, Hx⟩,
    existsi (b ^ n),
    existsi (⟨n, by simp⟩ : b ^ n ∈ powers b),
    exact Hx, },
  { rintros ⟨y, ⟨n, Hy⟩, Hx⟩,
    rw ←Hy at Hx,
    apply elem_powers_b1_bn.2 ⟨n, Hx⟩, }
end

-- Localization map A --> A[1/a][1/b].

@[reducible] def h : R → Rab := λ x, ⟦⟨⟦⟨x, 1, is_submonoid.one_mem _⟩⟧, 1, is_submonoid.one_mem _⟩⟧
instance is_ring_hom_h : is_ring_hom h :=
{ map_one := rfl,
  map_add := λ x y,
  begin
    apply quotient.sound; use [1, one_powers_b1]; simp,
    apply quotient.sound; use [1, one_powers_a]; simp,
  end,
  map_mul := λ x y,
  begin
    apply quotient.sound; use [1, one_powers_b1]; simp,
    apply quotient.sound; use [1, one_powers_a]; simp,
  end}

-- Proving the lemmas: inverts, denom and ker = ann.

section localization_ab_proof

-- Inverses.

def one_Rab : Rab := 1

def binv_Rab : Rab := ⟦⟨⟦⟨1, 1, one_powers_a⟩⟧, b1, ⟨1, by simp⟩⟩⟧
def ainv_Rab : Rab := ⟦⟨⟦⟨1, a, ⟨1, by simp⟩⟩⟧, 1, one_powers_b1⟩⟧

lemma loc_inverts : inverts (S {a * b}) h :=
begin
  rintros ⟨x, Hx⟩,
  induction Hx,
  case monoid.in_closure.basic : y Hy 
  { rcases Hy with ⟨Hya, Hyb⟩,
    { existsi (ainv_Rab * binv_Rab),
      apply quotient.sound; use [1, one_powers_b1]; simp,
      apply quotient.sound; use [1, one_powers_a]; simp,
      rw Hy; simp, },
    { cases Hy, } },
  case monoid.in_closure.one
  { existsi one_Rab,
    simp,
    rw is_ring_hom_h.map_one, 
    simpa, },
  case monoid.in_closure.mul : x y HxS HyS Hx Hy
  { rcases Hx with ⟨xinv, Hxinv⟩,
    rcases Hy with ⟨yinv, Hyinv⟩,
    existsi (xinv * yinv),
    simp at *,
    rw [is_ring_hom_h.map_mul, mul_comm _ yinv, mul_assoc, ←mul_assoc (h y)],
    rw [Hyinv, one_mul],
    exact Hxinv, }
end

-- Denoms.

def homogenizer (n m : ℕ) : R := if n ≤ m then a^(m - n) else b^(n - m)

lemma homogenizer_a {n m : ℕ} : n ≤ m → homogenizer n m = a^(m - n) :=
begin
  intros Hnm,
  dunfold homogenizer,
  rw if_eq_of_eq_true,
  apply eq_true_intro Hnm,
end

lemma homogenizer_b {n m : ℕ} : ¬(n ≤ m) → homogenizer n m = b^(n - m) := 
begin
  intros Hnm,
  dunfold homogenizer,
  rw if_eq_of_eq_false,
  apply eq_false_intro Hnm,
end

lemma homogenizer_mul : ∀ n m, a^n * b^m * homogenizer n m = a^(max n m) * b^(max n m) :=
begin
  intros n m,
  cases (classical.em (n ≤ m)) with Htt Hff,
  { rw homogenizer_a Htt,
    rw max_eq_right Htt,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw ←pow_add,
    rw nat.sub_add_cancel Htt,
    rw mul_comm, },
  { rw homogenizer_b Hff,
    replace Hff := le_of_not_le Hff,
    rw max_eq_left Hff,
    rw mul_assoc,
    rw ←pow_add,
    rw add_comm,
    rw nat.sub_add_cancel Hff, }
end

lemma loc_has_denom : has_denom (S {a * b}) h :=
begin
  intros x,
  refine quotient.induction_on x _,
  rintros ⟨xRa, xdenRab⟩,
  refine quotient.induction_on xRa _,
  rintros ⟨xR, xdenRa⟩,
  rcases xdenRa with ⟨y, Hy⟩,
  rcases xdenRab with ⟨w, Hw⟩,
  have Hb := elem_powers_b1.1 Hw,
  rcases Hb with ⟨z, Hz, Hweq⟩,
  have Hy' := Hy,
  rcases Hy with ⟨n, Hy⟩,
  rcases Hz with ⟨m, Hz⟩,
  have HyzkSab : (a * b)^(max n m) ∈ powers (a * b) := ⟨(max n m), by simp⟩,
  rw powers_closure_eq at HyzkSab,
  simp,
  existsi (a * b)^(max n m),
  existsi HyzkSab,
  existsi xR * homogenizer n m,
  apply quotient.sound, 
  use [w, Hw]; simp,
  rw Hweq,
  apply quotient.sound, 
  simp,
  existsi y,
  existsi Hy',
  simp,
  rw [←Hy, ←Hz],
  rw mul_comm xR,
  rw ←mul_assoc (b^m),
  rw ←mul_assoc (a^n),
  rw ←mul_assoc (a^n),
  rw homogenizer_mul n m,
  rw mul_pow a b,
  simp, 
end

-- Kernel is monoid annihilator.

lemma loc_ker_ann_sub : ker h ≤ submonoid_ann (S {a * b}) :=
λ x Hx,
begin
  unfold submonoid_ann,
  unfold ker at *,
  unfold ideal.mk at *,
  have Hx : x ∈ {x : R | h x = 0} := Hx,
  have Hx0 : h x = 0 := by apply_assumption,
  dunfold ann_aux,
  unfold set.range,
  simp,
  show ∃ (c z : R), z ∈ S {a * b} ∧ c * z = 0 ∧ c = x,
    existsi x,
    dunfold h at Hx0,
    have Hx01 := quotient.exact Hx0,
    rcases Hx01 with ⟨t, Ht, Hx01⟩,
    simp at Hx01,
    have Hty1 := elem_powers_b1.1 Ht,
    rcases Hty1 with ⟨y, Hy, Hty1⟩,
    rw Hty1 at Hx01,
    have Hxy0 := quotient.exact Hx01,
    rcases Hxy0 with ⟨z, Hz, Hxyz0⟩,
    simp at Hxyz0,
    rcases Hy with ⟨m, Hy⟩,
    rcases Hz with ⟨n, Hz⟩,
    existsi (z * y * homogenizer n m),
    split,
    { rw [←Hy, ←Hz, homogenizer_mul n m, ←mul_pow, ←powers_closure_eq],
      exact ⟨max n m, rfl⟩, },
    { split; try { refl },
      rw [←mul_assoc, mul_comm z, ←mul_assoc, Hxyz0],
      simp, }
end

lemma loc_ker_ann : ker h = submonoid_ann (S {a * b}) :=
begin
  apply le_antisymm,
  { exact loc_ker_ann_sub, },
  { exact inverts_ker (S {a * b}) h loc_inverts, }
end

-- R[1/a][1/b] = R[1/ab].

open localization

lemma loc_Rab : is_localization' {a * b} ((of ∘ of) : R → Rab) :=
⟨loc_inverts, loc_has_denom, loc_ker_ann⟩

end localization_ab_proof

end localization_ab
