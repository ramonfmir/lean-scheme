
import data.set.basic
import ring_theory.localization

import preliminaries.localisation

universes u v w

-- Define localisation on a set of generators.

section localisation_on_generators 

parameters {A : Type u} {B : Type v} {C : Type w} 
parameters [comm_ring A] [comm_ring B] [comm_ring C]
parameters (G : set A) (f : A → B) [is_ring_hom f]

def S : set A := monoid.closure G
instance S_submonoid : is_submonoid S := monoid.closure.is_submonoid G

def is_localization' := localization_alt.is_localization S f

end localisation_on_generators

/-
 Trying to fix issues in:
 https://github.com/kbuzzard/lean-stacks-project/blob/595aa1d6c5ce5a6fa0259c5a0a2226a91b07d96e/src/canonical_isomorphism_nonsense.lean#L268

 We want to prove the sheaf condition on the presheaf defined on the standard 
 opens D(fi) as in https://stacks.math.columbia.edu/tag/01HR.

 In the proof, they use Lemma 10.23.1/2 https://stacks.math.columbia.edu/tag/00EI
 which is when the "canonical isomorphism nonsense" was used.

 We should start testing this new API with the lemmas on localisation_UMP.
-/

-- Important result.

section

parameters {R : Type u} [comm_ring R]
parameters (a b : R)

-- Generic result.

lemma closure_mem {S : set R} :
∀ {x y : R}, x ∈ monoid.closure S → y ∈ monoid.closure S → (x * y) ∈ monoid.closure S :=
sorry

lemma powers_closure_eq : ∀ x : R, powers x = monoid.closure {x} :=
begin
  intros x,
  apply set.eq_of_subset_of_subset,
  { rintros y ⟨n, Hy⟩ ,
    unfold monoid.closure,
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
      rw [←Hx, ←Hy],
      rw ←pow_add,
      exact ⟨n + m, by simp⟩, } }
end

lemma powers_closure_two_subset : ∀ (x y : R), powers x ⊆ monoid.closure {x, y} :=
begin
  intros x y,
  rw powers_closure_eq,
  apply monoid.closure_mono,
  intros z Hz,
  cases Hz,
  { rw Hz, simp, },
  { cases Hz, }
end

lemma powers_closure_two_subset' : ∀ (x y : R), powers y ⊆ monoid.closure {x, y} :=
begin
  intros x y,
  rw powers_closure_eq,
  apply monoid.closure_mono,
  intros z Hz,
  cases Hz,
  { rw Hz, simp, },
  { cases Hz, }
end

-- R[1/a]

def Ra := localization.away a

instance Ra_comm_ring : comm_ring Ra := localization.away.comm_ring a
instance powers_a_submonoid : is_submonoid (powers a) := powers.is_submonoid a

lemma one_powers_a : (1:R) ∈ powers a := powers_a_submonoid.one_mem

-- A[1/a][1/b]

def b' : Ra := ⟦⟨b, 1, one_powers_a⟩⟧ 

def Rab := localization.loc Ra (powers b')
instance Afg_comm_ring : comm_ring Rab := localization.away.comm_ring b'
instance powers_b'_submonoid : is_submonoid (powers b') := powers.is_submonoid b'

lemma one_powers_b' : (1:Ra) ∈ powers b' := powers_b'_submonoid.one_mem

lemma one_powers_b'_mk : (1:Ra) = ⟦⟨1, 1, one_powers_a⟩⟧ :=
begin apply quotient.sound; use [1, one_powers_a]; simp end

lemma elem_powers_b'_bn
: ∀ x : Ra, x ∈ powers b' ↔ ∃ n : ℕ, x = ⟦⟨b ^ n, 1, one_powers_a⟩⟧ :=
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
      rw Hn (b' ^ n); try { refl },
      apply quotient.sound; use [1, one_powers_a]; simp, } },
  { rintros ⟨n, Hx⟩,
    existsi n,
    revert x,
    induction n with n Hn,
    { simp, apply quotient.sound; use [1, one_powers_a]; simp, },
    { intros x Hx,
      rw pow_succ at *,
      rw Hx,
      rw Hn (⟦(b ^ n, ⟨1, _⟩)⟧); try { refl },
      apply quotient.sound; use [1, one_powers_a]; simp, } }
end

lemma elem_powers_b'
: ∀ x : Ra, x ∈ powers b' ↔ ∃ y ∈ powers b, x = ⟦⟨y, 1, one_powers_a⟩⟧ :=
begin
  intros x,
  split,
  { intros Hx,
    have Hbn := (elem_powers_b'_bn x).1 Hx,
    rcases Hbn with ⟨n, Hx⟩,
    use [b ^ n, ⟨n, rfl⟩],
    exact Hx, },
  { rintros ⟨y, ⟨n, Hy⟩, Hx⟩,
    rw ←Hy at Hx,
    apply (elem_powers_b'_bn x).2 ⟨n, Hx⟩, }
end

-- h : A --> A[1/ab]

def h : R → Rab := λ x, ⟦⟨⟦⟨x, 1, one_powers_a⟩⟧, 1, one_powers_b'⟩⟧
instance is_ring_hom_h : is_ring_hom h :=
{ map_one := rfl,
  map_add := λ x y,
  begin
    apply quotient.sound; use [1, one_powers_b']; simp,
    apply quotient.sound; use [1, one_powers_a]; simp,
  end,
  map_mul := λ x y,
  begin
    apply quotient.sound; use [1, one_powers_b']; simp,
    apply quotient.sound; use [1, one_powers_a]; simp,
  end}

-- THE MAIN RESULT

-- Inverses.

@[reducible] def one_Rab : Rab := 1

def binv_Rab : Rab := ⟦⟨⟦⟨1, 1, one_powers_a⟩⟧, b', ⟨1, by simp⟩⟩⟧
def ainv_Rab : Rab := ⟦⟨⟦⟨1, a, ⟨1, by simp⟩⟩⟧, 1, one_powers_b'⟩⟧

lemma loc_inverts : localization_alt.inverts (S {a, b}) h :=
begin
  rintros ⟨x, Hx⟩,
  induction Hx,
  case monoid.in_closure.basic : y Hy 
  { rcases Hy with ⟨Hya, Hyb⟩,
    { existsi binv_Rab,
      apply quotient.sound; use [1, one_powers_b']; simp,
      apply quotient.sound; use [1, one_powers_a]; simp, },
    { cases Hy,
      { existsi ainv_Rab,
        apply quotient.sound; use [1, one_powers_b']; simp,
        apply quotient.sound; use [1, one_powers_a]; simp,
        rw Hy, simp, },
      { cases Hy, } } },
  case monoid.in_closure.one
  { existsi one_Rab,
    simp, rw is_ring_hom_h.map_one, },
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

lemma loc_has_denom : localization_alt.has_denom (monoid.closure {a, b}) h :=
begin
  intros x,
  refine quotient.induction_on x _,
  rintros ⟨xRa, xdenRab⟩,
  refine quotient.induction_on xRa _,
  rintros ⟨xR, xdenRa⟩,
  rcases xdenRa with ⟨y, Hy⟩,
  rcases xdenRab with ⟨w, Hw⟩,
  have Hb := (elem_powers_b' w).1 Hw,
  rcases Hb with ⟨z, Hz, Hweq⟩,
  have HySab : y ∈ monoid.closure {a, b} := (powers_closure_two_subset a b) Hy,
  have HzSab : z ∈ monoid.closure {a, b} := (powers_closure_two_subset' a b) Hz,
  have HyzSab := closure_mem HySab HzSab,
  dsimp,
  use (⟨(y * z), HyzSab⟩, xR),
  dsimp,
  apply quotient.sound,
  dsimp,
  use [w, Hw],
  simp,
  rw Hweq,
  apply quotient.sound,
  simp,
  use [y, Hy],
  simp,
  rw mul_assoc y,
  rw add_right_neg,
  simp,
end

lemma loc_ker_ann : localization_alt.ker h = localization_alt.submonoid_ann (S {a, b}) :=
sorry

lemma loc_Afg : is_localization' {a, b} h :=
begin
  split,
end

end
