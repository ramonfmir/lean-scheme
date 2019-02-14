import ring_theory.localization
import preliminaries.localisation
--import localisation_test
import tactic.find

universes u v w

-- Need this.

lemma prime_ideal_not_top 
{α : Type u} [comm_ring α] (I : ideal α) [P : ideal.is_prime I] : I ≠ ⊤ := P.1

section loc_test_3

parameters (P : ideal ℤ) [ideal.is_prime P]

-- Z(p).

def Zp := localization.at_prime P 
instance comm_ring_Zp : comm_ring Zp := localization.at_prime.comm_ring P

def f : ℤ → Zp := λ x, ⟦⟨x, 1⟩⟧
instance is_ring_hom_f : is_ring_hom f :=
{ map_one := rfl,
  map_mul := 
    begin 
      intros x y,
      apply quotient.sound,
      existsi (1 : ℤ),
      have HP := (ideal.ne_top_iff_one P).1 (prime_ideal_not_top P),
      existsi ((set.mem_compl_iff ↑P 1).2 HP),
      erw one_mul,
      simp,
    end,
  map_add := 
    begin
      intros x y,
      apply quotient.sound,
      existsi (1 : ℤ),
      have HP := (ideal.ne_top_iff_one P).1 (prime_ideal_not_top P),
      existsi ((set.mem_compl_iff ↑P 1).2 HP),
      rw mul_add,
      repeat { erw one_mul },
      simp,
      repeat { rw ←add_assoc },
      simp,
    end, }

-- Z/p.

def ZpZ := ideal.quotient P
instance comm_ring_ZpZ : comm_ring ZpZ := ideal.quotient.comm_ring P

def g : ℤ → ZpZ := λ x, ideal.quotient.mk P x
instance is_ring_hom_g : is_ring_hom g :=
{ map_one := rfl,
  map_mul := λ x y, by apply quotient.sound; simp,
  map_add := λ x y, by apply quotient.sound; simp, }

-- Z(p) --> Z/p

def h : Zp → ZpZ := sorry


end loc_test_3
