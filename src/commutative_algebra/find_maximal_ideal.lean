/-
  Kenny needed this to prove properties about Spec.

  Is this done better anywhere in the mathlib??
-/

import ring_theory.ideals

noncomputable theory
local attribute [instance] classical.prop_decidable

universe u

open lattice

section find_maximal_ideal

parameters {α : Type u} [comm_ring α] (P : ideal α) [HPnT : P ≠ ⊤]

instance ideal.has_subset : has_subset (ideal α) :=
{ subset := λ I J, I.1 ⊆ J.1, }

instance ideal.partial_order : partial_order (ideal α) :=
{ le := λ I J, I ⊆ J,
  le_refl := λ I, by apply set.subset.refl,
  le_trans := λ I J K, by apply set.subset.trans,
  le_antisymm := λ I J HIJ HJI, ideal.ext $ λ x, ⟨λ Hx, HIJ Hx, λ Hx, HJI Hx⟩, }

instance find_maximal_ideal.partial_order : partial_order {S : ideal α // P ⊆ S ∧ S ≠ ⊤} := 
begin
  apply subtype.partial_order _,
  apply_instance,
end

instance find_maximal_ideal.inhabited : inhabited {S : ideal α // P ⊆ S ∧ S ≠ ⊤} :=
⟨⟨P, set.subset.refl P, HPnT⟩⟩

include HPnT

private theorem find_maximal_ideal.aux :
  ∃ (M : {S : ideal α // P ⊆ S ∧ S ≠ ⊤}), ∀ x, M ≤ x → x = M :=
begin
  apply zorn.zorn_partial_order,
  intros c Hc,
  cases (classical.em (c = ∅)) with Hce Hce,
  { use ⟨P, set.subset.refl P, HPnT⟩,
    rw Hce,
    intros a Ha,
    cases Ha, },
  replace Hce := set.coe_nonempty_iff_ne_empty.2 Hce,
  replace Hce := classical.exists_true_of_nonempty Hce,
  replace Hce := set_coe.exists.1 Hce,
  rcases Hce with ⟨Q, HQ, H⟩; clear H,
  use [{y | ∃ S ∈ (subtype.val '' c), y ∈ S}],
  { -- zero
    use Q,
    simp, 
    exact ⟨Q.2, HQ⟩, },
  { -- add 
    intros x y Hx Hy,
    rcases Hx with ⟨I, ⟨HI, ⟨HIc, HIval⟩⟩, HxI⟩,
    rcases Hy with ⟨J, ⟨HJ, ⟨HJc, HJval⟩⟩, HyJ⟩,
    cases (classical.em (HI = HJ)),
    { use I, 
      simp,
      rw ←HIval,
      use HI.2, 
      simp,
      use HIc,
      rw HIval,
      rw [←HJval, ←h, HIval] at HyJ,
      exact (ideal.add_mem I HxI HyJ), },
    have Hzn := Hc HI HIc HJ HJc h,
    rw ←HJval at HyJ,
    rw ←HIval at HxI,
    cases Hzn,
    { use J,
      simp,
      rw ←HJval, 
      use HJ.2,
      { simp,
        use HJc, },
      replace HxI := Hzn HxI,
      apply ideal.add_mem _ HxI HyJ, },
    { use I,
      simp,
      rw ←HIval,
      use HI.2,
      { simp,
        use HIc, },
      replace HyJ := Hzn HyJ,
      apply ideal.add_mem _ HxI HyJ, } },
  { -- smul 
    intros k x Hx, 
    rcases Hx with ⟨I, ⟨HI, ⟨HIc, HIval⟩⟩, HxI⟩,
    use I,
    rw ←HIval,
    simp,
    use [HI.2, HIc],
    rw ←HIval at HxI,
    apply ideal.mul_mem_left _ HxI, },
  -- We have that ⋃ In is an ideal. Now we prove that it is an upper bound.
  { split,
    { intros x Hx,
      simp,
      use [Q.1, Q.2],
      { simp,
        use HQ, },
      exact (Q.2.1 Hx), },
    { intros HC,
      have Hone := (ideal.eq_top_iff_one _).1 HC,
      rcases Hone with ⟨I, ⟨HI, ⟨HIc, HIval⟩⟩, Hone⟩,
      apply HI.2.2,
      rw HIval,
      exact (ideal.eq_top_iff_one _).2 Hone, }, },
  { intros a Ha x Hx,
    use a.1,
    simp,
    exact ⟨⟨a.2, Ha⟩, Hx⟩, }
end

def find_maximal_ideal : ideal α :=
(classical.some find_maximal_ideal.aux).1

theorem find_maximal_ideal.contains : P ⊆ find_maximal_ideal :=
(classical.some find_maximal_ideal.aux).2.1

def find_maximal_ideal.is_maximal_ideal :
  ideal.is_maximal find_maximal_ideal :=
let HM := classical.some_spec find_maximal_ideal.aux in
let M := classical.some find_maximal_ideal.aux in
begin 
  split,
  { exact M.2.2, },
  { intros J HJ,
    by_contra HC,
    have HPJ : P ⊆ J := set.subset.trans find_maximal_ideal.contains HJ.1,
    have HMJ := (HM ⟨J, HPJ, HC⟩) HJ.1,
    have HnMJ := ne_of_lt HJ,
    apply HnMJ,
    exact subtype.ext.1 HMJ.symm, }
end

end find_maximal_ideal
