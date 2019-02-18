import ring_theory.localization
import preliminaries.localisation
import tactic.find

universes u v w

-- Need this.

lemma prime_ideal_not_top 
{α : Type u} [comm_ring α] (I : ideal α) [P : ideal.is_prime I] : I ≠ ⊤ := P.1

section loc_test_3

parameters (P : ideal ℤ) [ideal.is_prime P]
@[reducible] def P_set : set ℤ := set.compl ↑P

lemma one_P_set : (1 : ℤ) ∈ P_set :=
begin
  have HnT := prime_ideal_not_top P,
  have H1nP := (ideal.ne_top_iff_one P).1 HnT,
  exact ((set.mem_compl_iff ↑P 1).2 H1nP),
end

instance has_one_P_set : has_one P_set :=
{ one := 1 }

-- Z(p).

def Zp := localization.at_prime P 
instance comm_ring_Zp : comm_ring Zp := localization.at_prime.comm_ring P

def f : ℤ → Zp := λ x, ⟦⟨x, (1 : ℤ), one_P_set⟩⟧
instance is_ring_hom_f : is_ring_hom f :=
{ map_one := rfl,
  map_mul := 
    begin 
      intros x y,
      apply quotient.sound,
      use [1, one_P_set],
      erw one_mul,
      simp,
    end,
  map_add := 
    begin
      intros x y,
      apply quotient.sound,
      use [1, one_P_set],
      simp,
      repeat { rw ←add_assoc },
      simp,
    end, }

-- Sanity check.

@[reducible] def Zp_inv {x : ℤ} (H : x ∈ P_set) : Zp := ⟦⟨(1 : ℤ), x, H⟩⟧

lemma Zp_inverts : localization_alt.inverts P_set f :=
begin
  rintros ⟨x, Hx⟩,
  existsi (Zp_inv Hx),
  apply quotient.sound,
  use [1, one_P_set],
  erw one_mul,
  simp,
end

lemma Zp_denom : localization_alt.has_denom P_set f :=
begin
  intros x,
  refine quotient.induction_on x _,
  rintros ⟨xnom, xden⟩,
  use [⟨xden, xnom⟩],
  apply quotient.sound,
  use [1, one_P_set],
  rcases xden with ⟨xden, Hxden⟩,
  simp,
end

lemma Zp_ker_ann : localization_alt.ker f = localization_alt.submonoid_ann P_set :=
begin
  apply le_antisymm,
  { intros x Hx,
    dunfold localization_alt.submonoid_ann,
    dunfold localization_alt.ann_aux,
    unfold localization_alt.ker at *,
    unfold localization_alt.ideal.mk at *,
    unfold set.range,
    have Hxf0 : f x = 0 := Hx,
    have Hx0 : x = 0,
      rcases (quotient.exact Hxf0) with ⟨z, Hz, Hxz⟩,
      simp at Hxz,
      cases Hxz; try { apply_assumption },
      exact Hxz.symm ▸ P.zero_mem,
    simp,
    show ∃ (a y : ℤ), y ∈ P_set ∧ (a = 0 ∨ y = 0) ∧ a = x,
      use [x, 1],
      split,
      { exact one_P_set, },
      { split,
        { left, apply_assumption, },
        { refl, } } },
  { exact localization_alt.inverts_ker P_set f Zp_inverts, }
end

lemma Zp_is_local : localization_alt.is_localization P_set f :=
⟨Zp_inverts, Zp_denom, Zp_ker_ann⟩

-- Z/p.

def ZpZ := ideal.quotient P
instance comm_ring_ZpZ : comm_ring ZpZ := ideal.quotient.comm_ring P

def g : ℤ → ZpZ := λ x, ideal.quotient.mk P x
instance is_ring_hom_g : is_ring_hom g :=
{ map_one := rfl,
  map_mul := λ x y, by apply quotient.sound; simp,
  map_add := λ x y, by apply quotient.sound; simp, }

-- Z(p) --> Z/p

@[reducible] noncomputable def h' : Zp → ℤ := λ x, (quotient.out x).1

instance is_ring_hom_h' : is_ring_hom h' :=
{ map_one := 
    begin
      suffices Hsuff : ∀ {x : Zp}, x = 1 → h' x = 1,
        apply Hsuff,
        refl,
      intros x,
      refine quotient.induction_on x _,
      rintros ab Hab,
      have Ha := quotient.exact Hab,
      let one : ℤ × P_set := (1, ⟨1, one_P_set⟩),
      have Hloc : @localization.r ℤ _ P_set _ ab one := Ha,
      let Hprop := λ t, ((ab.2 : Zp) * one.1 - one.2 * ab.1) * (t : ℤ) = 0,
      --have H : ∃ t ∈ P_set, Hprop t := Hloc, 
    end }

def h : Zp → ZpZ :=  sorry


end loc_test_3
