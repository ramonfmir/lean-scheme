/-
    Stalk of rings on basis.

    https://stacks.math.columbia.edu/tag/007L
    (just says that the category of rings is a type of algebraic structure)
-/

import to_mathlib.opens
import topology.basic
import sheaves.stalk_on_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

namespace stalk_of_rings_on_standard_basis

variables {α : Type u} [topological_space α] 
variables {B : set (opens α )} {HB : opens.is_basis B}

-- Standard basis. TODO: Move somewhere else?

variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

variables (F : presheaf_of_rings_on_basis α HB) (x : α)

include Bstd

definition stalk_of_rings_on_standard_basis := 
stalk_on_basis F.to_presheaf_on_basis x

section stalk_of_rings_on_standard_basis_is_ring

open stalk_of_rings_on_standard_basis

-- Add.

protected def add_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := Bstd.2 s.BU t.BU,
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s + 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance has_add : has_add (stalk_of_rings_on_standard_basis Bstd F x) := 
{ add := quotient.lift₂ (stalk_of_rings_on_standard_basis.add_aux Bstd F x) $
    begin
      intros a1 a2 b1 b2 H1 H2,
      let F' := F.to_presheaf_on_basis,
      rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
      rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
      have BU1U2 := Bstd.2 BU1 BU2,
      apply quotient.sound,
      use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
      use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      have HresU1' : 
          (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
          (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
      := by rw HresU1,
      have HresU2' :
          (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
          (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
      := by rw HresU2,
      repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
      repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
      repeat { rw ←(presheaf_on_basis.Hcomp' F') },
      rw [HresU1', HresU2'],
    end }

@[simp] lemma has_add.mk : ∀ y z,
  (⟦y⟧ + ⟦z⟧ : stalk_of_rings_on_standard_basis Bstd F x) = 
  (stalk_of_rings_on_standard_basis.add_aux Bstd F x) y z :=
λ y z, rfl

instance add_semigroup : add_semigroup (stalk_of_rings_on_standard_basis Bstd F x) :=
{ add_assoc := 
    begin
      intros a b c,
      refine quotient.induction_on₃ a b c _,
      rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
      have BUVW := Bstd.2 (Bstd.2 BU BV) BW,
      have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
      := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
      apply quotient.sound,
      use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩],
      use [set.subset.refl _, HUVWsub],
      dsimp,
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { erw ←presheaf_on_basis.Hcomp' },
      rw add_assoc,
    end,
  ..stalk_of_rings_on_standard_basis.has_add Bstd F x }

instance add_comm_semigroup : add_comm_semigroup (stalk_of_rings_on_standard_basis Bstd F x) :=
{ add_comm :=
    begin
      intros a b,
      refine quotient.induction_on₂ a b _,
      rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩,
      apply quotient.sound,
      have BUV : U ∩ V ∈ B := Bstd.2 BU BV,
      have HUVUV : U ∩ V ⊆ U ∩ V := λ x HxUV, HxUV,
      have HUVVU : U ∩ V ⊆ V ∩ U := λ x ⟨HxU, HxV⟩, ⟨HxV, HxU⟩,
      use [U ∩ V, BUV, ⟨HxU, HxV⟩, HUVUV, HUVVU],
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      rw add_comm,
    end,
  ..stalk_of_rings_on_standard_basis.add_semigroup Bstd F x }

-- Zero.

protected def zero : stalk_of_rings_on_standard_basis Bstd F x := 
⟦{U := opens.univ, BU := Bstd.1, Hx := trivial, s:= 0}⟧

instance has_zero : has_zero (stalk_of_rings_on_standard_basis Bstd F x) := 
{ zero := stalk_of_rings_on_standard_basis.zero Bstd F x }

instance add_comm_monoid : add_comm_monoid (stalk_of_rings_on_standard_basis Bstd F x) :=
{ zero_add := 
    begin
      intros a,
      refine quotient.induction_on a _,
      rintros ⟨U, BU, HxU, sU⟩,
      apply quotient.sound,
      have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
      use [U, BU, HxU, HUsub, set.subset.refl U],
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
      try { apply_instance },
      rw zero_add,
      refl,
    end,
  add_zero :=
    begin
      intros a,
      refine quotient.induction_on a _,
      rintros ⟨U, BU, HxU, sU⟩,
      apply quotient.sound,
      have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
      use [U, BU, HxU, HUsub, set.subset.refl U],
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      dsimp,
      erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
      try { apply_instance },
      rw add_zero,
      refl,
    end,
  ..stalk_of_rings_on_standard_basis.has_zero Bstd F x,
  ..stalk_of_rings_on_standard_basis.add_comm_semigroup Bstd F x }

-- Neg.

protected def neg_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s, ⟦{U := s.U, BU := s.BU, Hx := s.Hx, s := -s.s}⟧

instance has_neg : has_neg (stalk_of_rings_on_standard_basis Bstd F x) :=
{ neg := quotient.lift (stalk_of_rings_on_standard_basis.neg_aux Bstd F x) $ 
  begin
    intros a b H,
    rcases H with ⟨U, ⟨BU, ⟨HxU, ⟨HUaU, HUbU, HresU⟩⟩⟩⟩,
    apply quotient.sound,
    use [U, BU, HxU, HUaU, HUbU],
    repeat { rw @is_ring_hom.map_neg _ _ _ _ _ (F.res_is_ring_hom _ _ _) },
    rw HresU,
  end }

instance add_comm_group : add_comm_group (stalk_of_rings_on_standard_basis Bstd F x) :=
{ add_left_neg := 
    begin
      intros a,
      refine quotient.induction_on a _,
      rintros ⟨U, BU, HxU, sU⟩,
      apply quotient.sound,
      have HUUU : U ⊆ U ∩ U := λ x HxU, ⟨HxU, HxU⟩,
      have HUuniv : U ⊆ opens.univ := λ x HxU, trivial,
      use [U, BU, HxU, HUUU, HUuniv],
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      erw (is_ring_hom.map_neg ((F.to_presheaf_on_basis).res _ _ _));
      try { apply_instance },
      rw add_left_neg,
      erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
      try { apply_instance },
    end,
  ..stalk_of_rings_on_standard_basis.has_neg Bstd F x,
  ..stalk_of_rings_on_standard_basis.add_comm_monoid Bstd F x, }

-- Mul.

protected def mul_aux : 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis.elem F.to_presheaf_on_basis x → 
stalk_on_basis F.to_presheaf_on_basis x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
BU := Bstd.2 s.BU t.BU,
Hx := ⟨s.Hx, t.Hx⟩, 
s := F.res s.BU _ (set.inter_subset_left _ _) s.s * 
     F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

instance has_mul : has_mul (stalk_of_rings_on_standard_basis Bstd F x) := 
{ mul := quotient.lift₂ (stalk_of_rings_on_standard_basis.mul_aux Bstd F x) $ 
    begin
      intros a1 a2 b1 b2 H1 H2, 
      let F' := F.to_presheaf_on_basis,
      rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
      rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
      have BU1U2 := Bstd.2 BU1 BU2,
      apply quotient.sound,
      use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
      use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      have HresU1' : 
          (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
          (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
      := by rw HresU1,
      have HresU2' :
          (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
          (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
      := by rw HresU2,
      repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
      repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
      repeat { rw ←(presheaf_on_basis.Hcomp' F') },
      rw [HresU1', HresU2'],
    end}

@[simp] lemma has_mul.mk : ∀ y z,
  (⟦y⟧ * ⟦z⟧ : stalk_of_rings_on_standard_basis Bstd F x) = 
  (stalk_of_rings_on_standard_basis.mul_aux Bstd F x) y z :=
λ y z, rfl

instance mul_semigroup : semigroup (stalk_of_rings_on_standard_basis Bstd F x) :=
{ mul_assoc := 
    begin
      intros a b c,
      refine quotient.induction_on₃ a b c _,
      rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
      have BUVW := Bstd.2 (Bstd.2 BU BV) BW,
      have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
      := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
      apply quotient.sound,
      use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩],
      use [set.subset.refl _, HUVWsub],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      rw mul_assoc,
    end,
  ..stalk_of_rings_on_standard_basis.has_mul Bstd F x }

instance mul_comm_semigroup : comm_semigroup (stalk_of_rings_on_standard_basis Bstd F x) :=
{ mul_comm := 
    begin
      intros a b,
      refine quotient.induction_on₂ a b _,
      rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩,
      apply quotient.sound,
      have BUV : U ∩ V ∈ B := Bstd.2 BU BV,
      have HUVUV : U ∩ V ⊆ U ∩ V := λ x HxUV, HxUV,
      have HUVVU : U ∩ V ⊆ V ∩ U := λ x ⟨HxU, HxV⟩, ⟨HxV, HxU⟩,
      use [U ∩ V, BUV, ⟨HxU, HxV⟩, HUVUV, HUVVU],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      rw mul_comm,
    end,
  ..stalk_of_rings_on_standard_basis.mul_semigroup Bstd F x }

-- One.

protected def one : stalk_of_rings_on_standard_basis Bstd F x := 
⟦{U := opens.univ, BU := Bstd.1, Hx := trivial, s:= 1}⟧

instance has_one : has_one (stalk_of_rings_on_standard_basis Bstd F x) := 
{ one := stalk_of_rings_on_standard_basis.one Bstd F x }

instance mul_comm_monoid : comm_monoid (stalk_of_rings_on_standard_basis Bstd F x) :=
{ one_mul := 
    begin
      intros a,
      refine quotient.induction_on a _,
      rintros ⟨U, BU, HxU, sU⟩,
      apply quotient.sound,
      have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
      use [U, BU, HxU, HUsub, set.subset.refl U],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      erw (is_ring_hom.map_one ((F.to_presheaf_on_basis).res _ _ _));
      try { apply_instance },
      rw one_mul,
      refl,
    end,
  mul_one := 
    begin
      intros a,
      refine quotient.induction_on a _,
      rintros ⟨U, BU, HxU, sU⟩,
      apply quotient.sound,
      have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
      use [U, BU, HxU, HUsub, set.subset.refl U],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      dsimp,
      erw (is_ring_hom.map_one ((F.to_presheaf_on_basis).res _ _ _));
      try { apply_instance },
      rw mul_one,
      refl,
    end,
  ..stalk_of_rings_on_standard_basis.has_one Bstd F x,
  ..stalk_of_rings_on_standard_basis.mul_comm_semigroup Bstd F x }

-- Stalks of rings on standard basis are rings.

instance comm_ring : comm_ring (stalk_of_rings_on_standard_basis Bstd F x) :=
{ left_distrib := 
    begin
      intros a b c,
      refine quotient.induction_on₃ a b c _,
      rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
      have BUVW := Bstd.2 (Bstd.2 BU BV) BW,
      have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
      := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
      have HUVWsub2 : U ∩ V ∩ W ⊆ U ∩ V ∩ (U ∩ W)
      := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨⟨HxU, HxV⟩, ⟨HxU, HxW⟩⟩,
      apply quotient.sound,
      use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWsub, HUVWsub2],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      rw mul_add,
    end,
  right_distrib := 
    begin
      intros a b c,
      refine quotient.induction_on₃ a b c _,
      rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
      have BUVW := Bstd.2 (Bstd.2 BU BV) BW,
      have HUVWrfl : U ∩ V ∩ W ⊆ U ∩ V ∩ W := λ x Hx, Hx,
      have HUVWsub : U ∩ V ∩ W ⊆ U ∩ W ∩ (V ∩ W)
      := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨⟨HxU, HxW⟩, ⟨HxV, HxW⟩⟩,
      apply quotient.sound,
      use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWrfl, HUVWsub],
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
      repeat { rw (F.res_is_ring_hom _ _ _).map_add },
      repeat { rw ←presheaf_on_basis.Hcomp' },
      rw add_mul,
    end,
  ..stalk_of_rings_on_standard_basis.add_comm_group Bstd F x,
  ..stalk_of_rings_on_standard_basis.mul_comm_monoid Bstd F x
}

end stalk_of_rings_on_standard_basis_is_ring

end stalk_of_rings_on_standard_basis
