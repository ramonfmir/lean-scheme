/-
  Presheaf of rings extension.

  https://stacks.math.columbia.edu/tag/009N
-/

import to_mathlib.opens
import sheaves.covering.covering
import sheaves.presheaf_of_rings
import sheaves.presheaf_of_rings_on_basis
import sheaves.stalk_of_rings_on_standard_basis

universes u v w

open topological_space
open lattice
open covering
open stalk_of_rings_on_standard_basis.

section presheaf_of_rings_extension

variables {α : Type u} [topological_space α]
variables {B : set (opens α)} {HB : opens.is_basis B}
variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

variables (F : presheaf_of_rings_on_basis α HB) (U : opens α) 

include Bstd

section presheaf_of_rings_on_basis_extension_is_ring

@[reducible] def Fext :=
{ s : Π (x ∈ U), stalk_of_rings_on_standard_basis Bstd F x //
  ∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F.to_presheaf_on_basis BV),
  ∀ (y ∈ U ∩ V), s y = λ _, ⟦{U := V, BU := BV, Hx := H.2, s := σ}⟧ }

-- Add.

private def Fext_add_aux (x : α) 
: stalk_of_rings_on_standard_basis Bstd F x
→ stalk_of_rings_on_standard_basis Bstd F x
→ stalk_of_rings_on_standard_basis Bstd F x :=
(stalk_of_rings_on_standard_basis.has_add Bstd F x).add

private def Fext_add : Fext Bstd F U → Fext Bstd F U → Fext Bstd F U 
:= λ ⟨s₁, Hs₁⟩ ⟨s₂, Hs₂⟩, 
  ⟨λ x Hx, (Fext_add_aux Bstd F x) (s₁ x Hx) (s₂ x Hx),
  begin
    intros x Hx,
    replace Hs₁ := Hs₁ x Hx,
    replace Hs₂ := Hs₂ x Hx,
    rcases Hs₁ with ⟨V₁, BV₁, HxV₁, σ₁, Hs₁⟩,
    rcases Hs₂ with ⟨V₂, BV₂, HxV₂, σ₂, Hs₂⟩,
    use [V₁ ∩ V₂, Bstd.2 BV₁ BV₂, ⟨HxV₁, HxV₂⟩],
    let σ₁' := F.res BV₁ (Bstd.2 BV₁ BV₂) (set.inter_subset_left _ _) σ₁,
    let σ₂' := F.res BV₂ (Bstd.2 BV₁ BV₂) (set.inter_subset_right _ _) σ₂,
    use [σ₁' + σ₂'],
    rintros y ⟨HyU, ⟨HyV₁, HyV₂⟩⟩,
    apply funext,
    intros Hy,
    replace Hs₁ := Hs₁ y ⟨HyU, HyV₁⟩,
    replace Hs₂ := Hs₂ y ⟨HyU, HyV₂⟩,
    rw Hs₁,
    rw Hs₂,
    refl,
  end⟩

instance Fext_has_add : has_add (Fext Bstd F U) := 
{ add := Fext_add Bstd F U }

@[simp] lemma Fext_add.eq (x : α) (Hx : x ∈ U) 
: ∀ (a b : Fext Bstd F U), (a + b).val x Hx = (a.val x Hx) + (b.val x Hx) :=
λ ⟨s₁, Hs₁⟩ ⟨s₂, Hs₂⟩, rfl

instance Fext_add_semigroup : add_semigroup (Fext Bstd F U) :=
{ add_assoc := λ a b c, subtype.eq $ funext $ λ x, funext $ λ HxU, by simp,
  ..Fext_has_add Bstd F U }

instance Fext_add_comm_semigroup : add_comm_semigroup (Fext Bstd F U) :=
{ add_comm := λ a b, subtype.eq $ funext $ λ x, funext $ λ HxU, by simp,
  ..Fext_add_semigroup Bstd F U }

-- Zero.

private def Fext_zero : Fext Bstd F U := 
⟨λ x Hx, (stalk_of_rings_on_standard_basis.has_zero Bstd F x).zero, 
λ x Hx, ⟨opens.univ, Bstd.1, trivial, 0, (λ y Hy, funext $ λ HyU, rfl)⟩⟩

instance Fext_has_zero : has_zero (Fext Bstd F U) := 
{ zero := Fext_zero Bstd F U }

@[simp] lemma Fext_zero.eq (x : α) (Hx : x ∈ U) 
: (0 : Fext Bstd F U).val x Hx = (stalk_of_rings_on_standard_basis.has_zero Bstd F x).zero := rfl

instance Fext_add_comm_monoid : add_comm_monoid (Fext Bstd F U) :=
{ zero_add := λ a, subtype.eq $ funext $ λ x, funext $ λ HxU, by simp,
  add_zero := λ a, subtype.eq $ funext $ λ x, funext $ λ HxU, by simp,
  ..Fext_has_zero Bstd F U,
  ..Fext_add_comm_semigroup Bstd F U, }

-- Neg.

private def Fext_neg_aux (x : α) 
: stalk_of_rings_on_standard_basis Bstd F x
→ stalk_of_rings_on_standard_basis Bstd F x :=
(stalk_of_rings_on_standard_basis.has_neg Bstd F x).neg

private def Fext_neg : Fext Bstd F U → Fext Bstd F U :=
λ ⟨s, Hs⟩, 
  ⟨λ x Hx, (Fext_neg_aux Bstd F x) (s x Hx),
  begin
    intros x Hx,
    replace Hs := Hs x Hx,
    rcases Hs with ⟨V, BV, HxV, σ, Hs⟩,
    use [V, BV, HxV, -σ],
    rintros y ⟨HyU, HyV⟩,
    apply funext,
    intros Hy,
    replace Hs := Hs y ⟨HyU, HyV⟩,
    rw Hs,
    refl,
  end⟩

instance Fext_has_neg : has_neg (Fext Bstd F U) :=
{ neg := Fext_neg Bstd F U, }

@[simp] lemma Fext_neg.eq (x : α) (Hx : x ∈ U) 
: ∀ (a : Fext Bstd F U), (-a).val x Hx = -(a.val x Hx) :=
λ ⟨s, Hs⟩, rfl

instance Fext_add_comm_group : add_comm_group (Fext Bstd F U) :=
{ add_left_neg := λ a, subtype.eq $ funext $ λ x, funext $ λ HxU, by simp,
  ..Fext_has_neg Bstd F U,
  ..Fext_add_comm_monoid Bstd F U, }

-- Mul.

private def Fext_mul_aux (x : α) 
: stalk_of_rings_on_standard_basis Bstd F x
→ stalk_of_rings_on_standard_basis Bstd F x
→ stalk_of_rings_on_standard_basis Bstd F x :=
(stalk_of_rings_on_standard_basis.has_mul Bstd F x).mul

private def Fext_mul : Fext Bstd F U → Fext Bstd F U → Fext Bstd F U 
:= λ ⟨s₁, Hs₁⟩ ⟨s₂, Hs₂⟩, 
  ⟨λ x Hx, (Fext_mul_aux Bstd F x) (s₁ x Hx) (s₂ x Hx),
  begin
    intros x Hx,
    replace Hs₁ := Hs₁ x Hx,
    replace Hs₂ := Hs₂ x Hx,
    rcases Hs₁ with ⟨V₁, BV₁, HxV₁, σ₁, Hs₁⟩,
    rcases Hs₂ with ⟨V₂, BV₂, HxV₂, σ₂, Hs₂⟩,
    use [V₁ ∩ V₂, Bstd.2 BV₁ BV₂, ⟨HxV₁, HxV₂⟩],
    let σ₁' := F.res BV₁ (Bstd.2 BV₁ BV₂) (set.inter_subset_left _ _) σ₁,
    let σ₂' := F.res BV₂ (Bstd.2 BV₁ BV₂) (set.inter_subset_right _ _) σ₂,
    use [σ₁' * σ₂'],
    rintros y ⟨HyU, ⟨HyV₁, HyV₂⟩⟩,
    apply funext,
    intros Hy,
    replace Hs₁ := Hs₁ y ⟨HyU, HyV₁⟩,
    replace Hs₂ := Hs₂ y ⟨HyU, HyV₂⟩,
    rw Hs₁,
    rw Hs₂,
    refl,
  end⟩

instance Fext_has_mul : has_mul (Fext Bstd F U) :=
{ mul := Fext_mul Bstd F U }

@[simp] lemma Fext_mul.eq (x : α) (Hx : x ∈ U) 
: ∀ (a b : Fext Bstd F U), (a * b).val x Hx = (a.val x Hx) * (b.val x Hx) :=
λ ⟨s₁, Hs₁⟩ ⟨s₂, Hs₂⟩, rfl

instance Fext_mul_semigroup : semigroup (Fext Bstd F U) :=
{ mul_assoc := λ a b c, subtype.eq $ funext $ λ x, funext $ λ HxU,
  begin
    simp,
    apply (stalk_of_rings_on_standard_basis.mul_semigroup Bstd F x).mul_assoc,
  end,
  ..Fext_has_mul Bstd F U, }

instance Fext_mul_comm_semigroup : comm_semigroup (Fext Bstd F U) :=
{ mul_comm := λ a b, subtype.eq $ funext $ λ x, funext $ λ HxU,
    begin
      simp,
      apply (stalk_of_rings_on_standard_basis.mul_comm_semigroup Bstd F x).mul_comm,
    end,
  ..Fext_mul_semigroup Bstd F U, }

-- One.

private def Fext_one : Fext Bstd F U  := 
⟨λ x Hx, (stalk_of_rings_on_standard_basis.has_one Bstd F x).one, 
λ x Hx, ⟨opens.univ, Bstd.1, trivial, 1, (λ y Hy, funext $ λ HyU, rfl)⟩⟩

instance Fext_has_one : has_one (Fext Bstd F U) := 
{ one := Fext_one Bstd F U }

instance Fext_mul_comm_monoid : comm_monoid (Fext Bstd F U) :=
{ one_mul := λ a, subtype.eq $ funext $ λ x, funext $ λ HxU,
    begin
      simp,
      apply (stalk_of_rings_on_standard_basis.mul_comm_monoid Bstd F x).one_mul,
    end,
  mul_one := λ a, subtype.eq $ funext $ λ x, funext $ λ HxU,
    begin
      simp,
      apply (stalk_of_rings_on_standard_basis.mul_comm_monoid Bstd F x).mul_one,
    end,
  ..Fext_has_one Bstd F U,
  ..Fext_mul_comm_semigroup Bstd F U, }

-- Ring

instance Fext_comm_ring : comm_ring (Fext Bstd F U) :=
{ left_distrib := λ a b c, subtype.eq $ funext $ λ x, funext $ λ HxU,
    begin
      rw Fext_add.eq,
      repeat { rw Fext_mul.eq, },
      rw Fext_add.eq,
      eapply (stalk_of_rings_on_standard_basis.comm_ring Bstd F x).left_distrib,
    end,
  right_distrib := λ a b c, subtype.eq $ funext $ λ x, funext $ λ HxU,
    begin
      rw Fext_add.eq,
      repeat { rw Fext_mul.eq, },
      rw Fext_add.eq,
      eapply (stalk_of_rings_on_standard_basis.comm_ring Bstd F x).right_distrib,
    end,
  ..Fext_add_comm_group Bstd F U,
  ..Fext_mul_comm_monoid Bstd F U, }

end presheaf_of_rings_on_basis_extension_is_ring

-- F defined in the whole space to F defined on the basis.

def presheaf_of_rings_to_presheaf_of_rings_on_basis 
(F : presheaf_of_rings α) : presheaf_of_rings_on_basis α HB :=
{ F := λ U BU, F U,
  res := λ U V BU BV HVU, F.res U V HVU,
  Hid := λ U BU, F.Hid U,
  Hcomp := λ U V W BU BV BW, F.Hcomp U V W,
  Fring := λ U BU, F.Fring U,
  res_is_ring_hom := λ U V BU BV HVU, F.res_is_ring_hom U V HVU, }

-- F defined on the bases extended to the whole space.

def presheaf_of_rings_extension
(F : presheaf_of_rings_on_basis α HB) : presheaf_of_rings α :=
{ F := λ U, {s : Π (x ∈ U), stalk_on_basis F.to_presheaf_on_basis x //
        ∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F.to_presheaf_on_basis BV),
        ∀ (y ∈ U ∩ V), s y = λ _, ⟦{U := V, BU := BV, Hx := H.2, s := σ}⟧},
  res := λ U W HWU FU, 
        { val := λ x HxW, (FU.val x $ HWU HxW),
          property := λ x HxW,
            begin
              rcases (FU.property x (HWU HxW)) with ⟨V, ⟨BV, ⟨HxV, ⟨σ, HFV⟩⟩⟩⟩,
              use [V, BV, HxV, σ],
              rintros y ⟨HyW, HyV⟩,
              rw (HFV y ⟨HWU HyW, HyV⟩),
            end },
  Hid := λ U, funext $ λ x, subtype.eq rfl,
  Hcomp := λ U V W HWV HVU, funext $ λ x, subtype.eq rfl,
  Fring := λ U, Fext_comm_ring Bstd F U,
  res_is_ring_hom := λ U V HVU,
    { map_one := rfl,
      map_mul := λ x y, subtype.eq $ funext $ λ x, funext $ λ Hx,
        begin
          erw Fext_mul.eq,
          refl,
        end,
      map_add := λ x y, subtype.eq $ funext $ λ x, funext $ λ Hx,
        begin
          erw Fext_add.eq,
          refl,
        end, } }

notation F `ᵣₑₓₜ`:1 Bstd := presheaf_of_rings_extension Bstd F

end presheaf_of_rings_extension
