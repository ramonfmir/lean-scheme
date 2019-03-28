import preliminaries.opens
import sheaves.presheaf_of_rings
import sheaves.presheaf_of_rings_on_basis
import sheaves.sheaf_on_basis
import sheaves.stalk_of_rings_on_standard_basis

universes u v w

open topological_space
open lattice
open covering

section sheaf_of_ring_on_basis

variables {α : Type u} [topological_space α]
variables {B : set (opens α)} {HB : opens.is_basis B}
variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

variables (F : presheaf_of_rings_on_basis α HB) (U : opens α) 

def Fext :=
{ s : Π (x ∈ U), stalk_of_rings_on_standard_basis F x //
  ∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F.to_presheaf_on_basis BV),
  ∀ (y ∈ U ∩ V), s y = λ _, ⟦{U := V, BU := BV, Hx := H.2, s := σ}⟧ }

-- Zero.

private def Fext_zero : Fext F U := 
⟨λ x Hx, (stalk_of_rings_has_zero Bstd F x).zero, 
begin
  intros x Hx,
  use [opens.univ, Bstd.1, trivial, 0],
  intros y Hy,
  apply funext,
  intros HyU,
  refl,
end⟩

instance Fext_has_zero : has_zero (Fext F U) := 
{ zero := Fext_zero Bstd F U }

-- One.

private def Fext_one : Fext F U  := 
⟨λ x Hx, (stalk_of_rings_has_one Bstd F x).one, 
begin
  intros x Hx,
  use [opens.univ, Bstd.1, trivial, 1],
  intros y Hy,
  apply funext,
  intros HyU,
  refl,  
end⟩

instance Fext_has_one : has_one (Fext F U) := 
{ one := Fext_one Bstd F U }

-- Add.

include Bstd

private def Fext_add_aux (x : α) 
: stalk_of_rings_on_standard_basis F x
→ stalk_of_rings_on_standard_basis F x
→ stalk_of_rings_on_standard_basis F x :=
(stalk_of_rings_has_add Bstd F x).add

private def Fext_add : Fext F U → Fext F U → Fext F U := λ ⟨s₁, Hs₁⟩ ⟨s₂, Hs₂⟩, 
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

--

instance Fext_is_ring (F : presheaf_of_rings_on_basis α HB) (U : opens α) : comm_ring (Fext F U) :=
sorry

definition presheaf_of_rings_on_basis_to_presheaf_of_rings
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
  Fring := 
    begin
      intros U,
      simp,
      sorry,
    end,
  res_is_ring_hom := sorry, }

end sheaf_of_ring_on_basis
