/-
  Presheaf (of types) extension.

  https://stacks.math.columbia.edu/tag/009N
-/

import topology.opens
import sheaves.presheaf
import sheaves.presheaf_on_basis
import sheaves.stalk_on_basis

universe u 

open topological_space

section presheaf_extension

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α)} {HB : opens.is_basis B}

-- F defined in the whole space to F defined on the basis.

def presheaf_to_presheaf_on_basis 
(F : presheaf α) : presheaf_on_basis α HB :=
{ F := λ U BU, F U,
  res := λ U V BU BV HVU, F.res U V HVU,
  Hid := λ U BU, F.Hid U,
  Hcomp := λ U V W BU BV BW, F.Hcomp U V W }

-- F defined on the bases extended to the whole space.

@[reducible] def presheaf_on_basis_to_presheaf
(F : presheaf_on_basis α HB) : presheaf α :=
{ F := λ U, {s : Π (x ∈ U), stalk_on_basis F x //
        ∀ (x ∈ U), ∃ (V) (BV : V ∈ B) (Hx : x ∈ V) (σ : F BV),
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
  Hcomp := λ U V W HWV HVU, funext $ λ x, subtype.eq rfl}

notation F `ₑₓₜ`:1 := presheaf_on_basis_to_presheaf F

end presheaf_extension
