import Kenny.sandbox

universes u v w u₁ v₁ w₁

namespace ulift

variables (X : Type u) [topological_space X]

instance : topological_space (ulift.{v} X) :=
topological_space.coinduced ulift.up _inst_1

end ulift

theorem continuous_up {X : Type u} [topological_space X] : continuous (ulift.up : X → ulift.{v} X) :=
λ U, id

theorem continuous_down {X : Type u} [topological_space X] : continuous (ulift.down : ulift.{v} X → X) :=
λ U, id

structure open_subspace (X : Type u) [topological_space X] :=
(U : Type v)
[top : topological_space U]
(inc : U → X)
(inj : function.injective inc)
(cont : continuous inc)
(op : ∀ {V : set U}, is_open V → is_open (inc '' V))
attribute [instance] open_subspace.top

namespace open_subspace

variables (X : Type u) [topological_space X]

instance : has_coe_to_sort (open_subspace X) :=
⟨_, open_subspace.U⟩

instance (U : open_subspace X) : topological_space U :=
U.top

def of_set (U : set X) (HU : is_open U) : open_subspace.{u u} X :=
{ U := U,
  inc := subtype.val,
  inj := subtype.val_injective,
  cont := continuous_induced_dom,
  op := λ V ⟨S, HS, HSV⟩, by rw [← HSV, subtype.image_preimage_val]; exact is_open_inter HS HU }

protected def ulift (U : open_subspace X) : open_subspace X :=
{ U := ulift U,
  inc := λ x, U.inc x.down,
  inj := function.injective_comp U.inj $ function.injective_of_left_inverse $ ulift.up_down,
  cont := U.cont.comp continuous_down,
  op := λ V HV, by rw [set.image_comp, set.image_eq_preimage_of_inverse ulift.up_down ulift.down_up];
    exact U.op (continuous_up _ HV) }

-- instance : has_inter (open_subspace X) :=
-- ⟨λ U V,
-- { U := { p : U × V // U.inc p.1 = V.inc p.2 },
--   inc := λ p, U.inc p.1.1,
--   inj := λ p q H, subtype.eq $ prod.ext (U.inj H) $ V.inj $
--     calc  V.inc p.1.2
--         = U.inc p.1.1 : p.2.symm
--     ... = U.inc q.1.1 : H
--     ... = V.inc q.1.2 : q.2,
--   cont := continuous.comp (continuous.comp continuous_induced_dom continuous_fst) U.cont,
--   op := λ W HW, by rw set.image_comp; exact U.op _ }⟩

end open_subspace

namespace gluing_data

protected structure topological_space :=
(left : Type u)
(right : Type v)
[topl : topological_space left]
[topr : topological_space right]
(osl : open_subspace left)
(osr : open_subspace right)
(maplr : osl → osr)
(maprl : osr → osl)
(contlr : continuous maplr)
(contrl : continuous maprl)
(lrl : ∀ x, maprl (maplr x) = x)
(rlr : ∀ x, maplr (maprl x) = x)
attribute [instance] gluing_data.topological_space.topl gluing_data.topological_space.topr

end gluing_data

namespace gluing

inductive topological_space.r (d : gluing_data.topological_space) :
  d.left ⊕ d.right → d.left ⊕ d.right → Prop
| refl : ∀ p, topological_space.r p p
| inlr : ∀ p : d.osl, topological_space.r (sum.inl (d.osl.inc p)) (sum.inr (d.osr.inc (d.maplr p)))
| inrl : ∀ p : d.osr, topological_space.r (sum.inr (d.osr.inc p)) (sum.inl (d.osl.inc (d.maprl p)))
attribute [refl] topological_space.r.refl

instance topological_space.setoid (d : gluing_data.topological_space) :
  setoid (d.left ⊕ d.right) :=
{ r := topological_space.r d,
  iseqv := ⟨topological_space.r.refl,
  begin
    rintros (p|p) (q|q) h,
    { cases h, refl },
    { cases h with _ p, convert topological_space.r.inrl (d.maplr p), rw d.lrl },
    { cases h with _ _ p, convert topological_space.r.inlr (d.maprl p), rw d.rlr },
    { cases h, refl }
  end,
  begin
    rintros (p|p) (q|q) r h1 h2,
    { cases h1, exact h2 },
    { cases h2,
      case gluing.topological_space.r.refl { exact h1 },
      case gluing.topological_space.r.inrl : q {
        generalize_hyp hr : d.osr.inc q = r at h1, cases h1 with _ r,
        replace hr := d.osr.inj hr, subst hr, rw d.lrl } },
    { cases h2,
      case gluing.topological_space.r.refl { exact h1 },
      case gluing.topological_space.r.inlr : q {
        generalize_hyp hr : d.osl.inc q = r at h1, cases h1 with _ r,
        replace hr := d.osl.inj hr, subst hr, rw d.rlr } },
    { cases h1, exact h2 }
  end⟩ }

protected def topological_space (d : gluing_data.topological_space) : Type* :=
quotient $ topological_space.setoid d

end gluing

namespace projective_line

end projective_line
