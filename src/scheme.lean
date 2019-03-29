import topology.basic
import sheaves.locally_ringed_space
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.spec_locally_ringed_space


open topological_space

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v

section restrictions

variables {X : Type u} [HX : topological_space X] (U : opens X)

include HX

def f : {x // x ∈ U} → X := λ x, x.val

lemma f_cts : continuous (f U) :=
begin
  intros S OS,
  rw is_open_induced_iff,
  use S,
  split,
  { exact OS, },
  { simp [f], }
end

lemma f_open_map : is_open_map (f U) :=
begin
  intros S OS,
  rw is_open_induced_iff at OS,
  rcases OS with ⟨T, ⟨OT, HT⟩⟩,
  dsimp [f],
  rw ←HT,
  rw subtype.image_preimage_val,
  apply HX.is_open_inter,
  { exact OT, },
  { exact U.2, }
end

def f_op : opens {x // x ∈ U} → opens X 
:= λ V, ⟨subtype.val '' V.1, f_open_map U V V.2⟩


@[simp] lemma f_op.val : ∀ {V}, (f_op U V).val = subtype.val '' V.val := λ V, rfl

lemma f_op.mono : ∀ {V W}, W ⊆ V → (f_op U W) ⊆ (f_op U V) := 
λ V W H x ⟨y, ⟨Hy, Hx⟩⟩, ⟨y, ⟨H Hy, Hx⟩⟩

@[simp] lemma f_op.inter
: ∀ {V W}, (f_op U (V ∩ W)) = (f_op U V) ∩ (f_op U W) :=
begin
  intros V W,
  apply subtype.eq,
  apply set.ext,
  intros x,
  split,
  { intros Hx,
    rcases Hx with ⟨y, ⟨⟨HyV, HyW⟩, Hy⟩⟩,
    exact ⟨⟨y, ⟨HyV, Hy⟩⟩, ⟨y, ⟨HyW, Hy⟩⟩⟩, },
  { intros Hx,
    rcases Hx with ⟨⟨y, ⟨HyV, Hy⟩⟩, ⟨z, ⟨HzW, Hz⟩⟩⟩,
    have : y = z,
      apply subtype.eq,
      rw [Hy, Hz],
    rw ←this at HzW,
    exact ⟨y, ⟨⟨HyV, HzW⟩, Hy⟩⟩, }
end

-- Restrict sheaf.

def res_presheaf (OX : presheaf_of_rings X) 
: presheaf_of_rings {x // x ∈ U} :=
{ F := λ V, OX.F (f_op U V), 
  res := λ V W H, OX.res (f_op U V) (f_op U W) (f_op.mono U H),
  Hid := λ V, by apply OX.Hid,
  Hcomp := λ V1 V2 V3 HV3V2 HV2V1, by apply OX.Hcomp,
  Fring := λ U, by apply OX.Fring,
  res_is_ring_hom := λ V W HWV, by apply OX.res_is_ring_hom, }

-- Covering of res...

@[reducible] def f_op.covering {V : opens U} (OC : covering V) 
: covering (f_op U V) :=
{ Uis := f_op U ∘ OC.Uis,
  Hcov := 
    begin
      have HV := OC.Hcov,
      apply subtype.eq,
      simp,
      apply set.ext,
      intros x,
      split,
      { intros Hx,
        rcases Hx with ⟨Ui, ⟨⟨OUi, ⟨HUi, HOUi⟩⟩, HxUi⟩⟩,
        rcases HUi with ⟨i, HUi⟩,
        simp at HUi,
        rw ←HUi at HOUi,
        simp at HOUi,
        rw ←HOUi at HxUi,
        rw ←HV,
        rcases HxUi with ⟨y, ⟨HyUi, Hy⟩⟩,
        use y,
        split,
        { use [(OC.Uis i).val],
          have H : (OC.Uis i).val ∈ subtype.val '' set.range (OC.Uis),
            simp,
            exact ⟨(OC.Uis i).2, ⟨i, rfl⟩⟩,
          use H,
          exact HyUi, },
        { exact Hy, } },
      { intros Hx,
        rw ←HV at Hx,
        rcases Hx with ⟨y, ⟨Hy, Hyval⟩⟩,
        rcases Hy with ⟨Uival, ⟨HUi, HxUi⟩⟩,
        rcases HUi with ⟨Ui, ⟨HUi, HUival⟩⟩,
        rcases HUi with ⟨i, HUi⟩,
        use [subtype.val '' Uival],
        have H : subtype.val '' Uival ∈ subtype.val '' set.range (f_op U ∘ OC.Uis),
          simp,
          have := (f_op U Ui).2,
          simp at this,
          rw HUival at this,
          use this,
          use i,
          rw HUi,
          apply subtype.eq,
          simp,
          erw ←HUival,
        use H,
        simp,
        rw ←Hyval,
        use y.2,
        simp,
        exact HxUi, }
    end }


def res_sheaf (OX : sheaf_of_rings X)
: sheaf_of_rings {x // x ∈ U} :=
{ F := res_presheaf U OX.F,
  locality := 
    begin
      intros V OC s t H,
      simp at *,
      exact (OX.locality (f_op.covering U OC) s t H),
    end,
  gluing := 
    begin
      intros V OC s H,
      have := (OX.gluing (f_op.covering U OC) s),
      dsimp [f_op.covering] at this,
      apply this,
      intros j k,
      replace H := H j k,
      simp [res_to_inter_left] at *, 
      simp [res_to_inter_right] at *, 
      convert H,
      { simp [coe_fn],
        simp [has_coe_to_fun.coe],
        apply congr_arg,
        dsimp,
        apply subtype.eq,
        simp,
        repeat { rw subtype.val_image, },
        rw set.inter_def,
        rw set.inter_def,
        simp,
        apply set.ext,
        intros x,
        split,
        { rintros ⟨⟨A, B⟩, ⟨C, D⟩⟩,
          exact ⟨A, B, D⟩, },
        { rintros ⟨A, B, C⟩,
          exact ⟨⟨A, B⟩, ⟨A, C⟩⟩, } }, 
      rw f_op.inter,
      rw f_op.inter,
    end, }

def res (OX : locally_ringed_space X)
: locally_ringed_space U :=
begin
  sorry,
end

end restrictions

-- Almost!

structure scheme (α : Type u) [topological_space α] :=
(carrier    : locally_ringed_space α)
(Haffinecov : 
  ∀ x, ∃ U : opens α, 
      x ∈ U 
    ∧ ∃ R [comm_ring R], 
      (nonempty ((res_presheaf U carrier.O.F) ≅ (structure_presheaf R))))
  
