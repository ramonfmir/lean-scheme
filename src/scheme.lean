import topology.basic
import spectrum_of_a_ring.zariski_topology
import sheaves.locally_ringed_space
import tactic.find

open topological_space

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v

-- Subspace topology

def res_opens {X : Type u} [HX : topological_space X] (U : opens X) 
: opens U → opens X :=
begin
  intros V,
  exact ⟨(subtype.val '' V.val),
  begin 
    rcases V with ⟨V, OV⟩,
    rw is_open_induced_iff at OV,
    rcases (classical.indefinite_description _ OV) with ⟨t, ⟨Ht, HV⟩⟩,
    simp,
    rw ←HV,
    rw subtype.image_preimage_val,
    apply HX.is_open_inter,
    { exact Ht, },
    { exact U.2, }
  end⟩
end

@[simp] lemma res_opens.val {X : Type u} [HX : topological_space X] (U : opens X) (V : opens U)
: (res_opens U V).val = subtype.val '' V.val := rfl

instance {X : Type u} [HX : topological_space X] {U : opens X} : has_lift_t (opens U) (opens X) := 
⟨res_opens U⟩

lemma res_opens.mono {X : Type u} [HX : topological_space X] (U : opens X)
: ∀ {V W}, W ⊆ V → (res_opens U W) ⊆ (res_opens U V) :=
begin
  intros V W HWV x Hx,
  simp [res_opens.val] at *,
  cases Hx with Hx HxW,
  existsi (Hx),
  exact (HWV HxW),
end

lemma res_opens.le {X : Type u} [HX : topological_space X] (U : opens X)
: ∀ {V W}, (res_opens U W) ⊆ (res_opens U V) → W ⊆ V :=
begin
  intros V W HWV x Hx,
  replace HWV : (res_opens U W).val ⊆ (res_opens U V).val := HWV,
  simp at HWV,
  have Hxval : x.val ∈ subtype.val '' W.val,
    simp,
    exact Hx,
  replace Hxval := HWV Hxval,
  rcases Hxval with ⟨y, ⟨Hx, Hy⟩⟩,
  have : x = y := subtype.eq Hy.symm,
  rw this,
  exact Hx,
end

lemma res_opens.subset_eq {X : Type u} [HX : topological_space X] (U : opens X)
: ∀ {V W}, (res_opens U W) ⊆ (res_opens U V) ↔ W ⊆ V :=
λ V W,
⟨res_opens.le U, res_opens.mono U⟩

lemma res_opens.inter {X : Type u} [HX : topological_space X] (U : opens X)
: ∀ {V W}, (res_opens U (V ∩ W)) = (res_opens U V) ∩ (res_opens U W) :=
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

#check res_opens.inter

@[reducible] def res_opens.covering {X : Type u} [HX : topological_space X] (U : opens X) 
{V : opens U} (OC : covering V) 
: covering (res_opens U V) :=
{ Uis := res_opens U ∘ OC.Uis,
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
        have H : subtype.val '' Uival ∈ subtype.val '' set.range (res_opens U ∘ OC.Uis),
          simp,
          have := (res_opens U Ui).2,
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


-- Restrict sheaf.

def res_presheaf {X : Type u} [topological_space X] (OX : presheaf_of_rings X) (U : opens X) 
: presheaf_of_rings U :=
{ F := λ V, OX.F (res_opens U V),
  res := λ V W HWV, OX.res (res_opens U V) (res_opens U W) (res_opens.mono U HWV),
  Hid := λ V, by apply OX.Hid,
  Hcomp := λ V1 V2 V3 HV3V2 HV2V1, by apply OX.Hcomp,
  Fring := λ U, by apply OX.Fring,
  res_is_ring_hom := λ V W HWV, by apply OX.res_is_ring_hom, }

-- Covering of res...

set_option trace.check true

def res_sheaf {X : Type u} [topological_space X] (OX : sheaf_of_rings X) (U : opens X) 
: sheaf_of_rings U :=
{ F := res_presheaf OX.F U,
  locality := 
    begin
      intros V OC s t H,
      simp at *,
      exact (OX.locality (res_opens.covering U OC) s t H),
    end,
  gluing := 
    begin
      intros V OC s H,
      simp at *,
      have := (OX.gluing (res_opens.covering U OC) s),
      dsimp [res_opens.covering] at this,
      dsimp at H,
      apply this,
      intros j k,
      replace H := H j k,
      simp [res_to_inter_right] at *,
      simp [res_to_inter_left] at *,
      --dsimp [res_opens.mono] at *,
      have := (@res_opens.inter _ _ U (OC.Uis j) (OC.Uis k)),
      have : ((OX.F).to_presheaf).res (res_opens U (OC.Uis j)) (res_opens U (OC.Uis j) ∩ res_opens U (OC.Uis k)) _ (s j)
      = ((OX.F).to_presheaf).res (res_opens U (OC.Uis j)) (res_opens U (OC.Uis j ∩ OC.Uis k)) _ (s j),
      --erw this at H,
      --exact H,
      sorry,
    end, }

def res {X : Type u} [topological_space X] (OX : locally_ringed_space X) (U : opens X) 
: locally_ringed_space U :=
begin
  sorry,
end

structure scheme (X : Type u) [topological_space X] :=
(carrier    : locally_ringed_space X)
(Haffinecov : 
  ∀ x, ∃ U : opens X, 
      x ∈ U 
    ∧ ∃ R [comm_ring R] (OSpecR : locally_ringed_space (Spec R)), 
      (res carrier U) ≅ OSpecR)
