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

def res_sheaf {X : Type u} [topological_space X] (OX : sheaf_of_rings X) (U : opens X) 
: sheaf_of_rings U :=
{ F := res_presheaf OX.F U,
  locality := 
    begin
      intros V OC s t H,
      simp at *,
      have := OX.locality, -- (res_opens U V),
    end,
  gluing := sorry, }

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
