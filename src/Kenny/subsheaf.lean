import Kenny.sheaf_on_opens

universes v u

open topological_space

variables {X : Type u} [topological_space X]

structure subpresheaf (F : presheaf.{u v} X) : Type (max u v) :=
(to_set : Π U : opens X, set (F U))
(res_mem_to_set : ∀ {U V : opens X} (HVU : V ⊆ U) {x : F U}, x ∈ to_set U → F.res U V HVU x ∈ to_set V)

namespace subpresheaf

instance (F : presheaf.{u v} X) : has_coe_to_fun (subpresheaf F) :=
⟨_, to_set⟩

instance (F : presheaf.{u v} X) : partial_order (subpresheaf F) :=
partial_order.lift to_set (λ ⟨x, hx⟩ ⟨y, hy⟩, mk.inj_eq.mpr) infer_instance

def to_subsheaf {F : presheaf.{u v} X} (S : subpresheaf F) : subpresheaf F :=
{ to_set := λ U, { x | ∃ OC : covering.{u} U, ∀ i : OC.γ, F.res U (OC.Uis i) (subset_covering i) x ∈ S (OC.Uis i) },
  res_mem_to_set := λ U V HVU x ⟨OC, hx⟩, ⟨opens.covering_res U V HVU OC,
    λ i, have _ ∈ S ((opens.covering_res U V HVU OC).Uis i) := S.res_mem_to_set (set.inter_subset_right _ _) (hx i),
    by rwa ← presheaf.Hcomp' at this ⊢⟩ }

theorem le_to_subsheaf {F : presheaf.{u v} X} (S : subpresheaf F) : S ≤ S.to_subsheaf :=
λ U x hx, ⟨{ γ := punit, Uis := λ _, U, Hcov := le_antisymm (lattice.supr_le $ λ _, le_refl U) (lattice.le_supr (λ _, U) punit.star) },
λ i, by erw F.Hid'; exact hx⟩

def to_presheaf {F : presheaf.{u v} X} (S : subpresheaf F) : presheaf X :=
{ F := λ U, S U,
  res := λ U V HVU x, ⟨F.res U V HVU x.1, S.2 HVU x.2⟩,
  Hid := λ U, funext $ λ x, subtype.eq $ F.Hid' U x.1,
  Hcomp := λ U V W HWV HVU, funext $ λ x, subtype.eq $ F.Hcomp' U V W HWV HVU x.1 }

theorem locality {O : sheaf.{u v} X} (S : subpresheaf O.to_presheaf) : locality S.to_presheaf :=
λ U OC s t H, subtype.eq $ O.locality OC s.1 t.1 $ λ i, have _ := congr_arg subtype.val (H i), this

end subpresheaf

class is_subsheaf {F : presheaf.{u v} X} (S : subpresheaf F) : Prop :=
(mem_of_res_mem : ∀ {U : opens X}, ∀ {x : F U}, ∀ OC : covering.{u} U, (∀ i : OC.γ, F.res U (OC.Uis i) (subset_covering i) x ∈ S (OC.Uis i)) → x ∈ S U)

theorem covering.exists {U : opens X} (OC : covering U) {x : X} (hx : x ∈ U) : ∃ i : OC.γ, x ∈ OC.Uis i :=
let ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, hi⟩ := set.mem_sUnion.1 (((set.ext_iff _ _).1 (congr_arg subtype.val OC.Hcov) x).2 hx) in ⟨i, hi⟩

def covering.glue {U : opens X} (OC : covering U) (F : Π i : OC.γ, covering (OC.Uis i)) : covering U :=
{ γ := Σ i : OC.γ, (F i).γ,
  Uis := λ P, (F P.1).Uis P.2,
  Hcov := opens.ext $ (set.sUnion_image _ _).trans $ set.subset.antisymm
    (set.bUnion_subset $ set.range_subset_iff.2 $ λ P, set.subset.trans (subset_covering P.2) (subset_covering P.1))
    (λ x hx, let ⟨i, hi⟩ := OC.exists hx, ⟨j, hj⟩ := (F i).exists hi in set.mem_bUnion ⟨⟨i, j⟩, rfl⟩ hj) }

theorem is_subsheaf_to_subsheaf {F : presheaf.{u v} X} (S : subpresheaf F) : is_subsheaf S.to_subsheaf :=
⟨λ U x OC H, ⟨OC.glue $ λ i, classical.some (H i),
λ P, have _ := classical.some_spec (H P.1) P.2, by rw ← F.Hcomp' at this; convert this⟩⟩

theorem is_subsheaf.is_sheaf_to_presheaf {O : sheaf.{u v} X} (S : subpresheaf O.to_presheaf) [is_subsheaf S] : is_sheaf S.to_presheaf :=
{ left := λ U, S.locality,
  right := λ U OC s H, let ⟨f, hf⟩ := O.gluing OC (λ i, (s i).1) (λ j k, congr_arg subtype.val (H j k)) in
    ⟨⟨f, is_subsheaf.mem_of_res_mem OC $ λ i, (hf i).symm ▸ (s i).2⟩, λ i, subtype.eq $ hf i⟩ }
