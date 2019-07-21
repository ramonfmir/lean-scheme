import sheaves.sheaf Kenny.sandbox

universes v w u₁ v₁ u

open topological_space lattice

namespace opens

variables {X : Type u} [topological_space X]

theorem Inf_eq (s : set (opens X)) : Inf s = opens.interior (Inf $ subtype.val '' s) :=
le_antisymm
  ((subset_interior_iff_subset_of_open (Inf s).2).2 $ show (Inf s).1 ≤ Inf (subtype.val '' s),
    from le_Inf $ λ t ⟨u, hus, hut⟩, le_trans interior_subset $ Inf_le ⟨u, show Inf (set.range (λ (H : u ∈ s), u.val)) = t,
    from le_antisymm (Inf_le ⟨hus, hut⟩) (le_Inf $ λ b ⟨c, hc⟩, hc ▸ ge_of_eq hut)⟩)
  (le_Inf $ λ U hus, set.subset.trans interior_subset $ show Inf (subtype.val '' s) ≤ U.1,
    from Inf_le $ set.mem_image_of_mem _ hus)

theorem inter_val (U V : opens X) : (U ∩ V).1 = U.1 ∩ V.1 := rfl
theorem inf_val (U V : opens X) : (U ⊓ V).1 = U.1 ∩ V.1 := rfl

theorem inf_Sup (U : opens X) (s : set (opens X)) : U ⊓ Sup s = Sup ((⊓) U '' s) :=
opens.ext $ by rw [inf_val, opens.Sup_s, opens.Sup_s, set.sUnion_eq_Union, set.inter_Union_left, ← set.image_comp]; exact
set.subset.antisymm
  (set.Union_subset $ λ ⟨t, i, his, hit⟩, set.subset_sUnion_of_mem ⟨i, his, congr_arg ((∩) U.1) hit⟩)
  (set.sUnion_subset $ λ t ⟨i, his, hit⟩, set.subset_sUnion_of_mem ⟨⟨i.1, i, his, rfl⟩, hit⟩)

def covering_inf_left (U V : opens X) (OC : covering U) : covering (V ⊓ U) :=
{ γ := OC.γ,
  Uis := λ i : OC.γ, V ⊓ OC.Uis i,
  Hcov := by conv_rhs { rw ← OC.Hcov }; rw [supr, supr, inf_Sup]; congr' 1; ext x; exact
    ⟨λ ⟨i, hix⟩, ⟨OC.Uis i, ⟨i, rfl⟩, hix⟩, λ ⟨_, ⟨i, rfl⟩, hix⟩, ⟨i, hix⟩⟩ }

def covering_res (U V : opens X) (H : V ⊆ U) (OC : covering U) : covering V :=
{ γ := OC.γ,
  Uis := λ i : OC.γ, V ⊓ OC.Uis i,
  Hcov := by erw [(covering_inf_left U V OC).Hcov, (inf_of_le_left $ show V ≤ U, from H)] }

end opens

def presheaf.covering (X : Type u) [topological_space X] : presheaf.{u (u+1)} X :=
{ F := covering,
  res := opens.covering_res,
  Hid := λ U, funext $ λ OC, by cases OC; dsimp only [opens.covering_res, id]; congr' 1; funext i; apply opens.ext;
    apply set.inter_eq_self_of_subset_right; rw ← OC_Hcov; apply set.subset_sUnion_of_mem; refine ⟨_, ⟨_, rfl⟩, rfl⟩,
  Hcomp := λ U V W HWV HVU, funext $ λ OC, by dsimp only [opens.covering_res, function.comp_apply]; congr' 1; funext i;
    rw [← lattice.inf_assoc, lattice.inf_of_le_left (show W ≤ V, from HWV)] }

def sheaf_on_opens (X : Type u) [topological_space X] (U : opens X) : Type (max u (v+1)) :=
sheaf.{u v} X

namespace sheaf_on_opens

variables {X : Type u} [topological_space X] {U : opens X}

def eval (F : sheaf_on_opens X U) (V : opens X) (HVU : V ≤ U) : Type v :=
presheaf.F (sheaf.F F) V

def res (F : sheaf_on_opens X U) (V : opens X) (HVU : V ≤ U) (W : opens X) (HWU : W ≤ U) (HWV : W ≤ V) : F.eval V HVU → F.eval W HWU :=
presheaf.res _ _ _ HWV

theorem res_self (F : sheaf_on_opens X U) (V HVU HV x) :
  F.res V HVU V HVU HV x = x :=
presheaf.Hid' _ _ _

theorem res_res (F : sheaf_on_opens X U) (V HVU W HWU HWV S HSU HSW x) :
  F.res W HWU S HSU HSW (F.res V HVU W HWU HWV x) = F.res V HVU S HSU (le_trans HSW HWV) x :=
(presheaf.Hcomp' _ _ _ _ _ _ _).symm

theorem locality (F : sheaf_on_opens X U) (V HVU s t) (OC : covering V)
  (H : ∀ i : OC.γ, F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) s =
    F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) t) :
  s = t :=
F.locality OC s t H

noncomputable def glue (F : sheaf_on_opens X U) (V HVU) (OC : covering V)
  (s : Π i : OC.γ, F.eval (OC.Uis i) (le_trans (subset_covering i) HVU))
  (H : ∀ i j : OC.γ, F.res _ _ (OC.Uis i ⊓ OC.Uis j) (le_trans inf_le_left (le_trans (subset_covering i) HVU)) inf_le_left (s i) =
    F.res _ _ (OC.Uis i ⊓ OC.Uis j) (le_trans inf_le_left (le_trans (subset_covering i) HVU)) inf_le_right (s j)) :
  F.eval V HVU :=
classical.some $ F.gluing OC s H

theorem res_glue (F : sheaf_on_opens X U) (V HVU) (OC : covering V) (s H i) :
  F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) (F.glue V HVU OC s H) = s i :=
classical.some_spec (F.gluing OC s H) i

theorem eq_glue (F : sheaf_on_opens X U) (V HVU) (OC : covering V)
  (s : Π i : OC.γ, F.eval (OC.Uis i) (le_trans (subset_covering i) HVU)) (H t)
  (ht : ∀ i, F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) t = s i) :
  F.glue V HVU OC s H = t :=
F.locality V HVU _ _ OC $ λ i, by rw [res_glue, ht]

def res_subset (F : sheaf_on_opens X U) (V : opens X) (HVU : V ≤ U) : sheaf_on_opens X V :=
F

theorem res_res_subset (F : sheaf_on_opens X U) (V HVU S HSV T HTV HTS x) :
  (F.res_subset V HVU).res S HSV T HTV HTS x = F.res S (le_trans HSV HVU) T (le_trans HTV HVU) HTS x :=
rfl

def stalk (F : sheaf_on_opens.{v} X U) (x : X) (hx : x ∈ U) : Type (max u v) :=
stalk F.1 x

def to_stalk (F : sheaf_on_opens X U) (x : X) (hx : x ∈ U) (V : opens X) (hxV : x ∈ V) (HVU : V ≤ U) (s : F.eval V HVU) : F.stalk x hx :=
⟦⟨V, hxV, s⟩⟧

@[simp] lemma to_stalk_res (F : sheaf_on_opens X U) (x : X) (hx : x ∈ U) (V : opens X) (hxV : x ∈ V) (HVU : V ≤ U)
  (W : opens X) (hxW : x ∈ W) (HWV : W ≤ V) (s : F.eval V HVU) :
  F.to_stalk x hx W hxW (le_trans HWV HVU) (F.res _ _ _ _ HWV s) = F.to_stalk x hx V hxV HVU s :=
quotient.sound ⟨W, hxW, set.subset.refl W.1, HWV, by dsimp only [res]; rw ← presheaf.Hcomp'; refl⟩

@[elab_as_eliminator] theorem stalk.induction_on {F : sheaf_on_opens X U} {x : X} {hx : x ∈ U}
  {C : F.stalk x hx → Prop} (g : F.stalk x hx)
  (H : ∀ V : opens X, ∀ hxV : x ∈ V, ∀ HVU : V ≤ U, ∀ s : F.eval V HVU, C (F.to_stalk x hx V hxV HVU s)) :
  C g :=
quotient.induction_on g $ λ e,
have (⟦e⟧ : F.stalk x hx) = ⟦⟨e.1 ⊓ U, ⟨e.2, hx⟩, F.F.res _ _ (set.inter_subset_left _ _) e.3⟩⟧,
from quotient.sound ⟨e.1 ⊓ U, ⟨e.2, hx⟩, set.inter_subset_left _ _, set.subset.refl _, by dsimp only; rw ← presheaf.Hcomp'; refl⟩,
this.symm ▸ H (e.1 ⊓ U) ⟨e.2, hx⟩ inf_le_right _

structure morphism (F : sheaf_on_opens.{v} X U) (G : sheaf_on_opens.{w} X U) : Type (max u v w) :=
(map : ∀ V ≤ U, F.eval V H → G.eval V H)
(commutes : ∀ (V : opens X) (HV : V ≤ U) (W : opens X) (HW : W ≤ U) (HWV : W ≤ V) (x),
  map W HW (F.res V HV W HW HWV x) = G.res V HV W HW HWV (map V HV x))

namespace morphism

protected def id (F : sheaf_on_opens.{v} X U) : F.morphism F :=
{ map := λ V HV, id,
  commutes := λ V HV W HW HWV x, rfl }

def comp {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} {H : sheaf_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) : F.morphism H :=
{ map := λ V HV x, η.map V HV (ξ.map V HV x),
  commutes := λ V HV W HW HWV x, by rw [ξ.commutes, η.commutes] }

@[simp] lemma comp_apply {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} {H : sheaf_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) (V HV s) :
  (η.comp ξ).1 V HV s = η.1 V HV (ξ.1 V HV s) :=
rfl

@[extensionality] lemma ext {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U}
  {η ξ : F.morphism G} (H : ∀ V HV x, η.map V HV x = ξ.map V HV x) : η = ξ :=
by cases η; cases ξ; congr; ext; apply H

@[simp] lemma id_comp {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) :
  (morphism.id G).comp η = η :=
ext $ λ V HV x, rfl

@[simp] lemma comp_id {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) :
  η.comp (morphism.id F) = η :=
ext $ λ V HV x, rfl

@[simp] lemma comp_assoc {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} {H : sheaf_on_opens.{u₁} X U} {I : sheaf_on_opens.{v₁} X U}
  (η : H.morphism I) (ξ : G.morphism H) (χ : F.morphism G) :
  (η.comp ξ).comp χ = η.comp (ξ.comp χ) :=
rfl

def res_subset {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) (V : opens X) (HVU : V ≤ U) :
  (F.res_subset V HVU).morphism (G.res_subset V HVU) :=
{ map := λ W HWV, η.map W (le_trans HWV HVU),
  commutes := λ S HSV T HTV, η.commutes S (le_trans HSV HVU) T (le_trans HTV HVU) }

@[simp] lemma res_subset_apply {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) (V : opens X) (HVU : V ≤ U)
  (W HWV s) : (η.res_subset V HVU).1 W HWV s = η.1 W (le_trans HWV HVU) s :=
rfl

@[simp] lemma comp_res_subset {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} {H : sheaf_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) (V : opens X) (HVU : V ≤ U) :
  (η.res_subset V HVU).comp (ξ.res_subset V HVU) = (η.comp ξ).res_subset V HVU :=
rfl

@[simp] lemma id_res_subset {F : sheaf_on_opens.{v} X U} (V : opens X) (HVU : V ≤ U) :
  (morphism.id F).res_subset V HVU = morphism.id (F.res_subset V HVU) :=
rfl

def stalk {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) (x : X) (hx : x ∈ U)
  (s : F.stalk x hx) : G.stalk x hx :=
quotient.lift_on s (λ g, ⟦(⟨g.1 ⊓ U, (⟨g.2, hx⟩ : x ∈ g.1 ⊓ U),
  η.map _ inf_le_right (presheaf.res F.1 _ _ (set.inter_subset_left _ _) g.3)⟩ : stalk.elem _ _)⟧) $
λ g₁ g₂ ⟨V, hxV, HV1, HV2, hg⟩, quotient.sound ⟨V ⊓ U, ⟨hxV, hx⟩, set.inter_subset_inter_left _ HV1, set.inter_subset_inter_left _ HV2,
calc  G.res _ _ (V ⊓ U) inf_le_right (inf_le_inf HV1 (le_refl _)) (η.map (g₁.U ⊓ U) inf_le_right ((F.F).res (g₁.U) (g₁.U ⊓ U) (set.inter_subset_left _ _) (g₁.s)))
    = η.map (V ⊓ U) inf_le_right ((F.F).res V (V ⊓ U) (set.inter_subset_left _ _) ((F.F).res (g₁.U) V HV1 (g₁.s))) : by rw [← η.2, res, ← presheaf.Hcomp', ← presheaf.Hcomp']
... = G.res _ _ (V ⊓ U) _ _ (η.map (g₂.U ⊓ U) inf_le_right ((F.F).res (g₂.U) (g₂.U ⊓ U) _ (g₂.s))) : by rw [hg, ← η.2, res, ← presheaf.Hcomp', ← presheaf.Hcomp']⟩

@[simp] lemma stalk_to_stalk {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) (x : X) (hx : x ∈ U)
  (V : opens X) (HVU : V ≤ U) (hxV : x ∈ V) (s : F.eval V HVU) : η.stalk x hx (F.to_stalk x hx V hxV HVU s) = G.to_stalk x hx V hxV HVU (η.map V HVU s) :=
quotient.sound ⟨V, hxV, set.subset_inter (set.subset.refl _) HVU, set.subset.refl _,
calc  G.res (V ⊓ U) inf_le_right V HVU (le_inf (le_refl V) HVU) (η.map (V ⊓ U) inf_le_right (F.res V HVU (V ⊓ U) inf_le_right inf_le_left s))
    = G.res V HVU V HVU (le_refl V) (η.map V HVU s) : by rw [η.2, res_res]⟩

end morphism

structure equiv (F : sheaf_on_opens.{v} X U) (G : sheaf_on_opens.{w} X U) : Type (max u v w) :=
(to_fun : morphism F G)
(inv_fun : morphism G F)
(left_inv : ∀ V HVU s, inv_fun.1 V HVU (to_fun.1 V HVU s) = s)
(right_inv : ∀ V HVU s, to_fun.1 V HVU (inv_fun.1 V HVU s) = s)

namespace equiv

def refl (F : sheaf_on_opens.{v} X U) : equiv F F :=
⟨morphism.id F, morphism.id F, λ _ _ _, rfl, λ _ _ _, rfl⟩

@[simp] lemma refl_apply (F : sheaf_on_opens.{v} X U) (V HV s) :
  (refl F).1.1 V HV s = s := rfl

def symm {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{v} X U} (e : equiv F G) : equiv G F :=
⟨e.2, e.1, e.4, e.3⟩

def trans {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{v} X U} {H : sheaf_on_opens.{u₁} X U}
  (e₁ : equiv F G) (e₂ : equiv G H) : equiv F H :=
⟨e₂.1.comp e₁.1, e₁.2.comp e₂.2,
λ _ _ _, by rw [morphism.comp_apply, morphism.comp_apply, e₂.3, e₁.3],
λ _ _ _, by rw [morphism.comp_apply, morphism.comp_apply, e₁.4, e₂.4]⟩

@[simp] lemma trans_apply {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{v} X U} {H : sheaf_on_opens.{u₁} X U}
  (e₁ : equiv F G) (e₂ : equiv G H) (V HV s) :
  (e₁.trans e₂).1.1 V HV s = e₂.1.1 V HV (e₁.1.1 V HV s) :=
rfl

def res_subset {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (e : equiv F G)
  (V : opens X) (HVU : V ≤ U) : equiv (F.res_subset V HVU) (G.res_subset V HVU) :=
⟨e.1.res_subset V HVU, e.2.res_subset V HVU,
λ _ _ _, by rw [morphism.res_subset_apply, morphism.res_subset_apply, e.3],
λ _ _ _, by rw [morphism.res_subset_apply, morphism.res_subset_apply, e.4]⟩

@[simp] lemma res_subset_apply {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (e : equiv F G)
  (V : opens X) (HVU : V ≤ U) (W HW s) :
  (e.res_subset V HVU).1.1 W HW s = e.1.1 W (le_trans HW HVU) s :=
rfl

def stalk {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (e : equiv F G) (x : X) (hx : x ∈ U) :
  F.stalk x hx ≃ G.stalk x hx :=
{ to_fun := e.1.stalk x hx,
  inv_fun := e.2.stalk x hx,
  left_inv := λ g, stalk.induction_on g $ λ V hxV HVU s, by rw [morphism.stalk_to_stalk, morphism.stalk_to_stalk, e.3],
  right_inv := λ g, stalk.induction_on g $ λ V hxV HVU s, by rw [morphism.stalk_to_stalk, morphism.stalk_to_stalk, e.4] }

end equiv

namespace sheaf_glue

variables {I : Type u} (S : I → opens X) (F : Π (i : I), sheaf_on_opens.{v} X (S i))
variables (φ : Π (i j : I), equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right))
variables (Hφ1 : ∀ i, φ i i = equiv.refl (res_subset (F i) (S i ⊓ S i) _))
variables (Hφ2 : ∀ i j k,
  ((φ i j).res_subset ((S i) ⊓ (S j) ⊓ (S k)) inf_le_left).trans
    ((φ j k).res_subset ((S i) ⊓ (S j) ⊓ (S k)) (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)) =
  (φ i k).res_subset ((S i) ⊓ (S j) ⊓ (S k)) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right))

@[reducible] def compat (W : opens X) : Type (max u v) :=
{ f : Π i, (F i).eval ((S i) ⊓ W) inf_le_left //
  ∀ i j, (φ i j).1.map ((S i) ⊓ (S j) ⊓ W) inf_le_left
    ((F i).res ((S i) ⊓ W) _ _ (le_trans inf_le_left inf_le_left)
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
      (f i)) =
    (F j).res ((S j) ⊓ W) _ _ (le_trans inf_le_left inf_le_right)
      (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)
      (f j) }

def res (U V : opens X) (HVU : V ≤ U) (f : compat S F φ U) : compat S F φ V :=
⟨λ i, (F i).res (S i ⊓ U) _ (S i ⊓ V) _ (inf_le_inf (le_refl _) HVU) (f.1 i), λ i j,
calc  (φ i j).1.map (S i ⊓ S j ⊓ V) inf_le_left
        (res (F i) (S i ⊓ V) inf_le_left (S i ⊓ S j ⊓ V)
          (le_trans inf_le_left inf_le_left)
          (le_inf (le_trans inf_le_left inf_le_left)
              inf_le_right)
          (res (F i) (S i ⊓ U) inf_le_left (S i ⊓ V) inf_le_left
              (inf_le_inf (le_refl _) HVU)
              (f.1 i)) : (F i).eval (S i ⊓ S j ⊓ V) (le_trans _ _))
    = (φ i j).1.map (S i ⊓ S j ⊓ V) inf_le_left
        (res (res_subset (F i) (S i ⊓ S j) inf_le_left) (S i ⊓ S j ⊓ U) inf_le_left
          (S i ⊓ S j ⊓ V)
          inf_le_left
          (inf_le_inf (le_refl _) HVU)
          (res (F i) (S i ⊓ U) inf_le_left (S i ⊓ S j ⊓ U)
            (le_trans inf_le_left inf_le_left)
            (le_inf (le_trans inf_le_left inf_le_left)
                inf_le_right)
            (f.1 i) : (F i).eval (S i ⊓ S j ⊓ U) (le_trans inf_le_left inf_le_left))) :
  by rw [res_res_subset, res_res, res_res]
... = (res (F j) (S j ⊓ V) inf_le_left (S i ⊓ S j ⊓ V)
        (le_trans inf_le_left inf_le_right)
        (le_inf (le_trans inf_le_left inf_le_right)
          inf_le_right)
        (res (F j) (S j ⊓ U) inf_le_left (S j ⊓ V) inf_le_left
          (inf_le_inf (le_refl _) HVU)
          (f.1 j)) : (F j).eval (S i ⊓ S j ⊓ V) _) :
  by rw [(φ i j).1.commutes, f.2 i j, res_res_subset, res_res, res_res]⟩

theorem locality (U : opens X) (OC : covering U) (s t : sheaf_glue.compat S F φ U)
  (H : ∀ i : OC.γ, sheaf_glue.res S F φ U (OC.Uis i) (subset_covering i) s =
    sheaf_glue.res S F φ U (OC.Uis i) (subset_covering i) t) :
  s = t :=
subtype.eq $ funext $ λ i, (F i).locality _ _ _ _ (opens.covering_inf_left U (S i) OC) $ λ j,
by have := H j; simp only [sheaf_glue.res, subtype.mk.inj_eq] at this; exact congr_fun this i

noncomputable def gluing.aux1 (U : opens X) (OC : covering U) (s : Π i : OC.γ, sheaf_glue.compat S F φ (OC.Uis i))
  (H : ∀ i j : OC.γ, sheaf_glue.res S F φ _ _ inf_le_left (s i) = sheaf_glue.res S F φ _ _ inf_le_right (s j))
  (i : I) : (F i).eval (S i ⊓ U) inf_le_left :=
(F i).glue _ _ (opens.covering_inf_left U (S i) OC) (λ j, (s j).1 i) $ λ j k,
have h1 : S i ⊓ OC.Uis j ⊓ (S i ⊓ OC.Uis k) ≤ S i ⊓ (OC.Uis j ⊓ OC.Uis k),
by rw [inf_assoc, inf_left_comm (OC.Uis j), ← inf_assoc, inf_idem]; exact le_refl _,
have h2 : S i ⊓ (OC.Uis j ⊓ OC.Uis k) ≤ S i ⊓ OC.Uis j,
from inf_le_inf (le_refl _) inf_le_left,
have h3 : S i ⊓ (OC.Uis j ⊓ OC.Uis k) ≤ S i ⊓ OC.Uis k,
from inf_le_inf (le_refl _) inf_le_right,
have (F i).res (S i ⊓ OC.Uis j) _ (S i ⊓ (OC.Uis j ⊓ OC.Uis k)) inf_le_left h2 ((s j).1 i) =
  (F i).res (S i ⊓ OC.Uis k) _ (S i ⊓ (OC.Uis j ⊓ OC.Uis k)) inf_le_left h3 ((s k).1 i),
from congr_fun (congr_arg subtype.val (H j k)) i,
calc  _
    = (F i).res (S i ⊓ OC.Uis j) _ ((S i ⊓ OC.Uis j) ⊓ (S i ⊓ OC.Uis k)) _ _ ((s j).1 i) : rfl
... = (F i).res (S i ⊓ (OC.Uis j ⊓ OC.Uis k)) _ ((S i ⊓ OC.Uis j) ⊓ (S i ⊓ OC.Uis k)) _ h1
        ((F i).res (S i ⊓ OC.Uis j) _ (S i ⊓ (OC.Uis j ⊓ OC.Uis k)) inf_le_left h2 ((s j).1 i)) : (res_res _ _ _ _ _ _ _ _ _ _).symm
... = (F i).res (S i ⊓ OC.Uis k) _ ((S i ⊓ OC.Uis j) ⊓ (S i ⊓ OC.Uis k)) _ inf_le_right ((s k).1 i) : by rw [this, res_res]

theorem gluing.aux2 (U : opens X) (OC : covering U) (s : Π i : OC.γ, sheaf_glue.compat S F φ (OC.Uis i))
  (H : ∀ i j : OC.γ, sheaf_glue.res S F φ _ _ inf_le_left (s i) = sheaf_glue.res S F φ _ _ inf_le_right (s j)) (i j : I) :
  (φ i j).1.map (S i ⊓ S j ⊓ U) inf_le_left
      ((F i).res (S i ⊓ U) _ (S i ⊓ S j ⊓ U) (le_trans inf_le_left inf_le_left)
        (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
        (gluing.aux1 S F φ U OC s H i)) =
    (F j).res (S j ⊓ U) _ (S i ⊓ S j ⊓ U) (le_trans inf_le_left inf_le_right)
      (by rw inf_assoc; exact inf_le_right)
      (gluing.aux1 S F φ U OC s H j) :=
(F j).locality _ _ _ _ (opens.covering_inf_left _ _ OC) $ λ k,
calc  ((F j).res_subset (S i ⊓ S j) inf_le_right).res (S i ⊓ S j ⊓ U) inf_le_left ((S i ⊓ S j) ⊓ OC.Uis k) inf_le_left
        (inf_le_inf (le_refl _) (subset_covering k))
        ((φ i j).1.map (S i ⊓ S j ⊓ U) inf_le_left
          ((F i).res (S i ⊓ U) _ (S i ⊓ S j ⊓ U) _
            (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
            (gluing.aux1 S F φ U OC s H i)))
    = (φ i j).1.map (S i ⊓ S j ⊓ OC.Uis k) inf_le_left
        ((F i).res ((opens.covering_inf_left U (S i) OC).Uis k) _ _ (le_trans inf_le_left inf_le_left)
          (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
          ((F i).res (S i ⊓ U) _ ((opens.covering_inf_left U (S i) OC).Uis k) inf_le_left
            (inf_le_inf (le_refl _) (subset_covering k))
            (gluing.aux1 S F φ U OC s H i))) : by rw [← (φ i j).1.commutes, res_res_subset, res_res, res_res]
... = (F j).res ((opens.covering_inf_left U (S j) OC).Uis k) _ ((S i ⊓ S j) ⊓ OC.Uis k) _
        (by rw inf_assoc; exact inf_le_right)
        ((F j).res (S j ⊓ U) _ ((opens.covering_inf_left U (S j) OC).Uis k) inf_le_left
          (inf_le_inf (le_refl _) (subset_covering k))
          (gluing.aux1 S F φ U OC s H j)) : by erw [res_glue, res_glue]; exact (s k).2 i j
... = (F j).res (S i ⊓ S j ⊓ U) _ ((S i ⊓ S j) ⊓ OC.Uis k) _ _
        ((F j).res (S j ⊓ U) _ (S i ⊓ S j ⊓ U) _ _ (gluing.aux1 S F φ U OC s H j)) : by rw [res_res, res_res]; refl

theorem gluing.aux3 (U : opens X) (OC : covering U) (s : Π i : OC.γ, sheaf_glue.compat S F φ (OC.Uis i))
  (H : ∀ i j : OC.γ, sheaf_glue.res S F φ _ _ inf_le_left (s i) = sheaf_glue.res S F φ _ _ inf_le_right (s j)) (i : OC.γ) :
  sheaf_glue.res S F φ U (OC.Uis i) (subset_covering i) ⟨λ i, gluing.aux1 S F φ U OC s H i, gluing.aux2 S F φ U OC s H⟩ = s i :=
subtype.eq $ funext $ λ j, by dsimp only [gluing.aux1, sheaf_glue.res];
change (F j).res _ _ ((opens.covering_inf_left U (S j) OC).Uis i) _ _ _ = _;
erw res_glue

theorem gluing (U : opens X) (OC : covering U) (s : Π i : OC.γ, sheaf_glue.compat S F φ (OC.Uis i))
  (H : ∀ i j : OC.γ, sheaf_glue.res S F φ _ _ inf_le_left (s i) = sheaf_glue.res S F φ _ _ inf_le_right (s j)) :
  ∃ t : sheaf_glue.compat S F φ U, ∀ i : OC.γ, sheaf_glue.res S F φ U (OC.Uis i) (subset_covering i) t = s i :=
⟨⟨λ i, gluing.aux1 S F φ U OC s H i, gluing.aux2 S F φ U OC s H⟩, λ i, gluing.aux3 S F φ U OC s H i⟩

end sheaf_glue

def sheaf_glue {I : Type u} (S : I → opens X) (F : Π (i : I), sheaf_on_opens.{v} X (S i))
  (φ : Π i j, equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right)) :
  sheaf_on_opens.{max u v} X (⋃S) :=
{ F :=
  { F := sheaf_glue.compat S F φ,
    res := sheaf_glue.res S F φ,
    Hid := λ U, funext $ λ f, subtype.eq $ funext $ λ i, by dsimp only [sheaf_glue.res, id]; rw res_self,
    Hcomp := λ U V W HWV HVU, funext $ λ f, subtype.eq $ funext $ λ i, by symmetry; apply res_res; exact inf_le_left },
  locality := sheaf_glue.locality S F φ,
  gluing := sheaf_glue.gluing S F φ }

@[simp] lemma sheaf_glue_res_val {I : Type u} (S : I → opens X) (F : Π (i : I), sheaf_on_opens.{v} X (S i))
  (φ : Π i j, equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right))
  (U HU V HV HVU s i) : ((sheaf_glue S F φ).res U HU V HV HVU s).1 i = (F i).res _ _ _ _ (inf_le_inf (le_refl _) HVU) (s.1 i) := rfl

def universal_property (I : Type u) (S : I → opens X) (F : Π (i : I), sheaf_on_opens.{v} X (S i))
  (φ : Π i j, equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right))
  (Hφ1 : ∀ i V HV s, (φ i i).1.1 V HV s = s)
  (Hφ2 : ∀ i j k V HV1 HV2 HV3 s, (φ j k).1.1 V HV1 ((φ i j).1.1 V HV2 s) = (φ i k).1.1 V HV3 s)
  (i : I) :
  equiv (res_subset (sheaf_glue S F φ) (S i) (le_supr S i)) (F i) :=
{ to_fun :=
  { map := λ U H s, (F i).res _ _ _ _ (le_inf H (le_refl _)) (s.1 i),
    commutes := λ U HU V HV HVU s, by rw [res_res, res_res_subset]; dsimp only [res, sheaf_glue, sheaf_glue.res]; rw ← presheaf.Hcomp'; refl },
  inv_fun :=
  { map := λ U H s, ⟨λ j, (φ i j).1.1 (S j ⊓ U) (le_inf (le_trans inf_le_right H) inf_le_left)
        ((F i).res _ _ _ (le_trans inf_le_right H) inf_le_right s),
      λ j k, begin
        have h1 : S j ⊓ S k ⊓ U ≤ S i ⊓ S j := le_inf (le_trans inf_le_right H) (le_trans inf_le_left inf_le_left),
        have h2 : S j ⊓ S k ⊓ U ≤ S i ⊓ S k := le_inf (le_trans inf_le_right H) (le_trans inf_le_left inf_le_right),
        rw [← res_res_subset (F j) _ _ _ _ _ h1, ← (φ i j).1.2, Hφ2 _ _ _ _ _ _ h2, res_res_subset, res_res],
        rw [← res_res_subset (F k) _ _ _ _ _ h2, ← (φ i k).1.2, res_res_subset, res_res],
      end⟩,
    commutes := λ U HU V HV HVU s, subtype.eq $ funext $ λ j, by dsimp only [res_res_subset, sheaf_glue_res_val];
      rw [← res_res_subset (F j), ← (φ i j).1.2, res_res_subset, res_res, res_res] },
  left_inv := λ V HV s, subtype.eq $ funext $ λ j, have _, from s.2 i j, calc
      _ = (φ i j).1.map (S j ⊓ V) (le_inf (le_trans inf_le_right HV) inf_le_left)
            ((F i).res V HV (S j ⊓ V) (le_trans inf_le_right HV) inf_le_right
              ((F i).res (S i ⊓ V) _ V HV (le_inf HV (le_refl _)) (s.1 i))) : rfl
    ... = (φ i j).1.map (S j ⊓ V) _
            ((F i).res (S i ⊓ V) _ (S j ⊓ V) _ _ (s.1 i)) : by rw res_res
    ... = (φ i j).1.map (S j ⊓ V) _
            (((F i).res_subset (S i ⊓ S j) _).res ((S i ⊓ S j) ⊓ V) inf_le_left _ _
              (by rw [inf_assoc, inf_left_comm, inf_of_le_right HV]; exact le_refl _)
              ((F i).res (S i ⊓ V) _ ((S i ⊓ S j) ⊓ V) (le_trans inf_le_left inf_le_left)
                (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
                (s.1 i))) : by rw [res_res_subset, res_res]
    ... = s.1 j : by rw [(φ i j).1.2, s.2 i j, res_res_subset, res_res, res_self],
  right_inv := λ V HV s, by dsimp only; erw [Hφ1, res_res, res_self] }

end sheaf_on_opens
