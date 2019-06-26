import sheaves.sheaf_of_rings Kenny.sheaf_on_opens ring_theory.subring

universes v w u₁ v₁ u

open topological_space lattice

def sheaf_of_rings_on_opens (X : Type u) [topological_space X] (U : opens X) : Type (max u (v+1)) :=
sheaf_of_rings.{u v} X

namespace sheaf_of_rings_on_opens

variables {X : Type u} [topological_space X] {U : opens X}

def to_sheaf_on_opens (F : sheaf_of_rings_on_opens X U) : sheaf_on_opens X U :=
{ F := F.1.1,
  locality := F.2,
  gluing := F.3 }

def eval (F : sheaf_of_rings_on_opens X U) : Π (V : opens X), V ≤ U → Type v :=
F.to_sheaf_on_opens.eval

instance comm_ring_eval (F : sheaf_of_rings_on_opens X U) (V HVU) : comm_ring (F.eval V HVU) :=
F.1.2 V

def res (F : sheaf_of_rings_on_opens X U) : Π (V : opens X) (HVU : V ≤ U) (W : opens X) (HWU : W ≤ U) (HWV : W ≤ V), F.eval V HVU → F.eval W HWU :=
F.to_sheaf_on_opens.res

instance is_ring_hom_res (F : sheaf_of_rings_on_opens X U) (V HVU W HWU HWV) : is_ring_hom (F.res V HVU W HWU HWV) :=
F.1.3 V W HWV

section
variables (F : sheaf_of_rings_on_opens X U) (V : opens X) (HVU : V ≤ U) (W : opens X) (HWU : W ≤ U) (HWV : W ≤ V)
variables (x y : F.eval V HVU) (n : ℕ)
@[simp] lemma res_add : F.res V HVU W HWU HWV (x + y) = F.res V HVU W HWU HWV x + F.res V HVU W HWU HWV y := is_ring_hom.map_add _
@[simp] lemma res_zero : F.res V HVU W HWU HWV 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma res_neg : F.res V HVU W HWU HWV (-x) = -F.res V HVU W HWU HWV x := is_ring_hom.map_neg _
@[simp] lemma res_sub : F.res V HVU W HWU HWV (x - y) = F.res V HVU W HWU HWV x - F.res V HVU W HWU HWV y := is_ring_hom.map_sub _
@[simp] lemma res_mul : F.res V HVU W HWU HWV (x * y) = F.res V HVU W HWU HWV x * F.res V HVU W HWU HWV y := is_ring_hom.map_mul _
@[simp] lemma res_one : F.res V HVU W HWU HWV 1 = 1 := is_ring_hom.map_one _
@[simp] lemma res_pow : F.res V HVU W HWU HWV (x^n) = (F.res V HVU W HWU HWV x)^n := is_semiring_hom.map_pow _ x n
end

theorem res_self (F : sheaf_of_rings_on_opens X U) (V HVU HV x) :
  F.res V HVU V HVU HV x = x :=
F.to_sheaf_on_opens.res_self V HVU HV x

theorem res_res (F : sheaf_of_rings_on_opens X U) (V HVU W HWU HWV S HSU HSW x) :
  F.res W HWU S HSU HSW (F.res V HVU W HWU HWV x) = F.res V HVU S HSU (le_trans HSW HWV) x :=
F.to_sheaf_on_opens.res_res V HVU W HWU HWV S HSU HSW x

theorem locality (F : sheaf_of_rings_on_opens X U) (V HVU s t) (OC : covering V)
  (H : ∀ i : OC.γ, F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) s =
    F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) t) :
  s = t :=
F.locality OC s t H

noncomputable def glue (F : sheaf_of_rings_on_opens X U) (V HVU) (OC : covering V)
  (s : Π i : OC.γ, F.eval (OC.Uis i) (le_trans (subset_covering i) HVU))
  (H : ∀ i j : OC.γ, F.res _ _ (OC.Uis i ⊓ OC.Uis j) (le_trans inf_le_left (le_trans (subset_covering i) HVU)) inf_le_left (s i) =
    F.res _ _ (OC.Uis i ⊓ OC.Uis j) (le_trans inf_le_left (le_trans (subset_covering i) HVU)) inf_le_right (s j)) :
  F.eval V HVU :=
classical.some $ F.gluing OC s H

theorem res_glue (F : sheaf_of_rings_on_opens X U) (V HVU) (OC : covering V) (s H i) :
  F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) (F.glue V HVU OC s H) = s i :=
classical.some_spec (F.gluing OC s H) i

theorem eq_glue (F : sheaf_of_rings_on_opens X U) (V HVU) (OC : covering V)
  (s : Π i : OC.γ, F.eval (OC.Uis i) (le_trans (subset_covering i) HVU)) (H t)
  (ht : ∀ i, F.res V HVU (OC.Uis i) (le_trans (subset_covering i) HVU) (subset_covering i) t = s i) :
  F.glue V HVU OC s H = t :=
F.locality V HVU _ _ OC $ λ i, by rw [res_glue, ht]

def res_subset (F : sheaf_of_rings_on_opens X U) (V : opens X) (HVU : V ≤ U) : sheaf_of_rings_on_opens X V :=
F

theorem res_res_subset (F : sheaf_of_rings_on_opens X U) (V HVU S HSV T HTV HTS x) :
  (F.res_subset V HVU).res S HSV T HTV HTS x = F.res S (le_trans HSV HVU) T (le_trans HTV HVU) HTS x :=
rfl

def stalk (F : sheaf_of_rings_on_opens.{v} X U) (x : X) (hx : x ∈ U) : Type (max u v) :=
stalk_of_rings F.1 x

instance comm_ring_stalk (F : sheaf_of_rings_on_opens.{v} X U) (x : X) (hx : x ∈ U) : comm_ring (F.stalk x hx) :=
stalk_of_rings_is_comm_ring F.1 x

def to_stalk (F : sheaf_of_rings_on_opens.{v} X U) (x : X) (hx : x ∈ U) (V : opens X) (hxV : x ∈ V) (HVU : V ≤ U) (s : F.eval V HVU) : F.stalk x hx :=
F.to_sheaf_on_opens.to_stalk x hx V hxV HVU s

instance is_ring_hom_to_stalk (F : sheaf_of_rings_on_opens X U) (x hx V hxV HVU) : is_ring_hom (F.to_stalk x hx V hxV HVU) :=
to_stalk.is_ring_hom _ _ _ _

section
variables (F : sheaf_of_rings_on_opens.{v} X U) (x : X) (hx : x ∈ U) (V : opens X) (hxV : x ∈ V) (HVU : V ≤ U)
variables (s t : F.eval V HVU) (n : ℕ)
@[simp] lemma to_stalk_add : F.to_stalk x hx V hxV HVU (s + t) = F.to_stalk x hx V hxV HVU s + F.to_stalk x hx V hxV HVU t := is_ring_hom.map_add _
@[simp] lemma to_stalk_zero : F.to_stalk x hx V hxV HVU 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma to_stalk_neg : F.to_stalk x hx V hxV HVU (-s) = -F.to_stalk x hx V hxV HVU s := is_ring_hom.map_neg _
@[simp] lemma to_stalk_sub : F.to_stalk x hx V hxV HVU (s - t) = F.to_stalk x hx V hxV HVU s - F.to_stalk x hx V hxV HVU t := is_ring_hom.map_sub _
@[simp] lemma to_stalk_mul : F.to_stalk x hx V hxV HVU (s * t) = F.to_stalk x hx V hxV HVU s * F.to_stalk x hx V hxV HVU t := is_ring_hom.map_mul _
@[simp] lemma to_stalk_one : F.to_stalk x hx V hxV HVU 1 = 1 := is_ring_hom.map_one _
@[simp] lemma to_stalk_pow : F.to_stalk x hx V hxV HVU (s^n) = (F.to_stalk x hx V hxV HVU s)^n := is_semiring_hom.map_pow _ s n
end

@[simp] lemma to_stalk_res (F : sheaf_of_rings_on_opens.{v} X U) (x : X) (hx : x ∈ U) (V : opens X) (hxV : x ∈ V) (HVU : V ≤ U)
  (W : opens X) (hxW : x ∈ W) (HWV : W ≤ V) (s : F.eval V HVU) :
  F.to_stalk x hx W hxW (le_trans HWV HVU) (F.res _ _ _ _ HWV s) = F.to_stalk x hx V hxV HVU s :=
to_stalk_res _ _ _ _ _ _ _ _

@[elab_as_eliminator] theorem stalk.induction_on {F : sheaf_of_rings_on_opens X U} {x : X} {hx : x ∈ U}
  {C : F.stalk x hx → Prop} (g : F.stalk x hx)
  (H : ∀ V : opens X, ∀ hxV : x ∈ V, ∀ HVU : V ≤ U, ∀ s : F.eval V HVU, C (F.to_stalk x hx V hxV HVU s)) :
  C g :=
quotient.induction_on g $ λ e,
have (⟦e⟧ : F.stalk x hx) = ⟦⟨e.1 ⊓ U, ⟨e.2, hx⟩, F.F.res _ _ (set.inter_subset_left _ _) e.3⟩⟧,
from quotient.sound ⟨e.1 ⊓ U, ⟨e.2, hx⟩, set.inter_subset_left _ _, set.subset.refl _, by dsimp only; rw ← presheaf.Hcomp'; refl⟩,
this.symm ▸ H (e.1 ⊓ U) ⟨e.2, hx⟩ inf_le_right _

@[elab_as_eliminator] theorem stalk.induction_on₂ {F : sheaf_of_rings_on_opens X U} {x : X} {hx : x ∈ U}
  {C : F.stalk x hx → F.stalk x hx → Prop} (g1 g2 : F.stalk x hx)
  (H : ∀ V : opens X, ∀ hxV : x ∈ V, ∀ HVU : V ≤ U, ∀ s t : F.eval V HVU, C (F.to_stalk x hx V hxV HVU s) (F.to_stalk x hx V hxV HVU t)) :
  C g1 g2 :=
quotient.induction_on₂ g1 g2 $ λ e1 e2,
have h1 : (⟦e1⟧ : F.stalk x hx) = _root_.to_stalk F.F x (e1.1 ⊓ e2.1 ⊓ U) ⟨⟨e1.2, e2.2⟩, hx⟩ (F.F.res _ _ (λ p hp, hp.1.1) e1.3),
by erw [_root_.to_stalk_res]; cases e1; refl,
have h2 : (⟦e2⟧ : F.stalk x hx) = _root_.to_stalk F.F x (e1.1 ⊓ e2.1 ⊓ U) ⟨⟨e1.2, e2.2⟩, hx⟩ (F.F.res _ _ (λ p hp, hp.1.2) e2.3),
by erw [_root_.to_stalk_res]; cases e2; refl,
h1.symm ▸ h2.symm ▸ H _ _ inf_le_right _ _

structure morphism (F : sheaf_of_rings_on_opens.{v} X U) (G : sheaf_of_rings_on_opens.{w} X U) : Type (max u v w) :=
(map : ∀ V ≤ U, F.eval V H → G.eval V H)
[hom : ∀ V HV, is_ring_hom (map V HV)]
(commutes : ∀ (V : opens X) (HV : V ≤ U) (W : opens X) (HW : W ≤ U) (HWV : W ≤ V) (x),
  map W HW (F.res V HV W HW HWV x) = G.res V HV W HW HWV (map V HV x))
attribute [instance] morphism.hom

namespace morphism

section
variables {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U}
variables (η : F.morphism G) (V : opens X) (HVU : V ≤ U) (x y : F.eval V HVU) (n : ℕ)
@[simp] lemma map_add : η.map V HVU (x + y) = η.map V HVU x + η.map V HVU y := is_ring_hom.map_add _
@[simp] lemma map_zero : η.map V HVU 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma map_neg : η.map V HVU (-x) = -η.map V HVU x := is_ring_hom.map_neg _
@[simp] lemma map_sub : η.map V HVU (x - y) = η.map V HVU x - η.map V HVU y := is_ring_hom.map_sub _
@[simp] lemma map_mul : η.map V HVU (x * y) = η.map V HVU x * η.map V HVU y := is_ring_hom.map_mul _
@[simp] lemma map_one : η.map V HVU 1 = 1 := is_ring_hom.map_one _
@[simp] lemma map_pow : η.map V HVU (x^n) = (η.map V HVU x)^n := is_semiring_hom.map_pow _ x n
end

def to_sheaf_on_opens {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) :
  F.to_sheaf_on_opens.morphism G.to_sheaf_on_opens :=
{ .. η }

protected def id (F : sheaf_of_rings_on_opens.{v} X U) : F.morphism F :=
{ map := λ V HV, id,
  commutes := λ V HV W HW HWV x, rfl }

def comp {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} {H : sheaf_of_rings_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) : F.morphism H :=
{ map := λ V HV x, η.map V HV (ξ.map V HV x),
  commutes := λ V HV W HW HWV x, by rw [ξ.commutes, η.commutes] }

@[simp] lemma comp_apply {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} {H : sheaf_of_rings_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) (V HV s) :
  (η.comp ξ).1 V HV s = η.1 V HV (ξ.1 V HV s) :=
rfl

@[extensionality] lemma ext {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U}
  {η ξ : F.morphism G} (H : ∀ V HV x, η.map V HV x = ξ.map V HV x) : η = ξ :=
by cases η; cases ξ; congr; ext; apply H

@[simp] lemma id_comp {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) :
  (morphism.id G).comp η = η :=
ext $ λ V HV x, rfl

@[simp] lemma comp_id {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) :
  η.comp (morphism.id F) = η :=
ext $ λ V HV x, rfl

@[simp] lemma comp_assoc {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} {H : sheaf_of_rings_on_opens.{u₁} X U} {I : sheaf_of_rings_on_opens.{v₁} X U}
  (η : H.morphism I) (ξ : G.morphism H) (χ : F.morphism G) :
  (η.comp ξ).comp χ = η.comp (ξ.comp χ) :=
rfl

def res_subset {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) (V : opens X) (HVU : V ≤ U) :
  (F.res_subset V HVU).morphism (G.res_subset V HVU) :=
{ map := λ W HWV, η.map W (le_trans HWV HVU),
  commutes := λ S HSV T HTV, η.commutes S (le_trans HSV HVU) T (le_trans HTV HVU) }

@[simp] lemma res_subset_apply {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) (V : opens X) (HVU : V ≤ U)
  (W HWV s) : (η.res_subset V HVU).1 W HWV s = η.1 W (le_trans HWV HVU) s :=
rfl

@[simp] lemma comp_res_subset {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} {H : sheaf_of_rings_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) (V : opens X) (HVU : V ≤ U) :
  (η.res_subset V HVU).comp (ξ.res_subset V HVU) = (η.comp ξ).res_subset V HVU :=
rfl

@[simp] lemma id_res_subset {F : sheaf_of_rings_on_opens.{v} X U} (V : opens X) (HVU : V ≤ U) :
  (morphism.id F).res_subset V HVU = morphism.id (F.res_subset V HVU) :=
rfl

def stalk {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) (x : X) (hx : x ∈ U)
  (s : F.stalk x hx) : G.stalk x hx :=
quotient.lift_on s (λ g, ⟦(⟨g.1 ⊓ U, (⟨g.2, hx⟩ : x ∈ g.1 ⊓ U),
  η.map _ inf_le_right (presheaf.res F.1.1 _ _ (set.inter_subset_left _ _) g.3)⟩ : stalk.elem _ _)⟧) $
λ g₁ g₂ ⟨V, hxV, HV1, HV2, hg⟩, quotient.sound ⟨V ⊓ U, ⟨hxV, hx⟩, set.inter_subset_inter_left _ HV1, set.inter_subset_inter_left _ HV2,
calc  G.res _ _ (V ⊓ U) inf_le_right (inf_le_inf HV1 (le_refl _)) (η.map (g₁.U ⊓ U) inf_le_right ((F.F).res (g₁.U) (g₁.U ⊓ U) (set.inter_subset_left _ _) (g₁.s)))
    = η.map (V ⊓ U) inf_le_right ((F.F).res V (V ⊓ U) (set.inter_subset_left _ _) ((F.F).res (g₁.U) V HV1 (g₁.s))) :
  by rw ← η.3; dsimp only [res, sheaf_on_opens.res, sheaf_of_rings_on_opens.to_sheaf_on_opens]; rw [← presheaf.Hcomp', ← presheaf.Hcomp']
... = G.res _ _ (V ⊓ U) _ _ (η.map (g₂.U ⊓ U) inf_le_right ((F.F).res (g₂.U) (g₂.U ⊓ U) _ (g₂.s))) :
  by rw [hg, ← η.3]; dsimp only [res, sheaf_on_opens.res, sheaf_of_rings_on_opens.to_sheaf_on_opens]; rw [← presheaf.Hcomp', ← presheaf.Hcomp']⟩

@[simp] lemma stalk_to_stalk {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) (x : X) (hx : x ∈ U)
  (V : opens X) (HVU : V ≤ U) (hxV : x ∈ V) (s : F.eval V HVU) : η.stalk x hx (F.to_stalk x hx V hxV HVU s) = G.to_stalk x hx V hxV HVU (η.map V HVU s) :=
quotient.sound ⟨V, hxV, set.subset_inter (set.subset.refl _) HVU, set.subset.refl _,
calc  G.res (V ⊓ U) inf_le_right V HVU (le_inf (le_refl V) HVU) (η.map (V ⊓ U) inf_le_right (F.res V HVU (V ⊓ U) inf_le_right inf_le_left s))
    = G.res V HVU V HVU (le_refl V) (η.map V HVU s) : by rw [η.3, res_res]⟩

instance is_ring_hom_stalk {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) (x : X) (hx : x ∈ U) :
  is_ring_hom (η.stalk x hx) :=
{ map_one := quotient.sound ⟨U, hx, set.subset_inter (set.subset_univ U.1) (set.subset.refl U.1), set.subset_univ U.1,
    by dsimp only; erw [_root_.res_one, η.map_one, _root_.res_one, _root_.res_one]⟩,
  map_mul := λ y z, stalk.induction_on₂ y z $ λ V hxV HVU s t, by rw [stalk_to_stalk, stalk_to_stalk, ← to_stalk_mul, stalk_to_stalk, η.map_mul, to_stalk_mul],
  map_add := λ y z, stalk.induction_on₂ y z $ λ V hxV HVU s t, by rw [stalk_to_stalk, stalk_to_stalk, ← to_stalk_add, stalk_to_stalk, η.map_add, to_stalk_add] }

section
variables {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (η : F.morphism G) (x : X) (hx : x ∈ U)
variables (s t : F.stalk x hx) (n : ℕ)
@[simp] lemma stalk_add : η.stalk x hx (s + t) = η.stalk x hx s + η.stalk x hx t := is_ring_hom.map_add _
@[simp] lemma stalk_zero : η.stalk x hx 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma stalk_neg : η.stalk x hx (-s) = -η.stalk x hx s := is_ring_hom.map_neg _
@[simp] lemma stalk_sub : η.stalk x hx (s - t) = η.stalk x hx s - η.stalk x hx t := is_ring_hom.map_sub _
@[simp] lemma stalk_mul : η.stalk x hx (s * t) = η.stalk x hx s * η.stalk x hx t := is_ring_hom.map_mul _
@[simp] lemma stalk_one : η.stalk x hx 1 = 1 := is_ring_hom.map_one _
@[simp] lemma stalk_pow : η.stalk x hx (s^n) = (η.stalk x hx s)^n := is_semiring_hom.map_pow _ s n
end

end morphism

structure equiv (F : sheaf_of_rings_on_opens.{v} X U) (G : sheaf_of_rings_on_opens.{w} X U) : Type (max u v w) :=
(to_fun : F.morphism G)
(inv_fun : G.to_sheaf_on_opens.morphism F.to_sheaf_on_opens)
(left_inv : ∀ V HVU s, inv_fun.1 V HVU (to_fun.1 V HVU s) = s)
(right_inv : ∀ V HVU s, to_fun.1 V HVU (inv_fun.1 V HVU s) = s)

namespace equiv

def to_sheaf_on_opens {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (e : F.equiv G) :
  F.to_sheaf_on_opens.equiv G.to_sheaf_on_opens :=
{ to_fun := e.1.to_sheaf_on_opens, .. e }

def refl (F : sheaf_of_rings_on_opens.{v} X U) : equiv F F :=
⟨morphism.id F, sheaf_on_opens.morphism.id F.to_sheaf_on_opens, λ _ _ _, rfl, λ _ _ _, rfl⟩

@[simp] lemma refl_apply (F : sheaf_of_rings_on_opens.{v} X U) (V HV s) :
  (refl F).1.1 V HV s = s := rfl

def symm {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{v} X U} (e : equiv F G) : equiv G F :=
⟨{ hom := λ V HVU, (ring_equiv.symm { to_fun := e.1.1 V HVU, inv_fun := e.2.1 V HVU, left_inv := e.3 V HVU, right_inv := e.4 V HVU, hom := e.1.2 V HVU }).hom,
  .. e.2 },
e.1.to_sheaf_on_opens, e.4, e.3⟩

def trans {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{v} X U} {H : sheaf_of_rings_on_opens.{u₁} X U}
  (e₁ : equiv F G) (e₂ : equiv G H) : equiv F H :=
⟨e₂.1.comp e₁.1, e₁.2.comp e₂.2,
λ _ _ _, by rw [morphism.comp_apply, sheaf_on_opens.morphism.comp_apply, e₂.3, e₁.3],
λ _ _ _, by rw [morphism.comp_apply, sheaf_on_opens.morphism.comp_apply, e₁.4, e₂.4]⟩

@[simp] lemma trans_apply {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{v} X U} {H : sheaf_of_rings_on_opens.{u₁} X U}
  (e₁ : equiv F G) (e₂ : equiv G H) (V HV s) :
  (e₁.trans e₂).1.1 V HV s = e₂.1.1 V HV (e₁.1.1 V HV s) :=
rfl

def res_subset {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (e : equiv F G)
  (V : opens X) (HVU : V ≤ U) : equiv (F.res_subset V HVU) (G.res_subset V HVU) :=
⟨e.1.res_subset V HVU, e.2.res_subset V HVU,
λ _ _ _, by rw [morphism.res_subset_apply, sheaf_on_opens.morphism.res_subset_apply, e.3],
λ _ _ _, by rw [morphism.res_subset_apply, sheaf_on_opens.morphism.res_subset_apply, e.4]⟩

@[simp] lemma res_subset_apply {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (e : equiv F G)
  (V : opens X) (HVU : V ≤ U) (W HW s) :
  (e.res_subset V HVU).1.1 W HW s = e.1.1 W (le_trans HW HVU) s :=
rfl

def stalk {F : sheaf_of_rings_on_opens.{v} X U} {G : sheaf_of_rings_on_opens.{w} X U} (e : equiv F G) (x : X) (hx : x ∈ U) :
  F.stalk x hx ≃ G.stalk x hx :=
{ to_fun := e.1.stalk x hx,
  inv_fun := e.2.stalk x hx,
  left_inv := λ g, stalk.induction_on g $ λ V hxV HVU s, by rw [morphism.stalk_to_stalk, to_stalk, sheaf_on_opens.morphism.stalk_to_stalk, e.3]; refl,
  right_inv := λ g, stalk.induction_on g $ λ V hxV HVU s, by rw [to_stalk, sheaf_on_opens.morphism.stalk_to_stalk, ← to_stalk, morphism.stalk_to_stalk, e.4]; refl }

end equiv

def sheaf_glue {I : Type u} (S : I → opens X) (F : Π (i : I), sheaf_of_rings_on_opens.{v} X (S i))
  (φ : Π i j, equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right)) :
  sheaf_of_rings_on_opens.{max u v} X (⋃S) :=
{ F :=
  { Fring := λ U, @subtype.comm_ring (Π (i : I), (F i).eval (S i ⊓ U) inf_le_left) _
      { f | ∀ (i j : I), (φ i j).1.map (S i ⊓ S j ⊓ U) inf_le_left
              ((F i).res (S i ⊓ U) inf_le_left (S i ⊓ S j ⊓ U) (le_trans inf_le_left inf_le_left)
                (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
                (f i)) =
            (F j).res (S j ⊓ U) inf_le_left (S i ⊓ S j ⊓ U) (le_trans inf_le_left inf_le_right)
              (by rw inf_assoc; exact inf_le_right)
              (f j) }
      { add_mem := λ f g hf hg i j, by erw [res_add, morphism.map_add, res_add, hf i j, hg i j],
        zero_mem := λ i j, by erw [res_zero, morphism.map_zero, res_zero]; refl,
        neg_mem := λ f hf i j, by erw [res_neg, morphism.map_neg, res_neg, hf i j],
        one_mem := λ i j, by erw [res_one, morphism.map_one, res_one]; refl,
        mul_mem := λ f g hf hg i j, by erw [res_mul, morphism.map_mul, res_mul, hf i j, hg i j] },
    res_is_ring_hom := λ U V HVU,
      { map_one := subtype.eq $ funext $ λ i, res_one _ _ _ _ _ _,
        map_mul := λ f g, subtype.eq $ funext $ λ i, res_mul _ _ _ _ _ _ _ _,
        map_add := λ f g, subtype.eq $ funext $ λ i, res_add _ _ _ _ _ _ _ _ },
    .. (sheaf_on_opens.sheaf_glue S (λ i, (F i).to_sheaf_on_opens) (λ i j, (φ i j).to_sheaf_on_opens)).F }
  .. sheaf_on_opens.sheaf_glue S (λ i, (F i).to_sheaf_on_opens) (λ i j, (φ i j).to_sheaf_on_opens) }

@[simp] lemma sheaf_glue_res_val {I : Type u} (S : I → opens X) (F : Π (i : I), sheaf_of_rings_on_opens.{v} X (S i))
  (φ : Π i j, equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right))
  (U HU V HV HVU s i) : ((sheaf_glue S F φ).res U HU V HV HVU s).1 i = (F i).res _ _ _ _ (inf_le_inf (le_refl _) HVU) (s.1 i) := rfl

def universal_property (I : Type u) (S : I → opens X) (F : Π (i : I), sheaf_of_rings_on_opens.{v} X (S i))
  (φ : Π i j, equiv ((F i).res_subset ((S i) ⊓ (S j)) inf_le_left) ((F j).res_subset ((S i) ⊓ (S j)) inf_le_right))
  (Hφ1 : ∀ i V HV s, (φ i i).1.1 V HV s = s)
  (Hφ2 : ∀ i j k V HV1 HV2 HV3 s, (φ j k).1.1 V HV1 ((φ i j).1.1 V HV2 s) = (φ i k).1.1 V HV3 s)
  (i : I) :
  equiv (res_subset (sheaf_glue S F φ) (S i) (le_supr S i)) (F i) :=
{ to_fun :=
  { hom := λ U HU,
    { map_one := res_one _ _ _ _ _ _,
      map_mul := λ x y, res_mul _ _ _ _ _ _ _ _,
      map_add := λ x y, res_add _ _ _ _ _ _ _ _ },
    .. (sheaf_on_opens.universal_property I S (λ i, (F i).to_sheaf_on_opens) (λ i j, (φ i j).to_sheaf_on_opens) Hφ1 Hφ2 i).1 },
  .. sheaf_on_opens.universal_property I S (λ i, (F i).to_sheaf_on_opens) (λ i j, (φ i j).to_sheaf_on_opens) Hφ1 Hφ2 i }

end sheaf_of_rings_on_opens
