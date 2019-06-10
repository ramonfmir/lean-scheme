import sheaves.sheaf

universes v w u₁ v₁ u

open topological_space

def sheaf_on_opens (X : Type u) [topological_space X] (U : opens X) : Type (max u (v+1)) :=
sheaf.{u v} X

namespace sheaf_on_opens

variables {X : Type u} [topological_space X] {U : opens X}

def eval (F : sheaf_on_opens X U) (V : opens X) (HVU : V ⊆ U) : Type v :=
presheaf.F (sheaf.F F) V

def res (F : sheaf_on_opens X U) (V : opens X) (HVU : V ⊆ U) (W : opens X) (HWU : W ⊆ U) (HWV : W ⊆ V) : F.eval V HVU → F.eval W HWU :=
presheaf.res _ _ _ HWV

def res_subset (F : sheaf_on_opens X U) (V : opens X) (HVU : V ⊆ U) : sheaf_on_opens X V :=
F

structure morphism (F : sheaf_on_opens.{v} X U) (G : sheaf_on_opens.{w} X U) : Type (max u v w) :=
(map : ∀ V ⊆ U, F.eval V H → G.eval V H)
(commutes : ∀ (V : opens X) (HV : V ⊆ U) (W : opens X) (HW : W ⊆ U) (HWV : W ⊆ V) (x),
  map W HW (F.res V HV W HW HWV x) = G.res V HV W HW HWV (map V HV x))

namespace morphism

protected def id (F : sheaf_on_opens.{v} X U) : F.morphism F :=
{ map := λ V HV, id,
  commutes := λ V HV W HW HWV x, rfl }

def comp {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} {H : sheaf_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) : F.morphism H :=
{ map := λ V HV x, η.map V HV (ξ.map V HV x),
  commutes := λ V HV W HW HWV x, by rw [ξ.commutes, η.commutes] }

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

def res_subset {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (η : F.morphism G) (V : opens X) (HVU : V ⊆ U) :
  (F.res_subset V HVU).morphism (G.res_subset V HVU) :=
{ map := λ W HWV, η.map W (set.subset.trans HWV HVU),
  commutes := λ S HSV T HTV, η.commutes S (set.subset.trans HSV HVU) T (set.subset.trans HTV HVU) }

@[simp] lemma comp_res_subset {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} {H : sheaf_on_opens.{u₁} X U}
  (η : G.morphism H) (ξ : F.morphism G) (V : opens X) (HVU : V ⊆ U) :
  (η.res_subset V HVU).comp (ξ.res_subset V HVU) = (η.comp ξ).res_subset V HVU :=
rfl

@[simp] lemma id_res_subset {F : sheaf_on_opens.{v} X U} (V : opens X) (HVU : V ⊆ U) :
  (morphism.id F).res_subset V HVU = morphism.id (F.res_subset V HVU) :=
rfl

end morphism

structure equiv (F : sheaf_on_opens.{v} X U) (G : sheaf_on_opens.{w} X U) : Type (max u v w) :=
(to_fun : morphism F G)
(inv_fun : morphism G F)
(left_inv : inv_fun.comp to_fun = morphism.id F)
(right_inv : to_fun.comp inv_fun = morphism.id G)

namespace equiv

def refl (F : sheaf_on_opens.{v} X U) : equiv F F :=
⟨morphism.id F, morphism.id F, rfl, rfl⟩

def symm {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{v} X U} (e : equiv F G) : equiv G F :=
⟨e.2, e.1, e.4, e.3⟩

def trans {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{v} X U} {H : sheaf_on_opens.{u₁} X U}
  (e₁ : equiv F G) (e₂ : equiv G H) : equiv F H :=
⟨e₂.1.comp e₁.1, e₁.2.comp e₂.2,
by rw [morphism.comp_assoc, ← e₂.2.comp_assoc, e₂.3, morphism.id_comp, e₁.3],
by rw [morphism.comp_assoc, ← e₁.1.comp_assoc, e₁.4, morphism.id_comp, e₂.4]⟩

def res_subset {F : sheaf_on_opens.{v} X U} {G : sheaf_on_opens.{w} X U} (e : equiv F G)
  (V : opens X) (HVU : V ⊆ U) : equiv (F.res_subset V HVU) (G.res_subset V HVU) :=
⟨e.1.res_subset V HVU, e.2.res_subset V HVU,
by rw [morphism.comp_res_subset, e.3, morphism.id_res_subset],
by rw [morphism.comp_res_subset, e.4, morphism.id_res_subset]⟩

end equiv

def glue (S : set (opens X)) (F : Π U ∈ S, sheaf_on_opens.{v} X U)
  (φ : Π (U : opens X) (HU : U ∈ S) (V : opens X) (HV : V ∈ S),
    equiv ((F U HU).res_subset (U ∩ V) (set.inter_subset_left _ _)) ((F V HV).res_subset (U ∩ V) (set.inter_subset_right _ _)))
  (Hφ1 : ∀ U HU, φ U HU U HU = equiv.refl (F U HU))
  (Hφ2 : ∀ (U : opens X) (HU : U ∈ S) (V : opens X) (HV : V ∈ S) (W : opens X) (HW : W ∈ S),
    ((φ U HU V HV).res_subset (U ∩ V ∩ W) (set.inter_subset_left _ _)).trans
      ((φ V HV W HW).res_subset (U ∩ V ∩ W) (set.subset_inter (set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_right _ _))) =
    (φ U HU W HW).res_subset (U ∩ V ∩ W) (set.subset_inter (set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_left _ _)) (set.inter_subset_right _ _))) :
  sheaf_on_opens.{max u v} X (lattice.Sup S) :=
{ F :=
  { F := λ S, { f : Π U H, (F U H).eval (U ∩ S) (set.inter_subset_left _ _) //
      ∀ U HU V HV, (φ U HU V HV).1.map (U ∩ V ∩ S) (set.inter_subset_left _ _)
        ((F U HU).res (U ∩ S) _ _ (set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_left _ _))
          (set.subset_inter (set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_left _ _)) (set.inter_subset_right _ _))
          (f U HU)) =
        (F V HV).res (V ∩ S) _ _ (set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_right _ _))
          (set.subset_inter (set.subset.trans (set.inter_subset_left _ _) (set.inter_subset_right _ _)) (set.inter_subset_right _ _))
          (f V HV) },
    res := sorry,
    Hid := sorry,
    Hcomp := sorry },
  locality := sorry,
  gluing := sorry }

end sheaf_on_opens
