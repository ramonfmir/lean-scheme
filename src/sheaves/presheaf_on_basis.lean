/-
  Presheaf (of types) on basis.

  https://stacks.math.columbia.edu/tag/009I
-/

import topology.basic
import topology.opens

universes u v

open topological_space

-- Presheaf of types where we only define sections on basis elements.

structure presheaf_on_basis (α : Type u) [T : topological_space α] 
{B : set (opens α)} (HB : opens.is_basis B) := 
(F     : Π {U}, U ∈ B → Type v)
(res   : ∀ {U V} (BU : U ∈ B) (BV : V ∈ B) (HVU : V ⊆ U), F BU → F BV)
(Hid   : ∀ {U} (BU : U ∈ B), (res BU BU (set.subset.refl U)) = id)  
(Hcomp : ∀ {U V W} (BU : U ∈ B) (BV : V ∈ B) (BW : W ∈ B)
  (HWV : W ⊆ V) (HVU : V ⊆ U),
  res BU BW (set.subset.trans HWV HVU) = (res BV BW HWV) ∘ (res BU BV HVU))

namespace presheaf_on_basis

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α)} {HB : opens.is_basis B}

instance : has_coe_to_fun (presheaf_on_basis α HB) :=
{ F := λ _, Π {U}, U ∈ B → Type v,
  coe := presheaf_on_basis.F }

-- Simplification lemmas.

@[simp] lemma Hid' (F : presheaf_on_basis α HB) :
∀ {U} (BU : U ∈ B) (s : F BU),
  (F.res BU BU (set.subset.refl U)) s = s := 
λ U OU s, by rw F.Hid OU; simp

@[simp] lemma Hcomp' (F : presheaf_on_basis α HB) :
∀ {U V W} (BU : U ∈ B) (BV : V ∈ B) (BW : W ∈ B)
  (HWV : W ⊆ V) (HVU : V ⊆ U) (s : F BU),
  (F.res BU BW (set.subset.trans HWV HVU)) s = 
  (F.res BV BW HWV) ((F.res BU BV HVU) s) := 
λ U V W OU OV OW HWV HVU s, by rw F.Hcomp OU OV OW HWV HVU

-- Morphism of presheaves on a basis (same as presheaves).

structure morphism (F G : presheaf_on_basis α HB) :=
(map      : ∀ {U} (HU : U ∈ B), F HU → G HU)
(commutes : ∀ {U V} (HU : U ∈ B) (HV : V ∈ B) (Hsub : V ⊆ U),
  (G.res HU HV Hsub) ∘ (map HU) = (map HV) ∘ (F.res HU HV Hsub))

namespace morphism

definition comp
  {F G H : presheaf_on_basis α HB}
  (fg : morphism F G)
  (gh : morphism G H) :
  morphism F H :=
{ map := λ U HU, gh.map HU ∘ fg.map HU,
  commutes := λ U V BU BV HVU,
    begin
      rw [←function.comp.assoc, gh.commutes BU BV HVU], symmetry,
      rw [function.comp.assoc, ←fg.commutes BU BV HVU]
    end }

definition is_identity {F : presheaf_on_basis α HB} (ff : morphism F F) :=
  ∀ {U} (HU : U ∈ B), ff.map HU = id 

definition is_isomorphism {F G : presheaf_on_basis α HB} (fg : morphism F G) := 
  ∃ gf : morphism G F, 
  is_identity (comp fg gf)
∧ is_identity (comp gf fg)

end morphism

-- Isomorphic presheaves of types on a basis.

def are_isomorphic (F G : presheaf_on_basis α HB) :=
∃ (fg : morphism F G) (gf : morphism G F),
    morphism.is_identity (morphism.comp fg gf)
  ∧ morphism.is_identity (morphism.comp gf fg)

end presheaf_on_basis
