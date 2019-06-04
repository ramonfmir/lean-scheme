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

infix `⟶`:80 := morphism 

section morphism

def comp {F G H : presheaf_on_basis α HB} (fg : F ⟶ G) (gh : G ⟶ H) : F ⟶ H :=
{ map := λ U HU, gh.map HU ∘ fg.map HU,
  commutes := λ U V BU BV HVU,
    begin
      rw [←function.comp.assoc, gh.commutes BU BV HVU], symmetry,
      rw [function.comp.assoc, ←fg.commutes BU BV HVU]
    end }

infix `⊚`:80 := comp

def id (F : presheaf_on_basis α HB) : F ⟶ F :=
{ map := λ U BU, id,
  commutes := λ U V BU BV HVU, by simp, }

structure iso (F G : presheaf_on_basis α HB) :=
(mor : F ⟶ G)
(inv : G ⟶ F)
(mor_inv_id : mor ⊚ inv = id F)
(inv_mor_id : inv ⊚ mor = id G)

infix `≅`:80 := iso

end morphism

end presheaf_on_basis
