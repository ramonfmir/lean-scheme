/-
  Sheaf (of types) on standard basis.

  https://stacks.math.columbia.edu/tag/009L
-/

import topology.basic
import to_mathlib.opens
import sheaves.covering.covering_on_standard_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

namespace sheaf_on_standard_basis

variables {α : Type u} [topological_space α] 
variables {B : set (opens α)} {HB : opens.is_basis B}
variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

include Bstd

section properties

-- Compactness definition.

-- Basis elementsfinite subcover
def basis_is_compact : Prop := 
∀ {U} (BU : U ∈ B) (OC : covering_standard_basis B U),
∃ (γ : Type u) (Hfin : fintype γ) (f : γ → OC.γ), (⋃ (OC.Uis ∘ f)) = U

end properties

section sheaf_condition

-- Restriction map from U to U ∩ V.

def res_to_inter_left (F : presheaf_on_basis α HB) {U V} (BU : U ∈ B) (BV : V ∈ B) 
: (F BU) → (F (Bstd.2 BU BV)) :=
F.res BU (Bstd.2 BU BV) (set.inter_subset_left U V)

@[simp] lemma res_to_inter_left'
(F : presheaf_on_basis α HB) {U V} (BU : U ∈ B) (BV : V ∈ B)
: sheaf_on_standard_basis.res_to_inter_left Bstd F BU BV =
  F.res BU (Bstd.2 BU BV) (set.inter_subset_left U V) 
:= rfl

-- Restriction map from V to U ∩ V.

def res_to_inter_right (F : presheaf_on_basis α HB) {U V} (BU : U ∈ B) (BV : V ∈ B) 
: (F BV) → (F (Bstd.2 BU BV)) :=
F.res BV (Bstd.2 BU BV) (set.inter_subset_right U V)

@[simp] lemma res_to_inter_right'
(F : presheaf_on_basis α HB) {U V} (BU : U ∈ B) (BV : V ∈ B)
: sheaf_on_standard_basis.res_to_inter_right Bstd F BU BV = 
  F.res BV (Bstd.2 BU BV) (set.inter_subset_right U V) 
:= rfl

-- Sheaf condition.

def locality 
(F : presheaf_on_basis α HB) {U} (BU : U ∈ B) (OC : covering_standard_basis B U) :=
∀ (s t : F BU), 
(∀ i, F.res BU (OC.BUis i) (subset_covering i) s = 
      F.res BU (OC.BUis i) (subset_covering i) t) → 
s = t

def gluing 
(F : presheaf_on_basis α HB) {U} (BU : U ∈ B) (OC : covering_standard_basis B U) :=
∀ (s : Π i, F (OC.BUis i)),
(∀ j k, sheaf_on_standard_basis.res_to_inter_left Bstd F (OC.BUis j) (OC.BUis k) (s j) =
        sheaf_on_standard_basis.res_to_inter_right Bstd F (OC.BUis j) (OC.BUis k) (s k)) → 
∃ S, ∀ i, F.res BU (OC.BUis i) (subset_covering i) S = s i

def is_sheaf_on_standard_basis (F : presheaf_on_basis α HB) :=
∀ {U} (BU : U ∈ B) (OC : covering_standard_basis B U),
locality Bstd F BU OC ∧ gluing Bstd F BU OC

end sheaf_condition

section cofinal_system

-- Suffices to prove the sheaf condition for finite covers.

def is_sheaf_on_standard_basis_cofinal_system (F : presheaf_on_basis α HB) : Prop :=
∀ {U} (BU : U ∈ B) (OC : covering_standard_basis B U) (Hfin : fintype OC.γ),
locality Bstd F BU OC ∧ gluing Bstd F BU OC

theorem cofinal_systems_coverings_standard_case
(F : presheaf_on_basis α HB) 
(Hcompact : basis_is_compact Bstd)
: is_sheaf_on_standard_basis_cofinal_system Bstd F → is_sheaf_on_standard_basis Bstd F :=
begin
  intros Hcofinal,
  have Hcofinal' := @Hcofinal,
  intros U BU OC,
  rcases (Hcompact BU OC) with ⟨γ, Hfinγ, fγ, Hcov⟩,
  have BUisfin : ∀ i, ((OC.Uis ∘ fγ) i) ∈ B := λ i, OC.BUis (fγ i),
  let OCfin : covering_standard_basis B U 
    := {γ := γ, Uis := OC.Uis ∘ fγ, Hcov := Hcov, BUis := BUisfin},
  replace Hcofinal := Hcofinal BU OCfin Hfinγ, 
  rcases Hcofinal with ⟨Hloc, Hglue⟩,
  split,
  -- Locality.
  { intros s t Hres,
    apply Hloc,
    intros i,
    apply Hres, },
  -- Gluing.
  { intros s Hinter,
    have Hinterfin 
    : ∀ (j k), 
      sheaf_on_standard_basis.res_to_inter_left Bstd F _ _ (s (fγ j)) = 
      sheaf_on_standard_basis.res_to_inter_right Bstd F _ _ (s (fγ k)) :=
    λ j k, Hinter (fγ j) (fγ k),
    have Hglobal := Hglue (λ i, s (fγ i)) Hinterfin,
    rcases Hglobal with ⟨S, HS⟩,
    existsi S,
    intros i,
    let Vjs := λ j : γ, (OCfin.Uis j) ∩ (OC.Uis i),
    have BVjs : ∀ j, (Vjs j) ∈ B := λ j, Bstd.2 (OCfin.BUis j) (OC.BUis i),
    have HVjscov : (⋃ Vjs) = OC.Uis i,
      apply opens.ext,
      apply set.ext,
      intros x,
      split,
      { intros HxUVjs,
        rcases HxUVjs with ⟨Vj, HVj, HxVj⟩,
        rcases HVj with ⟨VjO, ⟨⟨j, HVjO⟩, HVjeq⟩⟩,
        rw [←HVjeq, ←HVjO] at HxVj,
        exact HxVj.2, },
      { intros HxUi,
        have HxU : x ∈ U := OC.Hcov ▸ (opens_supr_mem OC.Uis i x HxUi),
        rw ←Hcov at HxU,
        rcases HxU with ⟨Uj, HUj, HxUj⟩,
        rcases HUj with ⟨UjO, ⟨⟨j, HUjO⟩, HUjeq⟩⟩,
        use [(Vjs j).1, ⟨(Vjs j), ⟨⟨j, rfl⟩, rfl⟩⟩],
        rw [←HUjeq, ←HUjO] at HxUj,
        exact ⟨HxUj, HxUi⟩, },
    have HVjUVjs : ∀ j, Vjs j ⊆ OC.Uis i 
      := HVjscov ▸ λ j x Hx, opens_supr_mem Vjs j x Hx,
    have HVjU : ∀ j, Vjs j ⊆ U
      := λ j, set.subset.trans (HVjUVjs j) (subset_covering i),
    let Ui : opens α := OC.Uis i,
    let BUi : Ui ∈ B := OC.BUis i,
    let OCfin' : covering_standard_basis B Ui 
      := {γ := γ, Uis := Vjs, Hcov := HVjscov, BUis := BVjs},
    have Hloc' := (@Hcofinal' Ui BUi OCfin' Hfinγ).1,
    have Hglue' := (@Hcofinal' Ui BUi OCfin' Hfinγ).2,
    have Hglue'' := Hglue' (λ j, F.res BU (BVjs j) (HVjU j) S),
    have Hres' : ∀ (j k),
      sheaf_on_standard_basis.res_to_inter_left Bstd 
        F (BVjs j) (BVjs k) (F.res BU (BVjs j) (HVjU j) S) = 
      sheaf_on_standard_basis.res_to_inter_right Bstd 
        F (BVjs j) (BVjs k) (F.res BU (BVjs k) (HVjU k) S),
      intros j k,
      simp,
      rw ←F.Hcomp',
      rw ←F.Hcomp',
    rcases (Hglue'' Hres') with ⟨S', HS'⟩,
    refine @eq.trans _ _ S' _ _ _,
    { apply Hloc',
      intro j,
      rw HS',
      rw ←F.Hcomp',
      refl, },
    { apply eq.symm,
      apply Hloc',
      intro j,
      simp at Hinter,
      erw ←Hinter,
      rw HS',
      have Hsfj : s (fγ j) = _ := (HS j).symm,
      rw Hsfj,
      rw ←F.Hcomp',
      refl, }, },
end

end cofinal_system

end sheaf_on_standard_basis
