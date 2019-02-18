/-
  Sheaf (of types) on standard basis.

  https://stacks.math.columbia.edu/tag/009L
-/


-- /- The lemma in this tag says that if we have a top space
-- and a basis with the property that the intersection of two
-- basis elements is in the basis, then to give a sheaf on B
-- is to give a "sheaf on a cofinal system of covers of B".
-- In the application to schemes, this means a presheaf with
-- the property that it satisfies the sheaf axiom for
-- finite covers of basic opens by basic opens, noting that
-- the intersection of two basis opens is a basic open.
-- -/

import preliminaries.opens
import preliminaries.covering_on_standard_basis
import topology.basic
import sheaves.presheaf
import sheaves.stalk_on_basis
import sheaves.presheaf_of_rings_on_basis

universe u 

open topological_space

section sheaf_on_standard_basis

parameters {α : Type u} [topological_space α] 
parameters {B : set (opens α)} [HB : opens.is_basis B]

-- Standard basis. TODO: Move somewhere else?

def opens.univ : opens α := ⟨set.univ, is_open_univ⟩
parameters {Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B}

section properties

-- Compactness definition.
-- TODO : Finite subcover stuff can be moved to preliminaries.

def basis_is_compact : Prop := 
∀ {U} (BU : U ∈ B) (OC : covering_standard_basis B U),
∃ (γ : Type u) (Hfin : fintype γ) (f : γ → OC.γ), (⋃ (OC.Uis ∘ f)) = U

end properties

section sheaf_condition

-- Restriction map from U to U ∩ V.

@[reducible] def res_to_inter_left' (F : presheaf_on_basis α HB) {U V} (BU : U ∈ B) (BV : V ∈ B) 
: (F BU) → (F (Bstd.2 BU BV)) :=
F.res BU (Bstd.2 BU BV) (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

@[reducible] def res_to_inter_right' (F : presheaf_on_basis α HB) {U V} (BU : U ∈ B) (BV : V ∈ B) 
: (F BV) → (F (Bstd.2 BU BV)) :=
F.res BV (Bstd.2 BU BV) (set.inter_subset_right U V)

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
(∀ j k, F.res (OC.BUis j) (Bstd.2 (OC.BUis j) (OC.BUis k)) (set.inter_subset_left _ _) (s j) =
        F.res (OC.BUis k) (Bstd.2 (OC.BUis j) (OC.BUis k)) (set.inter_subset_right _ _) (s k)) → 
∃ S, ∀ i, F.res BU (OC.BUis i) (subset_covering i) S = s i

def is_sheaf_on_standard_basis (F : presheaf_on_basis α HB) :=
∀ {U} (BU : U ∈ B) (OC : covering_standard_basis B U),
locality F BU OC ∧ gluing F BU OC

end sheaf_condition

section cofinal_system

def is_sheaf_on_standard_basis_cofinal_system (F : presheaf_on_basis α HB) :=
∀ {U} (BU : U ∈ B) (OC : covering_standard_basis B U) (Hfin : fintype OC.γ),
locality F BU OC ∧ gluing F BU OC

theorem cofinal_systems_coverings_standard_case
(F : presheaf_on_basis α HB) 
(Hcompact : basis_is_compact)
: is_sheaf_on_standard_basis_cofinal_system F → is_sheaf_on_standard_basis F :=
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
    apply Hres,
  },
  -- Gluing.
  { intros s Hinter,
    let sfin := λ i, (s (fγ i)),
    have Hinterfin 
    : ∀ (j k), res_to_inter_left' F _ _ (sfin j) = res_to_inter_right' F _ _ (sfin k) :=
    λ j k, Hinter (fγ j) (fγ k),
    have Hglobal := Hglue sfin Hinterfin,
    rcases Hglobal with ⟨S, HS⟩,
    existsi S,
    intros i,
    let Vjs := λ j, (OCfin.Uis j) ∩ (OC.Uis i),
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
        exact ⟨HxUj, HxUi⟩,
      },
    have HVjUVjs : ∀ j, Vjs j ⊆ OC.Uis i 
      := HVjscov ▸ λ j x Hx, opens_supr_mem Vjs j x Hx,
    have HVjU : ∀ j, Vjs j ⊆ U
      := λ j, set.subset.trans (HVjUVjs j) (subset_covering i),
    -- Cover Ui.
    let Ui : opens α := OC.Uis i,
    let BUi : Ui ∈ B := OC.BUis i,
    let OCfin' : covering_standard_basis B (OC.Uis i) 
      := {γ := γ, Uis := Vjs, Hcov := HVjscov, BUis := BVjs},
    have Hglue' := (@Hcofinal' Ui BUi OCfin' Hfinγ).2,
    have Hglue'' := Hglue' (λ j, F.res BU (BVjs j) (HVjU j) S),
    have Hres' : ∀ (j k),
      res_to_inter_left' F (BVjs j) (BVjs k) (F.res BU (BVjs j) (HVjU j) S) = 
      res_to_inter_right' F (BVjs j) (BVjs k) (F.res BU (BVjs k) (HVjU k) S),
      intros j k,
      let Vj := Vjs j,
      let Vk := Vjs k,
      let Vjk := Vj ∩ Vk,
      have BVj := BVjs j,
      have BVk := BVjs k,
      have BVjk := Bstd.2 BVj BVk,
      -- show ((F.res BVj BVjk (set.inter_subset_left _ _)) ∘ (FPTB.res BU BVj (HVjU j))) S = 
      --      ((F.res BVk BVjk (set.inter_subset_right _ _)) ∘ (FPTB.res BU BVk (HVjU k))) S,
      -- rw ←(FPTB.Hcomp U Vj1 Vj12 BU BVj1 BVj12 _ _),
      -- rw ←(FPTB.Hcomp U Vj2 Vj12 BU BVj2 BVj12 _ _),
      sorry,
    sorry,
  },
end

end cofinal_system

end sheaf_on_standard_basis
