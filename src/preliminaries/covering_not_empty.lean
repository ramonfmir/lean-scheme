/-
  This is not really useful... I had some issues with having empty sets in the
  covering, but I'm trying to solve it in a different way.
-/

import topology.basic
import preliminaries.opens
import preliminaries.covering

universe u

local attribute [instance] classical.prop_decidable

open topological_space lattice

variables {X : Type u} [topological_space X]

-- Opens.

lemma opens.univ_not_empty [HI : inhabited X] : @opens.univ X _ ≠ @opens.empty X _ :=
begin
    intros HC,
    have Hval : (@opens.univ X _).1 = (@opens.empty X _).1 := by rw HC,
    have Hset : set.univ = ∅ := Hval,
    have Hext := (set.ext_iff _ _).1 Hset,
    have Hx : ∃ x, x ∈ (@set.univ X) := ⟨HI.default, by simp⟩,
    cases Hx with x Hx,
    cases (Hext x).1 Hx,
end

lemma opens.exists_mem_of_ne_empty
: ∀ {U : opens X}, U ≠ opens.empty → ∃ x, x ∈ U :=
begin
    intros U HUne,
    have HUneset : U.1 ≠ ∅ := λ HC, HUne $ opens.ext HC,
    exact set.exists_mem_of_ne_empty HUneset,
end

lemma mem_subset_basis_of_mem_open 
(B : set (opens X)) (HB : opens.is_basis B) (U : opens X)
: U ≠ opens.empty → ∃ V ∈ B, V ⊆ U :=
begin 
  intros Hne,
  have Hnes : U.1 ≠ ∅ := λ HC, Hne (opens.ext HC),
  have Hx := set.ne_empty_iff_exists_mem.1 Hnes,
  rcases Hx with ⟨x, Hx⟩,
  have HU' := opens.is_basis_iff_nbhd.1 HB Hx,
  rcases HU' with ⟨U', HU', ⟨HxU', HU'U⟩⟩,
  use [U', HU', HU'U],
end

-- Covering.

lemma covering.exists_not_empty (U : opens X)
(HU : U ≠ opens.empty) (OC : covering U) : ∃ i, OC.Uis i ≠ opens.empty :=
begin
  apply classical.by_contradiction,
  intros HC,
  rw not_exists at HC,
  simp at HC,
  have Hemp : ⋃ OC.Uis = opens.empty,
    rw (supr_eq_bot.2 HC),
    refl,
  rw OC.Hcov at Hemp,
  exact HU Hemp,
end

noncomputable def covering.all_not_empty.aux (U : opens X)
(HU : U ≠ opens.empty) (OC : covering U) : OC.γ → opens X :=
begin
  have HUi := covering.exists_not_empty U HU OC,
  let i := classical.some HUi,
  intros j,
  exact (if (OC.Uis j = opens.empty) then OC.Uis i else OC.Uis j),
end

private lemma covering.all_not_empty.union (U : opens X)
(HU : U ≠ opens.empty) (OC : covering U) : ⋃ (covering.all_not_empty.aux U HU OC) = U :=
begin
  unfold covering.all_not_empty.aux,
  apply opens.ext,
  apply set.ext,
  intros x,
  split,
  { intros Hx,
    rcases Hx with ⟨Uiset, ⟨Ui, ⟨i, HUi⟩, HUival⟩, HxUi⟩,
    simp at HUi,
    rw ←HUival at HxUi,
    rw ←HUi at HxUi,
    cases (classical.prop_decidable (OC.Uis i = opens.empty)),
    { rw if_neg at HxUi,
      use (subset_covering _) HxUi, },
    { rw if_pos at HxUi,
      use (subset_covering _) HxUi,
      use h, } },
  { intros Hx,
    rw ←OC.Hcov at Hx,
    rcases Hx with ⟨Uiset, ⟨Ui, ⟨i, HUi⟩, HUival⟩, HxUi⟩,
    have HUine : OC.Uis i ≠ opens.empty,
      intros HC,
      rw ←HUival at HxUi,
      rw ←HUi at HxUi,
      rw HC at HxUi,
      cases HxUi,
    use [Ui.val],
    simp,
    use [Ui.property, i],
    rw if_neg,
    { exact HUi, },
    { exact HUine, },
    { rw HUival,
      exact HxUi, }, }
end

noncomputable lemma covering.all_not_empty (U : opens X)
(HU : U ≠ opens.empty) (OC : covering U) : covering U :=
begin
  have HUi := covering.exists_not_empty U HU OC,
  let i := classical.some HUi,
  let Hi := classical.some_spec HUi,
  exact { γ := OC.γ, 
          Uis := covering.all_not_empty.aux U HU OC,
          Hcov := covering.all_not_empty.union U HU OC }
end
