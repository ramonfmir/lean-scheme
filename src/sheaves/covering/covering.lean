/-
  Package the definition of an open cover of an open set.
-/

import topology.basic
import topology.opens
import to_mathlib.opens

universes u

open topological_space lattice

section covering

variables {α : Type u} [topological_space α]

-- Open cover.

structure covering (U : opens α) :=
{γ    : Type u}
(Uis  : γ → opens α)
(Hcov : ⋃ Uis = U)

variable (α)

def covering.univ := covering (@opens.univ α _)

variable {α}

-- If ⋃ Ui = U then for all i, Ui ⊆ U.

lemma subset_covering {U : opens α} {OC : covering U} :
∀ i, OC.Uis i ⊆ U :=
λ i x Hx, OC.Hcov ▸ opens_supr_mem OC.Uis i x Hx

-- Make covering from standard definition. Used for instance in compactness.

def opens.from_sets {A : Type*} [topological_space A]
: set (set A) → set (opens A) := λ C, { x | x.1 ∈ C }

lemma opens.from_sets.eq {A : Type*} [topological_space A]
(S : set (set A)) (HS : ∀ (t : set A), t ∈ S → is_open t)
: subtype.val '' (opens.from_sets S) = S :=
set.ext $ λ x, ⟨
  λ ⟨x', Hx', Hval⟩, Hval ▸ Hx',
  λ Hx, by simp [HS x Hx]; by exact Hx⟩

@[reducible] def covering.from_cover {A : Type*} [topological_space A]
(U     : opens A)
(C     : set (set A))
(HC    : ∀ (t : set A), t ∈ C → is_open t)
(Hcov : U.1 = ⋃₀ C)
: covering U :=
{ γ := opens.from_sets C,
  Uis := λ x, x,
  Hcov :=
    begin
      apply subtype.ext.2,
      rw Hcov,
      apply set.ext,
      intros x,
      split,
      { intros Hx,
        rcases Hx with ⟨U, HU, HxU⟩,
        existsi U,
        simp at HU,
        rcases HU with ⟨OU, HU⟩,
        rw ←opens.from_sets.eq C HC,
        split,
        { simp [HU],
          use OU, },
        { exact HxU, } },
      { intros Hx,
        rcases Hx with ⟨U, HU, HxU⟩,
        use U,
        simp,
        use (HC U HU),
        { simp [opens.from_sets],
          exact HU, },
        { exact HxU, }  }
    end, }

lemma covering.from_cover.Uis {A : Type*} [topological_space A]
(U     : opens A)
(C     : set (set A))
(HC    : ∀ (t : set A), t ∈ C → is_open t)
(Hcov : U.1 = ⋃₀ C)
: ∀ i, ((covering.from_cover U C HC Hcov).Uis i).1 ∈ C :=
begin
  intros i,
  simp [covering.from_cover] at *,
  cases i with i Hi,
  simp,
  simp [opens.from_sets] at *,
  exact Hi,
end

-- TODO -- should be in mathlib?
lemma opens.supr_val {X γ : Type*} [topological_space X] (ι : γ → opens X) :
  (⨆ i, ι i).val = ⨆ i, (ι i).val :=
@galois_connection.l_supr (opens X) (set X) _ _ _ (subtype.val : opens X → set X)
    opens.interior opens.gc _

--lemma opens.supr_comap_val {X Y : Type*} [topological_space X] [topological_space Y] {f : X → Y}
--  (hf : continuous f) {γ : Type*}
--  (ι : γ → opens Y) :
--(⨆ (j : γ), hf.comap (ι j)).val = set.Union (λ (j : γ), f ⁻¹' (ι j).val) :=
--by simp [set.ext_iff, opens.supr_val, continuous.comap]

/-- pullback of a covering is a covering -/
def covering.comap {X Y : Type*} [topological_space X] [topological_space Y]
  {U : opens Y} (OC : covering U) {f : X → Y} (hf : continuous f) : covering (hf.comap U) :=
{ γ := OC.γ,
  Uis := λ i, hf.comap $ OC.Uis i,
  Hcov := by simp [subtype.ext, continuous.comap, (subtype.ext.1 OC.Hcov).symm, opens.supr_val]
}

end covering
