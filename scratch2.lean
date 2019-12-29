import tactic

def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}

example (X : Type) (R : X → X → Prop) (HR : equivalence R) : ∀ (c d : set X),
  c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x} →
  d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x} → c ∩ d ≠ ∅ → c = d :=
begin
  intros c d hc hd hcd,
  /-
  1 goal
X : Type,
R : X → X → Prop,
HR : equivalence R,
c d : set X,
hc : c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x},
hd : d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x},
hcd : c ∩ d ≠ ∅
⊢ c = d
-/
  suffices htemp : ∀ (X : Type) (R : X → X → Prop) (HR : equivalence R) (c d : set X)
    (hc : c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x})
    (hd : d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x})
    (hcd : c ∩ d ≠ ∅), c ⊆ d, -- I want this to be my final goal
    apply set.subset.antisymm,
      exact htemp X R HR c d (by assumption) (by assumption) (by assumption),
    suffices htemp2 : d ∩ c ≠ ∅, -- I want this to be the last but one goal
      exact htemp X R HR d c (by assumption) (by assumption) (htemp2), -- `by assumption` fails for htemp2
    /- currently two goals.
     first is
     ⊢ d ∩ c ≠ ∅
     and we have a hypothesis
     hcd : c ∩ d ≠ ∅,
    -/
    sorry,
    /- other goal is overkill currently:

      X : Type,
      R : X → X → Prop,
      HR : equivalence R,
      c d : set X,
      hc : c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x},
      hd : d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x},
      hcd : c ∩ d ≠ ∅
      ⊢ ∀ (X : Type) (R : X → X → Prop),
        equivalence R →
        ∀ (c d : set X),
        c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x} →
        d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x} → c ∩ d ≠ ∅ → c ⊆ d
    -/
    clear hcd hd hc c d HR R X,
    intros X R HR c d hc hd hcd,
    /-
    X : Type,
    R : X → X → Prop,
    HR : equivalence R,
    c d : set X,
    hc : c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x},
    hd : d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x},
    hcd : c ∩ d ≠ ∅
    ⊢ c ⊆ d
    -/
    sorry
  end

  #exit

  and second is

  ...[can all be deleted]
  ⊢ ∀ (X : Type) (R : X → X → Prop),
    equivalence R →
    ∀ (c d : set X),
      c ∈ {S : set X | ∃ (x : X), S = equivalence_class R x} →
      d ∈ {S : set X | ∃ (x : X), S = equivalence_class R x} → c ∩ d ≠ ∅ → c ⊆ d

  -/
end
