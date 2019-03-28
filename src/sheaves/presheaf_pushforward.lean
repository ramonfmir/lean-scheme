/-
  Continuous maps and sheaves.

  https://stacks.math.columbia.edu/tag/008C
-/

import preliminaries.opens
import sheaves.presheaf

universes u v w

open topological_space

variables {α : Type u} [topological_space α]
variables {β : Type v} [topological_space β]
variables {f : α → β} (Hf : continuous f) 

-- f induced a `map` from G to F.

structure fmap (F : presheaf α) (G : presheaf β) :=
(map      : ∀ (U), G U → F (opens.comap Hf U))
(commutes : ∀ (U V) (HVU : V ⊆ U),
  (map V) ∘ (G.res U V HVU)
= (F.res (opens.comap Hf U) (opens.comap Hf V) (opens.comap_mono Hf V U HVU)) ∘ (map U))

section fmap

variables {γ : Type w} [topological_space γ]
variables {g : β → γ} (Hg : continuous g)

lemma comp {F : presheaf α} {G : presheaf β} {H : presheaf γ} 
(f_ : fmap Hf F G) (g_ : fmap Hg G H) : fmap (continuous.comp Hf Hg) F H :=
{ map := λ U, (f_.map (opens.comap Hg U)) ∘ (g_.map U),
  commutes := 
    begin
      intros U V HVU,
      rw function.comp.assoc _ _ (H.res _ _ _),
      rw g_.commutes,
      rw ←function.comp.assoc _ _ (g_.map _),
      rw f_.commutes,
      refl,
    end, }

end fmap
