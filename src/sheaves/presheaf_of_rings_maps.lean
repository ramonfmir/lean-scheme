/-
  Continuous maps and presheaves of rings.

  https://stacks.math.columbia.edu/tag/008C
-/

import preliminaries.opens
import sheaves.presheaf_of_rings
import sheaves.presheaf_maps

universes u v w

open topological_space

variables {α : Type u} [topological_space α]
variables {β : Type v} [topological_space β]
variables {f : α → β} (Hf : continuous f) 

namespace presheaf_of_rings

-- f induces a functor PSh(α) ⟶ PSh(β).

section pushforward

def pushforward (F : presheaf_of_rings α) : presheaf_of_rings β :=
{ Fring := λ U, F.Fring _,
  res_is_ring_hom := λ U V HVU, F.res_is_ring_hom _ _ _,
  ..presheaf.pushforward Hf F.to_presheaf }

def pushforward.morphism (F G : presheaf_of_rings α) (φ : F ⟶ G) 
: pushforward Hf F ⟶ pushforward Hf G :=
{ ring_homs := λ U, φ.ring_homs _,
  ..presheaf.pushforward.morphism Hf F.to_presheaf G.to_presheaf φ.to_morphism }

end pushforward

-- f induces a functor PSh(β) ⟶ PSh(α). Simplified to the case when f is 'nice'.

section pullback

-- variable (Hf' : ∀ U, is_open (f '' U))

-- def pullback (F : presheaf_of_rings β) : presheaf_of_rings α :=
-- { Fring := λ U, F.Fring _,
--   res_is_ring_hom := λ U V HVU, F.res_is_ring_hom _ _ _,
--   ..presheaf.pullback Hf' F.to_presheaf }

-- lemma pullback.morphism (F G : presheaf_of_rings β) (φ : F ⟶ G) : pullback Hf' F ⟶ pullback Hf' G :=
-- { ring_homs := λ U, φ.ring_homs _,
--   ..presheaf.pullback.morphism Hf' F.to_presheaf G.to_presheaf φ.to_morphism }

structure pullback (F : presheaf_of_rings β) :=
(φ : α → β) 
[Hcts : continuous φ]
(Hφ : ∀ U, is_open (φ '' U))
(range : opens β :=
  ⟨φ '' set.univ, Hφ set.univ⟩)
(carrier : presheaf_of_rings α :=
  { Fring := λ U, F.Fring _,
    res_is_ring_hom := λ U V HVU, F.res_is_ring_hom _ _ _,
    ..presheaf.pullback Hφ F.to_presheaf })

end pullback

-- f induces a `map` from a presheaf of rings on β to a presheaf of rings on α.

def fmap (F : presheaf_of_rings α) (G : presheaf_of_rings β) :=
presheaf.fmap Hf F.to_presheaf G.to_presheaf

namespace fmap

variables {γ : Type w} [topological_space γ]
variables {g : β → γ} {Hg : continuous g}

variable {Hf}

def comp {F : presheaf_of_rings α} {G : presheaf_of_rings β} {H : presheaf_of_rings γ} 
(f_ : fmap Hf F G) (g_ : fmap Hg G H) : fmap (continuous.comp Hf Hg) F H :=
presheaf.fmap.comp f_ g_

end fmap

end presheaf_of_rings
