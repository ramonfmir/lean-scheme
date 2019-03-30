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

lemma pushforward.morphism (F G : presheaf_of_rings α) (φ : F ⟶ G) 
: pushforward Hf F ⟶ pushforward Hf G :=
{ ring_homs := 
    begin
      intros U,
      dunfold presheaf.pushforward.morphism,
      exact φ.ring_homs (opens.comap Hf U),
    end,
  ..presheaf.pushforward.morphism Hf F.to_presheaf G.to_presheaf φ.to_morphism }

end pushforward

-- f induces a functor PSh(β) ⟶ PSh(α). Simplified to the case when f is 'nice'.

-- section pullback

-- variable (Hf' : ∀ U, is_open (f '' U))

-- def pullback (F : presheaf β) : presheaf α :=
-- { F := λ U, F (opens.map Hf' U),
--   res := λ U V HVU, F.res (opens.map Hf' U) (opens.map Hf' V) (opens.map_mono Hf' V U HVU),
--   Hid := λ U, F.Hid (opens.map Hf' U),
--   Hcomp := λ U V W HWV HVU, 
--     F.Hcomp (opens.map Hf' U) (opens.map Hf' V) (opens.map Hf' W) 
--             (opens.map_mono Hf' W V HWV) (opens.map_mono Hf' V U HVU), }

-- lemma pullback.morphism (F G : presheaf β) (φ : F ⟶ G) : pullback Hf' F ⟶ pullback Hf' G :=
-- { map := λ U, φ.map (opens.map Hf' U), 
--   commutes := λ U V HVU, 
--     φ.commutes (opens.map Hf' U) (opens.map Hf' V) (opens.map_mono Hf' V U HVU), }

-- end pullback

-- -- f induces a `map` from a presheaf on β to a presheaf on α.

-- section fmap

-- structure fmap (F : presheaf α) (G : presheaf β) :=
-- (map      : ∀ (U), G U → F (opens.comap Hf U))
-- (commutes : ∀ (U V) (HVU : V ⊆ U),
--   (map V) ∘ (G.res U V HVU)
-- = (F.res (opens.comap Hf U) (opens.comap Hf V) (opens.comap_mono Hf V U HVU)) ∘ (map U))

-- variables {γ : Type w} [topological_space γ]
-- variables {g : β → γ} {Hg : continuous g}

-- variable {Hf}

-- lemma comp {F : presheaf α} {G : presheaf β} {H : presheaf γ} 
-- (f_ : fmap Hf F G) (g_ : fmap Hg G H) : fmap (continuous.comp Hf Hg) F H :=
-- { map := λ U, (f_.map (opens.comap Hg U)) ∘ (g_.map U),
--   commutes := 
--     begin
--       intros U V HVU,
--       rw function.comp.assoc _ _ (H.res _ _ _),
--       rw g_.commutes,
--       rw ←function.comp.assoc _ _ (g_.map _),
--       rw f_.commutes,
--       refl,
--     end, }

-- end fmap

end presheaf_of_rings
