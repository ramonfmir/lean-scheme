import preliminaries.covering
import sheaves.presheaf_of_types

universes u v

open topological_space
open lattice

section sheaf_condition

variables {α : Type u} [topological_space α]

-- Restriction map from U to U ∩ V.

def res_to_inter_left (F : presheaf_of_types α) (U V : opens α) 
: (F U) → (F (U ∩ V)) :=
F.res U (U ∩ V) (set.inter_subset_left U V)

-- Restriction map from V to U ∩ V.

def res_to_inter_right (F : presheaf_of_types α) (U V : opens α) 
: (F V) → (F (U ∩ V)) :=
F.res V (U ∩ V) (set.inter_subset_right U V)

-- Sheaf condition.

def locality (F : presheaf_of_types α) :=
∀ {U} (OC : covering U) (s t : F U), 
(∀ i, F.res U (OC.Uis i) (subset_covering i) s = 
      F.res U (OC.Uis i) (subset_covering i) t) → 
s = t

def gluing (F : presheaf_of_types α) :=
∀ {U} (OC : covering U),
∀ (s : Π i, F (OC.Uis i)),
(∀ j k, res_to_inter_left F (OC.Uis j) (OC.Uis k) (s j) = 
        res_to_inter_right F (OC.Uis j) (OC.Uis k) (s k)) → 
∃ S, ∀ i, F.res U (OC.Uis i) (subset_covering i) S = s i

end sheaf_condition

-- Definition of a sheaf of types.

structure sheaf_of_types (α : Type u) [T : topological_space α] :=
(F        : presheaf_of_types α)
(locality : locality F)
(gluing   : gluing F) 

section sheaf_of_types

variables {α : Type u} [T : topological_space α]
include T

instance : has_coe (sheaf_of_types α) (presheaf_of_types α) := 
⟨λ S, S.F⟩

def is_sheaf_of_types (F : presheaf_of_types α) :=
locality F ∧ gluing F

end sheaf_of_types
