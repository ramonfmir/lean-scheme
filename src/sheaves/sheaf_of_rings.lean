import tag006T -- sheaves of types
import tag006N -- presheaves of rings

-- this should really be done for abstract categories; we "cheat" here because
-- equalizers in the category of commutative rings are the same as equalizers
-- in the underlying category of sets: see tag0073 (lemma 6.9.2)

def is_sheaf_of_rings {α : Type*} [T : topological_space α] 
  (PR : presheaf_of_rings α) : Prop :=
is_sheaf_of_types PR.to_presheaf_of_types

