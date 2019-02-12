import data.set data.equiv.basic
import algebra.group ring_theory.algebra

import preliminaries.localisation

-- Define localisation on a set of generators.

section localisation_on_generators 

universes u v w

parameters {A : Type u} {B : Type v} {C : Type w} 
parameters [comm_ring A] [comm_ring B] [comm_ring C]
parameters (G : set A) (f : A → B) [is_ring_hom f]

def S : set A := monoid.closure G
instance S_submonoid : is_submonoid S := monoid.closure.is_submonoid G

def is_localization' := localization_alt.is_localization S f

end localisation_on_generators

/-
 Trying to fix issues in:
 https://github.com/kbuzzard/lean-stacks-project/blob/595aa1d6c5ce5a6fa0259c5a0a2226a91b07d96e/src/canonical_isomorphism_nonsense.lean#L268

 We want to prove the sheaf condition on the presheaf defined on the standard 
 opens D(fi) as in https://stacks.math.columbia.edu/tag/01HR.

 In the proof, they use Lemma 10.23.1/2 https://stacks.math.columbia.edu/tag/00EI
 which is when the "canonical isomorphism nonsense" was used.

 We should start testing this new API with the lemmas on localisation_UMP.
-/