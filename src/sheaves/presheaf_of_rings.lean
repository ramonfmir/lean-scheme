import tag006E -- presheaf of sets
universe u
-- I only need rings at the minute.

structure presheaf_of_rings (α : Type u) [T : topological_space α] extends presheaf_of_types α :=
[Fring : ∀ {U} (OU : T.is_open U), comm_ring (F OU)]
(res_is_ring_morphism : ∀ (U V : set α) (OU : T.is_open U) (OV : T.is_open V) (H : V ⊆ U),
  is_ring_hom (res U V OU OV H))

attribute [instance] presheaf_of_rings.Fring

structure morphism_of_presheaves_of_rings {α : Type u} [Tα : topological_space α]
  (FPR : presheaf_of_rings α) (GPR : presheaf_of_rings α) :=
(morphism : morphism_of_presheaves_of_types FPR.to_presheaf_of_types GPR.to_presheaf_of_types)
(ring_homs : ∀ U : set α, ∀ HU : is_open U, 
  @is_ring_hom _ _ _ _ (morphism.morphism U HU))

def are_isomorphic_presheaves_of_rings {α : Type u} [Tα : topological_space α]
  (FPR : presheaf_of_rings α) (GPR : presheaf_of_rings α) : Prop := 
∃ (fg : morphism_of_presheaves_of_rings FPR GPR) (gf : morphism_of_presheaves_of_rings GPR FPR),
  is_identity_morphism_of_presheaves_of_types (composition_of_morphisms_of_presheaves_of_types fg.morphism gf.morphism)
  ∧ is_identity_morphism_of_presheaves_of_types( composition_of_morphisms_of_presheaves_of_types gf.morphism fg.morphism)
