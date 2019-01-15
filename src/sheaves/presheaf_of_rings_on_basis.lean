import tag009I tag009J
universe u 

structure presheaf_of_rings_on_basis {X : Type u} [TX : topological_space X] 
  {B : set (set X)} (HB : topological_space.is_topological_basis B) extends presheaf_of_types_on_basis HB :=
(Fring : ∀ {U} (BU : U ∈ B), comm_ring (F BU))
(res_is_ring_morphism : ∀ {U V} (BU : U ∈ B) (BV : V ∈ B) (H : V ⊆ U),
  is_ring_hom (res BU BV H))

attribute [instance] presheaf_of_rings_on_basis.Fring
attribute [instance] presheaf_of_rings_on_basis.res_is_ring_morphism

/-
instance F_is_comm_ring {X : Type u} [TX : topological_space X] 
  {B : set (set X)} (HB : topological_space.is_topological_basis B)
(FPRB : presheaf_of_rings_on_basis HB)
  (U : set X) (BU : U ∈ B) :
 comm_ring ((FPRB.to_presheaf_of_types_on_basis).F BU) := by apply_instance
-/

/-
instance res_is_ring_morphism_instance {X : Type u} [TX : topological_space X] 
  {B : set (set X)} (HB : topological_space.is_topological_basis B)
(FPRB : presheaf_of_rings_on_basis HB)
  (U V : set X) (BU : U ∈ B) (BV : V ∈ B) (HUV : V ⊆ U) :
 is_ring_hom ((FPRB.to_presheaf_of_types_on_basis).res BU BV HUV) := by apply_instance
-/

structure morphism_of_presheaves_of_rings_on_basis {X : Type u} [TX : topological_space X]
{B : set (set X)} {HB : topological_space.is_topological_basis B}
  (FPR GPR : presheaf_of_rings_on_basis HB) :=
(morphism : morphism_of_presheaves_of_types_on_basis FPR.to_presheaf_of_types_on_basis GPR.to_presheaf_of_types_on_basis)
(ring_homs : ∀ {U} (BU : U ∈ B), is_ring_hom (morphism.morphism BU))

definition is_sheaf_of_rings_on_basis {X : Type u} [TX : topological_space X]
{B : set (set X)} {HB : topological_space.is_topological_basis B} (PRB : presheaf_of_rings_on_basis HB) :=
is_sheaf_of_types_on_basis PRB.to_presheaf_of_types_on_basis


/-
structure morphism_of_presheaves_of_rings {α : Type*} [Tα : topological_space α]
  (FPR : presheaf_of_rings α) (GPR : presheaf_of_rings α) :=
(morphism : morphism_of_presheaves_of_types FPR.to_presheaf_of_types GPR.to_presheaf_of_types)
(ring_homs : ∀ U : set α, ∀ HU : is_open U, 
  @is_ring_hom _ _ (FPR.Fring U HU) (GPR.Fring U HU) (morphism.morphism U HU))
-/

--def is_sheaf_of_types {X : Type*} [TX : topological_space X] {B : set (set X)}
--  (HB : topological_space.is_topological_basis B) := 

/-
def is_sheaf_of_rings {α : Type*} [T : topological_space α] 
  (PR : presheaf_of_rings α) : Prop :=
is_sheaf_of_types PR.to_presheaf_of_types


  structure presheaf_of_rings (α : Type*) [T : topological_space α] extends presheaf_of_types α :=
(Fring : ∀ U OU, comm_ring (F U OU))
(res_is_ring_morphism : ∀ (U V : set α) (OU : T.is_open U) (OV : T.is_open V) (H : V ⊆ U),
  is_ring_hom (res U V OU OV H))

  def is_sheaf_of_types {α : Type*} [T : topological_space α]
  (PT : presheaf_of_types α) : Prop :=
∀ (U : set α) [OU : T.is_open U] {γ : Type*} (Ui : γ → set α)
  [UiO : ∀ x : γ, T.is_open (Ui x)] (Hcov : (⋃ (x : γ), (Ui x)) = U),
function.bijective (@gluing _ _ PT U OU _ Ui UiO Hcov)

structure presheaf_of_types_on_basis {X : Type*} [TX : topological_space X] {B : set (set X)}
  (HB : topological_space.is_topological_basis B) := 
(F : Π {U : set X}, U ∈ B → Type*)
(res : ∀ {U V : set X} (BU : U ∈ B) (BV : V ∈ B) (H : V ⊆ U), 
  (F BU) → (F BV))
(Hid : ∀ (U : set X) (BU : U ∈ B), (res BU BU (set.subset.refl U)) = id)  
(Hcomp : ∀ (U V W : set X) (BU : U ∈ B) (BV : V ∈ B) (BW : W ∈ B)
  (HUV : V ⊆ U) (HVW : W ⊆ V),
  (res BU BW (set.subset.trans HVW HUV)) = (res BV BW HVW) ∘ (res BU BV HUV) )


-/