import analysis.topology.topological_space data.set
import analysis.topology.continuity 
import Kenny_comm_alg.Zariski
import tag00EJ
import localization
import localization_UMP
import tag00E0
import tag00DY
import tag006E -- presheaf of types
import tag006N -- presheaf of rings
import tag006T -- sheaves of types
import tag0072 -- sheaves of rings
import Kenny_comm_alg.temp
import mathlib_someday.topology
import tag01HR
import tag007N -- poor mans direct limit

universes u 

local attribute [class] topological_space.is_open 

definition presheaf_of_types_pushforward
  {α : Type u} [Tα : topological_space α]
  {β : Type u} [Tβ : topological_space β]
  (f : α → β)
  (fcont: continuous f)
  (FPT : presheaf_of_types α) :
  presheaf_of_types β :=
{ F := λ V OV, FPT.F (fcont V OV),
  res := λ V₁ V₂ OV₁ OV₂ H, 
    FPT.res (f ⁻¹' V₁) (f⁻¹' V₂) (fcont V₁ OV₁) (fcont V₂ OV₂) (λ x Hx,H Hx),
  Hid := λ V OV, FPT.Hid (f ⁻¹' V) (fcont V OV),
  Hcomp := λ Uβ Vβ Wβ OUβ OVβ OWβ HUV HVW,
    FPT.Hcomp (f ⁻¹' Uβ)(f ⁻¹' Vβ)(f ⁻¹' Wβ) (fcont Uβ OUβ) (fcont Vβ OVβ) (fcont Wβ OWβ)
    (λ x Hx, HUV Hx) (λ x Hx, HVW Hx) }

definition presheaf_of_rings_pushforward
  {α : Type u} [Tα : topological_space α]
  {β : Type u} [Tβ : topological_space β]
  (f : α → β)
  (fcont: continuous f)
  (FPR : presheaf_of_rings α) :
  presheaf_of_rings β :=
{ Fring := λ U OU,FPR.Fring (fcont U OU),
  res_is_ring_morphism := λ U V OU OV H,
    FPR.res_is_ring_morphism (f ⁻¹' U) (f ⁻¹' V) (fcont U OU) (fcont V OV) (λ x Hx, H Hx),
  .. presheaf_of_types_pushforward f fcont FPR.to_presheaf_of_types }

definition presheaf_of_types_pullback_under_open_immersion
  {α : Type u} [Tα : topological_space α]
  {β : Type u} [Tβ : topological_space β]
  (PT : presheaf_of_types β)
  (f : α → β)
  (H : topological_space.open_immersion f) :
  presheaf_of_types α :=
{ F := λ U HU,PT.F ((H.fopens U).1 HU),
  res := λ U V OU OV H2,PT.res (f '' U) (f '' V) ((H.fopens U).1 OU) ((H.fopens V).1 OV)
    (set.image_subset f H2),
  Hid := λ _ _,PT.Hid _ _,
  Hcomp := λ U V W _ _ _ HUV HVW, 
    PT.Hcomp _ _ _ _ _ _ (set.image_subset f HUV) (set.image_subset f HVW) } 

definition presheaf_of_rings_pullback_under_open_immersion
  {α : Type u} [Tα : topological_space α]
  {β : Type u} [Tβ : topological_space β]
  (PR : presheaf_of_rings β)
  (f : α → β)
  (H : topological_space.open_immersion f) :
  presheaf_of_rings α := 
{ Fring := λ U OU,PR.Fring (topological_space.open_of_open_immersion_open f H U OU),
  res_is_ring_morphism := λ U V OU OV H2,PR.res_is_ring_morphism (f '' U) (f '' V)
    (topological_space.open_of_open_immersion_open f H U OU)
    (topological_space.open_of_open_immersion_open f H V OV) 
    (set.image_subset f H2),
  .. presheaf_of_types_pullback_under_open_immersion PR.to_presheaf_of_types f H }


lemma zariski.univ_is_basic (R : Type u) [comm_ring R] : is_zariski.standard_open (@set.univ (X R)) :=
⟨(1 : R),eq.symm $ set.univ_subset_iff.1 $ λ ⟨P,HP⟩ _,@@is_prime_ideal.one_not_mem _ P HP⟩

instance zariski.structure_presheaf_of_rings_on_basis_stalk_is_ring (R : Type u) [comm_ring R] (x : X R) :
comm_ring (presheaf_on_basis_stalk
  (zariski.structure_presheaf_of_rings_on_basis_of_standard R).to_presheaf_of_types_on_basis x) :=
presheaf_of_rings_on_basis_stalk.stalks_of_presheaf_of_rings_on_basis_are_rings
  (zariski.structure_presheaf_of_rings_on_basis_of_standard R) x
  (zariski.standard_basis_has_FIP R)
  (zariski.univ_is_basic R)

instance zariski.structure_presheaf_of_types_on_basis_stalk_is_ring (R : Type u) [comm_ring R] (x : X R) : 
comm_ring (presheaf_on_basis_stalk (zariski.structure_presheaf_of_types_on_basis_of_standard R) x)
:= 
presheaf_of_rings_on_basis_stalk.stalks_of_presheaf_of_rings_on_basis_are_rings
  (zariski.structure_presheaf_of_rings_on_basis_of_standard R) x
  (zariski.standard_basis_has_FIP R)
  (zariski.univ_is_basic R)

instance zariski.structure_sheaf_of_types_sections_has_add
(R : Type u) [comm_ring R] (U : set (X R)) (OU : is_open U) : 
has_add ((zariski.structure_presheaf_of_types R).F OU) := 
⟨λ s t,⟨λ x HUx,s.1 x HUx + t.1 x HUx,begin
  intros x HUx,
  cases s.2 x HUx with Us Hs, -- kenny says use rcases
  cases Hs with BUs Hs, -- rcases s.2 x HUx with \<Us, BUs, HxUs, sigmas\>
  cases Hs with HxUs Hs,
  cases Hs with sigmas Hs,
  cases t.2 x HUx with Ut Ht,
  cases Ht with BUt Ht,
  cases Ht with HxUt Ht,
  cases Ht with sigmat Ht,
  let Ust := Us ∩ Ut,
  existsi Ust,
  let BUst := zariski.standard_basis_has_FIP R _ _ BUs BUt,
  existsi BUst,
  existsi (⟨HxUs,HxUt⟩ : x ∈ Us ∩ Ut),
  let sigma := 
  ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res 
      BUs BUst (set.inter_subset_left Us Ut) sigmas) +
  ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res 
      BUt BUst (set.inter_subset_right Us Ut) sigmat),
  existsi sigma,
  intros y Hy,
  funext HyU,
  have Hsy := Hs y ⟨HyU,Hy.2.1⟩,
  have Hty := Ht y ⟨HyU,Hy.2.2⟩,
  rw [Hsy,Hty],
  apply quotient.sound,
  existsi Ust,
  existsi Hy.2,
  existsi BUst,
  existsi (set.subset.refl _: Ust ⊆ Us ∩ Ut),
  existsi (set.subset.refl _: Ust ⊆ Ust),
  dsimp,
  rw (presheaf_of_rings_on_basis.res_is_ring_morphism
    (zariski.structure_presheaf_of_rings_on_basis_of_standard R)
    _ _ _).map_add,
  rw ←(presheaf_of_rings_on_basis.to_presheaf_of_types_on_basis 
        (zariski.structure_presheaf_of_rings_on_basis_of_standard R)).Hcomp',
  rw ←(presheaf_of_rings_on_basis.to_presheaf_of_types_on_basis 
        (zariski.structure_presheaf_of_rings_on_basis_of_standard R)).Hcomp',
  rw (presheaf_of_rings_on_basis.res_is_ring_morphism
       (zariski.structure_presheaf_of_rings_on_basis_of_standard R)
        _ _ _).map_add,
  show _ = (zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUst BUst _
        ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUs BUst _ sigmas) +
           (zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUst BUst _
        ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUt BUst _ sigmat),
  rw ←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp',
  rw ←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp',
  refl,
end
⟩⟩

instance zariski.structure_sheaf_of_types_sections_has_zero
(R : Type u) [comm_ring R] (U : set (X R)) (OU : is_open U) : 
has_zero ((zariski.structure_presheaf_of_types R).F OU) := ⟨⟨λ x Hx,0,
begin
  intros x Hx,
  existsi (set.univ),
  existsi zariski.univ_is_basic R,
  existsi trivial,
  existsi (0 : (zariski.structure_presheaf_of_types_on_basis_of_standard R).F _),
    tactic.swap,apply_instance, -- shrug
  intros y Hy,
  funext,
  apply quotient.sound,
  refl,
end⟩⟩


instance zariski.structure_sheaf_of_types_sections_has_neg
(R : Type u) [comm_ring R] (U : set (X R)) (OU : is_open U) : 
has_neg ((zariski.structure_presheaf_of_types R).F OU) := 
⟨λ s,⟨λ x HUx,-(s.1 x HUx),begin
  intros x HUx,
  rcases (s.2 x HUx) with ⟨Us,BUs,HxUs,sigmas,Hs⟩,
  existsi Us,existsi BUs,existsi HxUs,existsi -sigmas,
  intros y Hy,
  funext,
  rw (Hs y Hy),
  apply quotient.sound,
  refl,
end
⟩⟩

instance zariski.structure_sheaf_of_types_sections_has_mul
(R : Type u) [comm_ring R] (U : set (X R)) (OU : is_open U) : 
has_mul ((zariski.structure_presheaf_of_types R).F OU) := 
⟨λ s t,⟨λ x HUx,s.1 x HUx * t.1 x HUx,begin
  intros x HUx,
  rcases (s.2 x HUx) with ⟨Us,BUs,HxUs,sigmas,Hs⟩,
  rcases (t.2 x HUx) with ⟨Ut,BUt,HxUt,sigmat,Ht⟩,
  let Ust := Us ∩ Ut,
  existsi Ust,
  let BUst := zariski.standard_basis_has_FIP R _ _ BUs BUt,
  existsi BUst,
  existsi (⟨HxUs,HxUt⟩ : x ∈ Us ∩ Ut),
  let sigma := 
  ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res 
      BUs BUst (set.inter_subset_left Us Ut) sigmas) *
  ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res 
      BUt BUst (set.inter_subset_right Us Ut) sigmat),
  existsi sigma,
  intros y Hy,
  funext HyU,
  have Hsy := Hs y ⟨HyU,Hy.2.1⟩,
  have Hty := Ht y ⟨HyU,Hy.2.2⟩,
  rw [Hsy,Hty],
  apply quotient.sound,
  existsi Ust,
  existsi Hy.2,
  existsi BUst,
  existsi (set.subset.refl _: Ust ⊆ Us ∩ Ut),
  existsi (set.subset.refl _: Ust ⊆ Ust),
  dsimp,
  rw (presheaf_of_rings_on_basis.res_is_ring_morphism
    (zariski.structure_presheaf_of_rings_on_basis_of_standard R)
    _ _ _).map_mul,
  rw ←(presheaf_of_rings_on_basis.to_presheaf_of_types_on_basis 
        (zariski.structure_presheaf_of_rings_on_basis_of_standard R)).Hcomp',
  rw ←(presheaf_of_rings_on_basis.to_presheaf_of_types_on_basis 
        (zariski.structure_presheaf_of_rings_on_basis_of_standard R)).Hcomp',
  rw (presheaf_of_rings_on_basis.res_is_ring_morphism
       (zariski.structure_presheaf_of_rings_on_basis_of_standard R)
        _ _ _).map_mul,
  show _ = (zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUst BUst _
        ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUs BUst _ sigmas) *
           (zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUst BUst _
        ((zariski.structure_presheaf_of_types_on_basis_of_standard R).res BUt BUst _ sigmat),
  rw ←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp',
  rw ←(zariski.structure_presheaf_of_types_on_basis_of_standard R).Hcomp',
  refl,
end
⟩⟩

instance zariski.structure_sheaf_of_types_sections_has_one
(R : Type u) [comm_ring R] (U : set (X R)) (OU : is_open U) : 
has_one ((zariski.structure_presheaf_of_types R).F OU) := ⟨⟨λ x Hx,1,
begin
  intros x Hx,
  existsi (set.univ),
  existsi zariski.univ_is_basic R,
  existsi trivial,
  existsi (1 : (zariski.structure_presheaf_of_types_on_basis_of_standard R).F _),
    tactic.swap,apply_instance, -- shrug
  intros y Hy,
  funext,
  apply quotient.sound,
  refl,
end⟩⟩

instance zariski.structure_sheaf_of_types_sections_are_rings (R : Type u) [comm_ring R]
(U : set (X R)) (OU : is_open U) : 
comm_ring ((zariski.structure_presheaf_of_types R).F OU) :=
by refine
{ add := has_add.add,
  add_assoc := λ _ _ _, subtype.eq $ by funext;exact add_assoc _ _ _,
  zero := has_zero.zero _,
  zero_add := λ _, subtype.eq $ by funext;exact zero_add _,
  add_zero := λ _, subtype.eq $ by funext;exact add_zero _,
  neg := has_neg.neg,
  add_left_neg := λ _, subtype.eq $ by funext;exact add_left_neg _,
  add_comm := λ _ _, subtype.eq $ by funext;exact add_comm _ _,
  mul := has_mul.mul,
  mul_assoc := λ _ _ _,subtype.eq $ by funext;exact mul_assoc _ _ _,
  one := has_one.one _,
  one_mul := λ _, subtype.eq $ by funext;exact one_mul _,
  mul_one := λ _, subtype.eq $ by funext;exact mul_one _,
  left_distrib := λ _ _ _,subtype.eq $ by funext;exact left_distrib _ _ _,
  right_distrib := λ _ _ _,subtype.eq $ by funext;exact right_distrib _ _ _,
  mul_comm := λ _ _,subtype.eq $ by funext;exact mul_comm _ _ }

definition zariski.structure_presheaf_of_rings (R : Type u) [comm_ring R] : 
presheaf_of_rings (X R) := begin refine {
res_is_ring_morphism := _,
..zariski.structure_presheaf_of_types R},
  intros U V OU OV HVU,
  constructor;intros;apply subtype.eq;funext;refl
end 

theorem zariski.structure_presheaf_is_sheaf_of_rings (R : Type u) [comm_ring R] :
is_sheaf_of_rings (zariski.structure_presheaf_of_rings R) := 
zariski.structure_sheaf_is_sheaf_of_types R 

structure scheme :=
(α : Type u)
(T : topological_space α)
(O_X : presheaf_of_rings α)
(O_X_sheaf : is_sheaf_of_rings O_X)
(locally_affine : ∃ β : Type u,
  ∃ cov : β → set α,
  ∃ cov_open : ∀ b, T.is_open $ cov b, 
  (∀ x, ∃ b, x ∈ cov b) ∧
  ∀ b : β, ∃ R : Type u, ∃ RR : comm_ring R, ∃ fR : (X R) → α, 
    set.range fR = cov b ∧ -- thanks Johan Commelin!!
    ∃ H : topological_space.open_immersion fR, 
    are_isomorphic_presheaves_of_rings 
      (presheaf_of_rings_pullback_under_open_immersion O_X fR H)
      (zariski.structure_presheaf_of_rings R)
)

definition scheme_of_affine_scheme (R : Type u) [comm_ring R] : scheme :=
{ α := X R,
  T := by apply_instance,
  O_X := zariski.structure_presheaf_of_rings R,
  O_X_sheaf := zariski.structure_presheaf_is_sheaf_of_rings R,
  locally_affine := begin
    existsi (punit : Type u),
    existsi (λ _, set.univ),
    existsi (λ _, is_open_univ),
    split,
    { intro x,
      existsi punit.star,
      trivial },
    intro _,
    existsi R,
    existsi _,tactic.swap,apply_instance,
    existsi id,
    split,
    { apply set.eq_univ_of_forall,
      intro x, existsi x, refl },
    existsi topological_space.open_immersion_id _,
    constructor,tactic.swap,
    { constructor,tactic.swap,
      { constructor,tactic.swap,
          { intros U HU, -- should I use res again??
            refine (zariski.structure_presheaf_of_rings R).res _ _ _ _ _,
              rwa set.image_id,
              rwa set.image_id,
          },
          intros U V HU HV Hsub,
          refl,
        },
        intros,constructor,
        {refl,
        },
        { intros x y,refl,
        },
        { intros x y,refl
        },
      },
    { existsi _,tactic.swap,
      { constructor,tactic.swap,
        { constructor,tactic.swap,
          { intros U HU, -- should I use res again??
            refine (zariski.structure_presheaf_of_rings R).res _ _ _ _ _,
              rwa set.image_id,
              rwa set.image_id,
          },
          intros U V HU HV Hsub,
          refl,
        },
        intros,constructor,
        {refl,
        },
        { intros x y,refl,
        },
        { intros x y,refl
        }
      },
    constructor,
    {
      unfold is_identity_morphism_of_presheaves_of_types,
      intros,
      funext,
      unfold composition_of_morphisms_of_presheaves_of_types,
      dsimp,
      show (zariski.structure_presheaf_of_types R).res U (id '' U) OU _ _
      ((zariski.structure_presheaf_of_types R).res (id '' U) U _ OU _ x) =
    x,
      rw ←presheaf_of_types.Hcomp',
      simp,
    },
    { unfold is_identity_morphism_of_presheaves_of_types,
      intros,
      funext,
      unfold composition_of_morphisms_of_presheaves_of_types,
      dsimp,
      show (zariski.structure_presheaf_of_types R).res (id '' U) U _ OU _
      ((zariski.structure_presheaf_of_types R).res U (id '' U) OU _ _ x) =
    x,
      rw ←presheaf_of_types.Hcomp',
      simp,
    },
  }
  end 
}
