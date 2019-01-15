/-
if R is a ring, I and ideal of R and S a multiplicative subset of R, then S−1I is an ideal of S−1R, and we have S−1R/S−1I=S⎯⎯⎯−1(R/I), where S⎯⎯⎯ is the image of S in R/I, 

[proof omitted]
-/

import Kenny_comm_alg.temp linear_algebra.quotient_module 
import linear_algebra.linear_map_module
import group_theory.submonoid
universe u

def localize {α : Type u} [comm_ring α] (S : set α) [is_submonoid S]
  (I : set α) [is_submodule I] :
  set (localization.loc α S) :=
{y | ∃ (x s : α) (hx : x ∈ I) (hs : s ∈ S), ⟦(⟨x, s, hs⟩:α × S)⟧ = y}

abbreviation localize' {α : Type u} [comm_ring α] (I : set α) [is_submodule I]
  (S : set α) [is_submonoid S] :
  set (localization.loc α S) :=
localize S I

variables {α : Type u} [comm_ring α] (S : set α) [is_submonoid S]

variables (I : set α) [is_submodule I]


postfix ⁻¹ := localize
infix ` /ᵣ `:100 := localization.loc
infix ` /ᵣ `:100 := localize'
notation α` [1/`:max S `]` := localization.loc α S
notation I` [1/`:max S `]` := localize S I
notation S `ₑ`:max := quotient.mk '' S

instance localization.is_submodule.of_comm_ring : is_submodule (S⁻¹ I) :=
{ zero_ := ⟨(0:α), (1:α), @is_submodule.zero _ _ _ _ I _, is_submonoid.one_mem S, quotient.sound $ setoid.refl _⟩,
  add_  := λ m₁ m₂ ⟨x₁, s₁, hx₁, hs₁, h₁⟩ ⟨x₂, s₂, hx₂, hs₂, h₂⟩,
    ⟨s₁ * x₂ + s₂ * x₁, s₁ * s₂, is_submodule.add (is_submodule.smul _ hx₂) (is_submodule.smul _ hx₁),
     is_submonoid.mul_mem hs₁ hs₂, by rw [← h₁, ← h₂]; refl⟩,
  smul  := λ c m ⟨x, s, hx, hs, h⟩, quotient.induction_on c $ λ ⟨cr, cs, ch⟩,
    ⟨cr * x, cs * s, is_submodule.smul _ hx, is_submonoid.mul_mem ch hs, by rw [← h]; refl⟩ }

instance localization.is_submonoid.of_comm_ring : is_submonoid (quotient.mk '' S : set (α /ᵣ I)) :=
{ one_mem := ⟨1, is_submonoid.one_mem S, rfl⟩,
  mul_mem := λ x y, quotient.induction_on₂ x y $ λ m n ⟨mw, hms, hm⟩ ⟨nw, hns, hn⟩,
    ⟨mw * nw, is_submonoid.mul_mem hms hns, by rw [← hm, ← hn]; refl⟩ }

private def to_be_named_aux1 : α × S → (α /ᵣ I) [1/(S ₑ)] :=
λ x, ⟦⟨⟦x.1⟧, ⟦x.2.1⟧, x.2.1, x.2.2, rfl⟩⟧

private def to_be_named_aux2 : α [1/S] → (α /ᵣ I) [1/(S ₑ)] :=
quotient.lift (to_be_named_aux1 S I) $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨w, hws, hw⟩,
quotient.sound $ ⟨⟦w⟧, ⟨w, hws, rfl⟩, quotient.sound $ begin simp at hw ⊢,rw hw,end⟩

--set_option pp.notation false
private def to_be_named_aux3 : α [1/S] /ᵣ (S⁻¹ I) → (α /ᵣ I) [1/(S ₑ)] :=
quotient.lift (to_be_named_aux2 S I) $ λ x y, quotient.induction_on₂ x y $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨v, w, hv, hw, h⟩, quotient.sound $
let ⟨t, hts, hsv⟩ := quotient.exact h in
⟨⟦w * t⟧, ⟨w * t, is_submonoid.mul_mem hw hts, rfl⟩,
 quotient.sound $ suffices (s₁ * r₂ - s₂ * r₁) * (w * t) ∈ I,
 begin simp at this ⊢, 
   show (s₁ * r₂ + -(s₂ * r₁)) * (w * t) - 0 ∈ I,
   simp [this],
  end,
 have (-(s₁ * s₂ * v) + w * (s₂ * r₁ + -(s₁ * r₂))) * t = 0,
 by simpa using hsv, calc
         (s₁ * r₂ - s₂ * r₁) * (w * t)
       = (-(s₁ * s₂ * v) + w * (s₂ * r₁ + -(s₁ * r₂))) * t + (s₁ * r₂ - s₂ * r₁) * (w * t) : by simp [this]
   ... = (-s₁ * s₂ * t) * v : by ring
   ... ∈ I : is_submodule.smul _ hv⟩

private lemma to_be_named_aux35 : (1:α [1/S])
  = ⟦⟨1, 1, is_submonoid.one_mem S⟩⟧ := rfl

private def to_be_named_aux4 : is_ring_hom (to_be_named_aux3 S I) :=
{ map_add := λ x y, quotient.induction_on₂ x y $
    λ m n, quotient.induction_on₂ m n $
    λ ⟨p, q, r⟩ ⟨s, t, u⟩, by simp [is_ideal.coset_eq, to_be_named_aux3,
      to_be_named_aux2, to_be_named_aux1, localization.mk_eq],
  map_mul := λ x y, quotient.induction_on₂ x y $
    λ m n, quotient.induction_on₂ m n $
    λ ⟨p, q, r⟩ ⟨s, t, u⟩, by simp [is_ideal.coset_eq, to_be_named_aux3,
      to_be_named_aux2, to_be_named_aux1, localization.mk_eq],
  map_one := by simp [is_ideal.coset_eq, to_be_named_aux3,
      to_be_named_aux2, to_be_named_aux1, localization.mk_eq];
      rw to_be_named_aux35; rw quotient.lift_beta; simp }

local attribute [instance] to_be_named_aux4
local attribute [instance] is_ring_hom.ker.is_ideal
instance deus : comm_ring (α [1/S] /ᵣ (S⁻¹ I)) := by apply_instance
instance salva : module (α [1/S] /ᵣ (S⁻¹ I)) (α [1/S] /ᵣ (S⁻¹ I)) := ring.to_module
instance me : is_submodule (is_ring_hom.ker (to_be_named_aux3 S I)) := is_ring_hom.ker.is_submodule (to_be_named_aux3 S I)

private def to_be_named_aux5 :
  α [1/S] /ᵣ (S⁻¹ I) ≃ᵣ
    α [1/S] /ᵣ (S⁻¹ I) /ᵣ is_ring_hom.ker (to_be_named_aux3 S I) :=
{ to_fun := quotient.mk,
  is_ring_hom := is_ideal.to_quotient _ _,
  inv_fun := quotient.lift (@id (α [1/S] /ᵣ (S⁻¹ I))) $
    λ x y, quotient.induction_on₂ x y $
    λ m n, quotient.induction_on₂ m n $
    λ ⟨b, c, d⟩ ⟨e, f, g⟩ h,
    begin
      change _ - _ ∈ _ at h,
      simp [is_ideal.coset_eq, to_be_named_aux3,
      to_be_named_aux2, to_be_named_aux1, localization.mk_eq] at h,
      replace h := quotient.exact h,
      rcases h with ⟨r, s, h⟩,
      rcases s with ⟨p, q, hp⟩,
      rw ← hp at h,
      replace h := quotient.exact h,
      change _ - _ ∈ _ at h,
      apply quotient.sound,
      existsi p * (f * b - c * e),
      existsi p * (c * f),
      have hx : p * (f * b - c * e) ∈ I,
        { have aux : p * (f * b - c * e) = -((c * f * 0 + -(1 * (f * b + -(c * e)))) * p - 0),
          { ring },
          rw aux,
          exact is_submodule.neg h },
      existsi hx,
      existsi is_submonoid.mul_mem q (is_submonoid.mul_mem d g),
      apply quotient.sound,
      existsi (1:α),
      existsi is_submonoid.one_mem S,
      simp,
      ring
    end,
  left_inv := λ x, rfl,
  right_inv := λ x, quotient.induction_on x $ λ m, rfl }

private def to_be_named_aux6 :
  ↥(is_ring_hom.im (to_be_named_aux3 S I)) ≃ᵣ
    (α /ᵣ I) [1/(S ₑ)] :=
{ to_fun := subtype.val,
  is_ring_hom := subring.is_ring_hom _ _,
  inv_fun := λ x, ⟨x, quotient.induction_on x $
    λ ⟨m, n, p, hp, hpn⟩, quotient.induction_on m $
    begin
      intro q,
      existsi @is_ideal.mk' _ (localization.comm_ring _ _) _ _ ⟦(⟨q, p, hp⟩ : α × S)⟧,
      simp [to_be_named_aux3,
        to_be_named_aux2, to_be_named_aux1, localization.mk_eq],
      apply quotient.sound,
      existsi ⟦(1:α)⟧,
      split,
      { existsi (1:α),
        existsi is_submonoid.one_mem S,
        refl },
      simp [hpn]
    end⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, rfl }

noncomputable def to_be_named : α [1/S] /ᵣ (S⁻¹ I) ≃ᵣ (α /ᵣ I) [1/(S ₑ)] :=
(to_be_named_aux5 S I).trans $
(first_isom _ _ $ to_be_named_aux3 S I).trans $
to_be_named_aux6 S I
