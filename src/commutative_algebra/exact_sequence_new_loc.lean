/-
  (fᵢ) = R ⇒ 0 → R → Π Rfᵢ → Π Rfᵢfⱼ is exact. 

  https://stacks.math.columbia.edu/tag/00EJ
-/

import data.set.finite
import data.fintype
import tactic.ring
import preliminaries.localisation

universes u

variables {R : Type u} [comm_ring R] 
variables {γ : Type u} [fintype γ] {fi : γ → R}

open localization_alt

def is_localisation_at 
(a : R) {Ra : Type u} [comm_ring Ra] (φ : R → Ra) [is_ring_hom φ] := 
is_localization (powers a) φ

variables (Hgen : (1 : R) ∈ ideal.span (set.range fi))

variables (Ri : γ → Type u) [∀ i, comm_ring (Ri i)]
variables (φi : Π i, R → (Ri i)) [∀ i, is_ring_hom (φi i)] 
variables (Hloci : ∀ i, is_localisation_at (fi i) (φi i))

variables {Rij : γ → γ → Type u} [∀ i j, comm_ring (Rij i j)]
variables (φij : Π i j, R → (Rij i j)) [∀ i j, is_ring_hom (φij i j)] 
variables (Hlocij : ∀ i j, is_localisation_at ((fi i)*(fi j)) (φij i j))

include Hloci Hlocij

def α : R → Π i, (Ri i) := λ x i, (φi i) x

def β1 : Π i, (Ri i) → Π i j, (Rij i j) := sorry

def β2 : Π j, (Ri j) → Π i j, (Rij i j) := sorry
