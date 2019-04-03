import ring_theory.localization
import preliminaries.localisation
import preliminaries.localisation_tests.localization_of

import spectrum_of_a_ring.properties

import sheaves.presheaf_of_rings_on_basis
import sheaves.sheaf_of_rings_on_standard_basis
import sheaves.locally_ringed_space
import spectrum_of_a_ring.spectrum
import spectrum_of_a_ring.zariski_topology
import spectrum_of_a_ring.standard_basis

universe u

open topological_space

local attribute [instance] classical.prop_decidable

noncomputable theory

variables {R : Type u} [comm_ring R]

open localization_alt

section maps

-- D(g) ⊆ D(f) → f ∈ R[1/g]*

lemma localization.inverts.of_Dfs_subset {f g : R} (H : Spec.D'(g) ⊆ Spec.D'(f)) 
: inverts (powers f) (localization.of : R → localization R (powers g)) :=
begin
  rintros ⟨fn, Hfn⟩,
  suffices Hsuff : ∃ si, (localization.of : R → localization R (powers g)) f * si = 1,
    rcases Hsuff with ⟨si, Hsi⟩,
    show ∃ si, localization.of fn * si = 1,
    rcases Hfn with ⟨n, Hfn⟩,
    rw ←Hfn,
    clear Hfn,
    induction n with n Hn,
    { simp, },
    { rw pow_succ,
      rw (@is_ring_hom.map_mul _ _ _ _ localization.of localization.of.is_ring_hom),
      rcases Hn with ⟨sin, Hn⟩,
      existsi (si * sin),
      rw ←mul_assoc,
      rw mul_assoc _ _ si,
      rw mul_comm _ si,
      rw ←mul_assoc,
      rw Hsi,
      rw one_mul,
      exact Hn, },
  unfold Spec.D' at H,
  rw set.compl_subset_compl at H,
  unfold Spec.V' at H,
  by_contra Hne,
  rw not_exists at Hne,
  have Hnu : ¬is_unit ((localization.of : R → localization R (powers g)) f),
    intros HC,
    simp [is_unit] at HC,
    rcases HC with ⟨u, HC⟩,
    apply (Hne u.inv),
    rw HC,
    exact u.3,
  let F : ideal (localization.away g) := ideal.span {(localization.of f)},
  have HFnT : F ≠ ⊤,
    intros HC,
    rw ideal.span_singleton_eq_top at HC,
    exact (Hnu HC),
  rcases (ideal.exists_le_maximal F HFnT) with ⟨S, ⟨HMS, HFS⟩⟩,
  have HfF : localization.of f ∈ F,
    suffices Hsuff : localization.of f ∈ {localization.of f},
      exact ideal.subset_span Hsuff,
    exact set.mem_singleton _,
  have HfM : localization.of f ∈ S := HFS HfF,
  have PS := ideal.is_maximal.is_prime HMS,
  have PS' : ideal.is_prime (ideal.comap localization.of S)
    := @ideal.is_prime.comap _ _ _ _ localization.of _ _ PS,
  let S' : Spec R := ⟨ideal.comap localization.of S, PS'⟩,
  have HfS' : f ∈ S'.val,
    rw ideal.mem_comap,
    exact HfM,
  replace HfS' : S' ∈ {P : Spec R | f ∈ P.val} := HfS',
  have HgS' : g ∈ ideal.comap localization.of S := H HfS',
  rw ideal.mem_comap at HgS',
  rcases (localization.coe_is_unit R (powers g) ⟨g, ⟨1, pow_one g⟩⟩) with ⟨w, Hw⟩,
  rcases w with ⟨w, winv, Hwwinv, Hwinvw⟩,
  change localization.of g = w at Hw,
  have HC : localization.of g * winv ∈ S := ideal.mul_mem_right S HgS',
  erw [Hw, Hwwinv] at HC,
  exact ((ideal.ne_top_iff_one S).1 PS.1) HC,
end

-- TODO : This can be done in general... Although it's not very nice.

def localization.inverts_data.of_Dfs_subset {f g : R} (H : Spec.D'(g) ⊆ Spec.D'(f)) 
: inverts_data (powers f) (localization.of : R → localization R (powers g)) :=
begin
  intros s,
  have Hs := localization.inverts.of_Dfs_subset H s,
  rcases (classical.indefinite_description _ Hs) with ⟨si, Hsi⟩,
  exact ⟨si, Hsi⟩,
end

-- D(g) ⊆ D(f) → ∃ a e, g^e = a * f.

lemma localization.inverts.of_Dfs_subset₂ {f g : R} (H : Spec.D'(g) ⊆ Spec.D'(f)) 
: ∃ (a : R) (e : ℕ), g^e = a * f :=
begin 
  have Hinv := localization.inverts.of_Dfs_subset H,
  rcases (Hinv ⟨f, ⟨1, pow_one f⟩⟩) with ⟨w, Hw⟩,
  dsimp only [subtype.coe_mk] at Hw,
  rcases (quotient.exists_rep w) with ⟨⟨a, ⟨gn, ⟨n, Hn⟩⟩⟩, Hagn⟩,
  erw [←Hagn, quotient.eq] at Hw,
  rcases Hw with ⟨gm, ⟨⟨m, Hm⟩, Hw⟩⟩,
  simp [-sub_eq_add_neg] at Hw,
  rw [sub_mul, sub_eq_zero, mul_assoc, mul_comm f, ←Hn, ←Hm, ←pow_add] at Hw,
  existsi [a * g ^ m, n + m],
  exact Hw,
end

-- Map from R[1/f] to R[1/g].

def localization.map.of_Dfs_subset {f g : R} (H : Spec.D'(g) ⊆ Spec.D'(f))
: localization R (powers f) → localization R (powers g) :=
is_localization_initial 
  (powers f)
  (localization.of : R → localization R (powers f))
  (localization.of.is_localization_data (powers f))
  (localization.of : R → localization R (powers g))
  (localization.inverts_data.of_Dfs_subset H)

end maps

section localization_S

-- Define S(U) so that R[1/f] ≃ R[1/S(D(f))].

def S (U : opens (Spec R)) : set R := { r : R | U.1 ⊆ Spec.D'(r) }

instance S.is_submonoid (U : opens (Spec R)) : is_submonoid (S U) :=
{ one_mem := λ ⟨P, PI⟩ HP, ((ideal.ne_top_iff_one P).1 PI.1),
  mul_mem := λ f g Hf Hg,
    begin
      show U.1 ⊆ Spec.D'(f*g),
      exact (Spec.D'.product_eq_inter f g).symm ▸ set.subset_inter Hf Hg,
    end, }

lemma S.rev_mono {U V : opens (Spec R)} (HVU : V ⊆ U) : S U ⊆ S V :=
λ x Hx, set.subset.trans HVU Hx

lemma S.f_mem (f : R) : f ∈ S (Spec.DO R (f)) := set.subset.refl _

lemma S.inter_subset_Sinter (U V : opens (Spec R)) : (S U) ∩ (S V) ⊆ S (U ∩ V) :=
begin
  rintros x ⟨HxU, HxV⟩,
  change U.1 ⊆ Spec.D'(x) at HxU,
  change V.1 ⊆ Spec.D'(x) at HxV,
  have H := set.inter_subset_inter HxU HxV,
  rw set.inter_self at H,
  exact H,
end

-- Proof of the localization property.

lemma localization.SDf.inverts_data (f : R) 
: inverts_data (powers f) (localization.of : R → localization R (S (Spec.DO R (f)))) :=
begin
  rintros ⟨s, Hs⟩,
  have HsS : s ∈ S (Spec.DO R (f)) := (is_submonoid.power_subset (S.f_mem f)) Hs,use [⟦⟨1, ⟨s, HsS⟩⟩⟧],
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  simp,
end

lemma localization.SDf.has_denom_data (f : R) 
: has_denom_data (powers f) (localization.of : R → localization R (S (Spec.DO R (f)))) :=
begin
  intros x,
  have Hx := quotient.exists_rep x,
  rcases (classical.indefinite_description _ Hx) with ⟨⟨p, q⟩, Hpq⟩,
  rcases q with ⟨q, Hq⟩,
  dsimp [S, Spec.DO] at Hq,
  have Hea := localization.inverts.of_Dfs_subset₂ Hq,
  rcases (classical.indefinite_description _ Hea) with ⟨a, He⟩,
  rcases (classical.indefinite_description _ He) with ⟨e, Hfe⟩,
  use [⟨⟨f^e, ⟨e, rfl⟩⟩, a * p⟩],
  dsimp only [subtype.coe_mk],
  rw [Hfe, ←Hpq],
  apply quotient.sound,
  use [1, is_submonoid.one_mem _],
  dsimp,
  ring,
end

lemma localization.SDf.ker_le (f : R)
: ker (localization.of : R → localization R (S (Spec.DO R (f)))) ≤ submonoid_ann (powers f) :=
begin 
  intros x Hx,
  change localization.of x = 0 at Hx,
  erw quotient.eq at Hx,
  rcases Hx with ⟨s, ⟨Hs, Hx⟩⟩,
  simp at Hx,
  dsimp [S, Spec.DO] at Hs,
  have Hea := localization.inverts.of_Dfs_subset₂ Hs,
  rcases (classical.indefinite_description _ Hea) with ⟨a, He⟩,
  rcases (classical.indefinite_description _ He) with ⟨e, Hfe⟩,
  use [⟨x, ⟨f^e, ⟨e, rfl⟩⟩⟩],
  { dsimp only [subtype.coe_mk],
    rw Hfe,
    rw mul_comm a,
    rw ←mul_assoc,
    rw Hx,
    rw zero_mul, },
  { refl, } 
end

lemma localization.SDf (f : R) 
: is_localization_data (powers f) (localization.of : R → localization R (S (Spec.DO R (f)))) :=
{ inverts := localization.SDf.inverts_data f,
  has_denom := localization.SDf.has_denom_data f, 
  ker_le := localization.SDf.ker_le f }

end localization_S

section structure_presheaf

variable (R)

-- Structure presheaf on Spec(R) defined on the basis.

@[reducible] def structure_presheaf_on_basis : presheaf_of_rings_on_basis (Spec R) (D_fs_basis R) := 
{ F := λ U BU, localization R (S U),
  res := λ U V BU BV HVU,
    begin
      have H := S.rev_mono HVU,
      apply quotient.lift (λ (x : R × (S U)), ⟦(x.1, (⟨x.2.1, H x.2.2⟩ : (S V)))⟧),
      { rintros ⟨a1, b1, Hb1⟩ ⟨a2, b2, Hb2⟩ ⟨t, Ht, Habt⟩,
        simp,
        use [t, H Ht, Habt], },
    end,
  Hid := λ U BU, funext $ λ x, quotient.induction_on x $ λ a, by simp,
  Hcomp := λ U V W BU BV BW HWV HVU, funext $ λ x, quotient.induction_on x $ λ a, by simp,
  Fring := λ U BU, by apply_instance,
  res_is_ring_hom := λ U V BU BV HVU,
      { map_one := rfl,
        map_add := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl,
        map_mul := λ x y, quotient.induction_on₂ x y $ λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, rfl, }, }

-- 𝒪(D(f)) = R[1/f].

lemma localization.structure_presheaf_on_basis.F (f : R) :
is_localization_data 
  (powers f)
  (localization.of : R → (structure_presheaf_on_basis R).F (D_fs.mem R f)) :=
localization.SDf f

-- -- From ρ : 𝒪(D(f)) → 𝒪(D(g)) deduce 

def localization.SDf.inverts_data.of_Dfs_subset {f g : R} (H : Spec.D'(g) ⊆ Spec.D'(f))
: inverts_data (powers f) (localization.of : R → (structure_presheaf_on_basis R).F (D_fs.mem R g)) :=
begin
  intros s,
  -- This will give us an inverse for s in R[1/g].
  have sinv := localization.inverts_data.of_Dfs_subset H s,
  rcases sinv with ⟨sinv, Hsinv⟩,
  -- Map from R[1/g] to R[1/S(D(g))].
  let φ := 
    is_localization_initial 
      (powers g)
      (localization.of : R → localization R (powers g))
      (localization.of.is_localization_data (powers g))
      (localization.of : R → (structure_presheaf_on_basis R).F (D_fs.mem R g))
      (localization.SDf.inverts_data g),
  use [φ sinv],
  -- Use composition.
  rw ←is_localization_initial_comp 
    (powers g)
    (localization.of : R → localization R (powers g))
    (localization.of.is_localization_data (powers g))
    (localization.of : R → (structure_presheaf_on_basis R).F (D_fs.mem R g))
    (localization.SDf.inverts_data g),
  rw ←is_ring_hom.map_mul φ,
  rw Hsinv,
  rw is_ring_hom.map_one φ,
end

def localization.SDf.map.of_Dfs_subset {f g : R} (H : Spec.D'(g) ⊆ Spec.D'(f))
: (structure_presheaf_on_basis R).F (D_fs.mem R f) 
→ (structure_presheaf_on_basis R).F (D_fs.mem R g) :=
is_localization_initial 
  (powers f)
  (localization.of : R → (structure_presheaf_on_basis R).F (D_fs.mem R f))
  (localization.SDf f)
  (localization.of : R → (structure_presheaf_on_basis R).F (D_fs.mem R g))
  (localization.SDf.inverts_data.of_Dfs_subset R H)

lemma localization.structure_presheaf_on_basis.res 
(f g : R) (H : Spec.DO R (g) ⊆ Spec.DO R (f)) :
  (structure_presheaf_on_basis R).res (D_fs.mem R f) (D_fs.mem R g) H
= localization.SDf.map.of_Dfs_subset R H :=
begin
  apply funext,
  intros x,
  apply quotient.induction_on x,
  rintros ⟨a, b⟩,
  simp [localization.SDf.map.of_Dfs_subset, is_localization_initial],
  rcases (localization.SDf f).has_denom ⟦(a, b)⟧ with ⟨⟨q, p⟩, Hpq⟩,
  dsimp at *,
  rcases localization.SDf.inverts_data.of_Dfs_subset R H q with ⟨w, Hw⟩,
  dsimp,
  revert Hw,
  apply quotient.induction_on w,
  rintros ⟨c, d⟩,
  intros Hw,
  apply quotient.sound,
  dsimp,
  dunfold localization.of at Hpq,
  erw quotient.eq at Hpq,
  rcases Hpq with ⟨t, ⟨Ht, Hpq⟩⟩,
  simp [-sub_eq_add_neg] at Hpq,
  dunfold localization.of at Hw,
  erw quotient.eq at Hw,
  rcases Hw with ⟨s, ⟨Hs, Hw⟩⟩,
  simp [-sub_eq_add_neg] at Hw,

  rcases (localization.inverts.of_Dfs_subset₂ H) with ⟨a₁, ⟨e₁, Ha₁⟩⟩,
  rcases (localization.inverts.of_Dfs_subset₂ Ht) with ⟨a₂, ⟨e₂, Ha₂⟩⟩,

  have Heq : t * a₂ * a₁ ^ e₂ = g ^ (e₁ * e₂),
    rw mul_comm at Ha₂,
    rw ←Ha₂,
    rw ←mul_pow,
    rw mul_comm at Ha₁,
    rw ←Ha₁,
    rw ←pow_mul,

  have HgS : g ∈ S (Spec.DO R g) := S.f_mem g,
  have HtS : t * a₂ * a₁ ^ e₂ ∈ S (Spec.DO R g) := Heq.symm ▸ is_submonoid.pow_mem HgS,

  use [s * (t * a₂ * a₁ ^ e₂), is_submonoid.mul_mem Hs HtS],
  simp [-sub_eq_add_neg],
  rw sub_mul,
  rw sub_mul at Hpq,
  rw sub_mul at Hw,
  rw sub_eq_zero,
  rw sub_eq_zero at Hpq,
  rw sub_eq_zero at Hw,
  repeat { rw ←mul_assoc },
  suffices Hsuff : ↑b * p * c * s * t = ↑d * a * s * t,
    erw Hsuff,
  
  iterate 2 { rw [mul_assoc _ _ t, mul_comm _ t, ←mul_assoc] },
  rw Hpq,

  symmetry,

  rw [mul_assoc _ _ s, mul_comm _ s, ←mul_assoc],
  rw Hw,

  ring,
end

def structure_presheaf : presheaf_of_rings (Spec R) :=
  presheaf_of_rings_on_basis_to_presheaf_of_rings 
    (D_fs_standard_basis R) 
    (structure_presheaf_on_basis R)

end structure_presheaf
