/-
Tag 01HS

Lemma 25.5.1. Let R be a ring. Let f∈R.

    If g∈R and D(g)⊂D(f), then
        f is invertible in Rg,
        ge=af for some e≥1 and a∈R,
        there is a canonical ring map Rf→Rg, and
        there is a canonical Rf-module map Mf→Mg for any R-module M. 
    Any open covering of D(f) can be refined to a finite open covering of the form D(f)=⋃ni=1D(gi).
    If g1,…,gn∈R, then D(f)⊂⋃D(gi) if and only if g1,…,gn generate the unit ideal in Rf. 

Proof. Recall that D(g)=Spec(Rg) (see tag 00E4). Thus (a) holds because f maps to an element of Rg which
 is not contained in any prime ideal, and hence invertible, see tag 00E0. Write the inverse of f in Rg as a/gd.
 This means gd−af is annihilated by a power of g, whence (b). For (c), the map Rf→Rg exists by (a) from the
 universal property of localization, or we can define it by mapping b/fn to anb/gne. The equality Mf=M⊗RRf can be used to obtain the map on modules, or we can define Mf→Mg by mapping x/fn to anx/gne.

Recall that D(f) is quasi-compact, see tag 00F6. Hence the second statement follows directly from the fact that the standard opens form a basis for the topology.

The third statement follows directly from tag 00E0. 
-/

import Kenny_comm_alg.Zariski localization_UMP
import tensor_product 
import tag00E2 
import tag00E4
import tag00E8 -- Spec(R) is compact
import Kenny_comm_alg.avoid_powers algebra.module
import mathlib_someday.topology

universes u v

local attribute [instance] classical.prop_decidable

-- the next line should not be here. It's in broken Atiyah.lean.
-- KB added it to localization_UMP in localization namespace

--def is_unit {α : Type u} [comm_ring α] (x : α) := ∃ y, x * y = 1 

--localization.of_comm_ring :
--  Π (α : Type u_1) [_inst_1 : comm_ring α] (S : set α) [_inst_2 : is_submonoid α S], α → localization.loc α S

example (R : Type u) [comm_ring R] (f : R) : topological_space (X R) := by apply_instance 

/-- Stacks project tag 01HS -/
lemma lemma_standard_open_1b (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  ∃ e : ℕ, ∃ a, g^e = a*f :=
have h1 : ¬∀ n, g^n ∉ span {f},
from λ h,
  let P := @@is_ideal.avoid_powers _ g (span {f}) is_ideal_span h in
  have h1 : ∀ n : ℕ, g ^ n ∉ P,
    from @@is_ideal.avoid_powers.avoid_powers _ g (span {f}) is_ideal_span h,
  have h2 : span {f} ⊆ P,
    from @is_ideal.avoid_powers.contains _ _ g (span {f}) is_ideal_span h,
  have h3 : is_prime_ideal P,
    from @@is_ideal.avoid_powers.is_prime_ideal _ g (span {f}) is_ideal_span h,
  have h4 : (⟨P, h3⟩ : X R) ∈ Spec.D' g,
    from λ h5, h1 1 $ by simpa [monoid.pow] using h5,
  H h4 $ h2 $ subset_span $ set.mem_singleton f,
begin
  simp [not_forall, span, span_singleton] at h1,
  rcases h1 with ⟨e, a, h⟩,
  exact ⟨e, a, h.symm⟩
end

lemma lemma_standard_open_1a (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  localization.is_unit (localization.of_comm_ring R (powers g) f) :=
let ⟨e, a, h⟩ := lemma_standard_open_1b R f g H in
⟨⟦(a,(⟨g^e,⟨e,rfl⟩⟩:powers g))⟧,
 quotient.sound $ ⟨(1:R), ⟨0, rfl⟩, by simp [h, mul_comm]⟩⟩

noncomputable def lemma_standard_open_1c (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  localization.away f → localization.away g :=
localization.away.extend_map_of_im_unit
  (localization.of_comm_ring R (powers g))
  (lemma_standard_open_1a R f g H) -- regardless of my incompetence above, I now need that
  -- if p:R->S is a ring hom and image of f is a unit then there's a unique q:R[1/f]->S
  -- such that p is q ∘ localization.of_comm_ring . Do we have this?

  -- Note that this lemma should have a uniqueness statement too, saying that there is precisely
  -- one R-algebra morphism between these rings. The uniqueness is essential because we want
  -- define O_X(U) to be R[1/f] if U=D(f), however this is not well-defined, so I propose
  -- defining it as the subring of the product (over all f such that )

instance lemma_standard_open_1c.is_ring_hom (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  is_ring_hom (lemma_standard_open_1c R f g H) :=
localization.away.extend_map_of_im_unit.is_ring_hom _ _

local attribute [instance] is_ring_hom.to_module

set_option eqn_compiler.zeta true
def lemma_standard_open_1c.is_linear_map (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f)) :
  is_linear_map (lemma_standard_open_1c R f g H) :=
{ add := λ x y, is_ring_hom.map_add _,
  smul := λ c x, calc
          lemma_standard_open_1c R f g H (localization.of_comm_ring R _ c * x)
        = lemma_standard_open_1c R f g H (localization.of_comm_ring R _ c) * lemma_standard_open_1c R f g H x : is_ring_hom.map_mul _
    ... = localization.of_comm_ring R _ c * lemma_standard_open_1c R f g H x : congr_arg (λ z, z * lemma_standard_open_1c R f g H x) (localization.away.extend_map_extends _ _ _) }

noncomputable def lemma_standard_open_1d (R : Type u) [comm_ring R] (f : R) (g : R) (H : Spec.D'(g) ⊆ Spec.D'(f))
  (M : Type) [module R M] :
  tensor_product M (localization.loc R (powers f)) → tensor_product M (localization.loc R (powers g)) :=
tensor_product.tprod_map
  is_linear_map.id
  (lemma_standard_open_1c.is_linear_map R f g H)

set_option pp.proofs true 

def lemma_standard_open_2 (R : Type u) [comm_ring R] (f : R) (α : Type u) 
  (cover : α → set (X R)) (Hcover : ∀ i : α, topological_space.is_open (Zariski R) (cover i)) : 
  set.Union cover = Spec.D'(f) → ∃ γ : Type u, ∃ refine : γ → α, ∃ g : γ → R,
  ∃ H : fintype γ, (∀ m : γ, Spec.D'(g m) ⊆ cover (refine m)) ∧ set.Union (λ m, Spec.D'(g m)) = Spec.D'(f)  
   := 

begin
  intro cover_covers,
  let Rf := localization.away f, -- R[1/f]
  have H1 : compact (@set.univ (X Rf)) := lemma_quasi_compact,
  let g := localization.of_comm_ring R (powers f),
  let φ := Zariski.induced g,
--   in
--  topological_space.open_immersion φ ∧ φ '' set.univ = Spec.D'(f) :=
  have H2 : compact (Spec.D' f),
    rw (lemma_standard_open R f).2.symm,
    exact compact_image H1 (Zariski.induced.continuous g),
  -- now refine cover to be a cover by basis elements
  -- first a bunch of axiom of choice nonsense
  let basis_cover := λ (i : α), classical.some (topological_space.Union_basis_elements_of_open (D_f_form_basis R) (Hcover i)),
  have basis_cover_proof : ∀ (i : α),
    (∃ (f : (basis_cover i) → set (X R)), cover i = set.Union f ∧ ∀ (t : (basis_cover i)), f t ∈ standard_basis R)
  := λ (i : α), classical.some_spec (topological_space.Union_basis_elements_of_open (D_f_form_basis R) (Hcover i)),
  -- and we now need a lemma that says that any open is a union of basis elements
  -- then we build beta as a sigma type
  -- and beta has a map to alpha
  let β := Σ (i : α), basis_cover i,
  let basis_cover_proof_function := λ i, classical.some (basis_cover_proof i),
  have basis_cover_proof_proof : ∀ (i : α),
  (cover i = set.Union (basis_cover_proof_function i)) ∧ (∀ (j : basis_cover i), (basis_cover_proof_function i) j ∈ standard_basis R)
  := λ i, classical.some_spec (basis_cover_proof i),

  let cover' : β → set (X R) := λ j,basis_cover_proof_function j.1 j.2, 
  -- claim that cover' is a cover
  have Hcover' : set.Union cover' = Spec.D' f,
    rw set.subset.antisymm_iff,
    split,
    { intros b Hb,
      cases Hb with V HV,cases HV with HV Hb,cases HV with j Hj,
      have Htemp := (basis_cover_proof_proof j.1).1,
      -- ready for proof now
      rw ←cover_covers,
      apply set.subset_Union cover j.1,
      rw Htemp,
      apply set.subset_Union (basis_cover_proof_function j.1) j.2,
      suffices : basis_cover_proof_function (j.1) (j.2) = cover' j,
        rwa [this,←Hj],
      refl,
    },
    { intro y,
      rw ←cover_covers,
      intro Hy,
      cases Hy with V HV,
      cases HV with HV Hy,
      cases HV with i Hi,
      rw Hi at Hy,
      rw (basis_cover_proof_proof i).1 at Hy,
      cases Hy with W HW,
      cases HW with H HW,
      cases H with i2 Hi2,
      existsi W,
      existsi _,assumption,
      existsi (⟨i,i2⟩ : β),
      exact Hi2,
    },
  have H := compact_elim_finite_subcover H2,
    show set (set (X R)),
    exact (set.range cover'),
  have H' : (∀ (t : set (X R)), t ∈ set.range cover' → is_open t),
    intros U HU,
    cases HU with j Hj,
    rw ←Hj,
    apply topological_space.is_open_of_is_topological_basis (D_f_form_basis R),
    exact (basis_cover_proof_proof j.1).2 j.2,
  have H'' : Spec.D' f ⊆ ⋃₀ set.range cover',
    rw ←Hcover',
    rw ←set.Union_eq_sUnion_range,
  have H3 := H H' H'',clear H H' H'',
  -- I've morally deone it now.
  -- I just need to interface my way to the results.
  cases H3 with fcover H,
  cases H with Hf Hc,
  existsi {k // k ∈ fcover},
  existsi _,tactic.swap,
    intro kk,
    have H : kk.1 ∈ set.range cover',
      exact Hf kk.2,
    let j := classical.some H,
    have jproof : cover' j = kk.val := classical.some_spec H,
    exact j.1,
  existsi _,tactic.swap,
    intro kk,
    have H : kk.1 ∈ set.range cover',
      exact Hf kk.2,
    let j := classical.some H,
    have j'proof : cover' j = kk.val := classical.some_spec H,
    have H2 := (basis_cover_proof_proof j.1).2 j.2,
    exact classical.some H2,
  existsi _,tactic.swap,
    exact set.finite.fintype Hc.1,
  split,
  { intros U x Hx,
    let j := classical.some (Hf (U.property)),
    show x ∈ cover (j.1),
    let g := classical.some ((basis_cover_proof_proof (j.fst)).right (j.snd)),
    have gproof : basis_cover_proof_function (j.fst) (j.snd) = Spec.D' (g) := classical.some_spec ((basis_cover_proof_proof (j.fst)).right (j.snd)),
    change x ∈ Spec.D' g at Hx,
    rw (basis_cover_proof_proof (j.fst)).1,
    existsi cover' j,
    existsi _,tactic.swap,
      existsi j.2,
      refl,
    show x ∈ basis_cover_proof_function (j.fst) (j.snd),
    rwa gproof,
  },
  show (⋃ (U : {k // k ∈ fcover}),
       Spec.D'
         (classical.some
            ((basis_cover_proof_proof ((classical.some (Hf (U.property))).fst)).right
               ((classical.some (Hf (U.property))).snd)))) =
    Spec.D' f,
  rw set.subset.antisymm_iff,
  split,
  { refine set.Union_subset _,
    intro U,
    let j := classical.some (Hf (U.property)),
    let g := classical.some ((basis_cover_proof_proof (j.fst)).right (j.snd)),
    have gproof : basis_cover_proof_function (j.fst) (j.snd) = Spec.D' (g) := classical.some_spec ((basis_cover_proof_proof (j.fst)).right (j.snd)),
    show Spec.D' g ⊆ Spec.D' f,
    rw ←gproof,
    refine @set.subset.trans _ _ (cover j.fst) _ _ _,
    { rw (basis_cover_proof_proof j.fst).1,
      exact set.subset_Union _ _,
    },
  rw ←cover_covers,
  apply set.subset_Union,
  },
  -- gamble
  suffices : ⋃₀ fcover = ⋃ (U : {k // k ∈ fcover}),
      Spec.D'
        (classical.some
           ((basis_cover_proof_proof ((classical.some (Hf (U.property))).fst)).right
              ((classical.some (Hf (U.property))).snd))),
    rw ←this,
    exact Hc.2,
  -- is this true?
  have H : ∀ U : {k // k ∈ fcover}, U.1 = Spec.D'
        (classical.some
           ((basis_cover_proof_proof ((classical.some (Hf (U.property))).fst)).right
              ((classical.some (Hf (U.property))).snd))),
    intro U,
    let j := classical.some (Hf (U.property)),
    let g := classical.some ((basis_cover_proof_proof (j.fst)).right (j.snd)),
    have gproof : basis_cover_proof_function (j.fst) (j.snd) = Spec.D' (g) := classical.some_spec ((basis_cover_proof_proof (j.fst)).right (j.snd)),
    show U.val = Spec.D' g,
    rw ←gproof,
    have jproof : cover' j = U.val := classical.some_spec (Hf (U.property)),
    rw ←jproof,
  rw set.sUnion_eq_Union,
  show (⋃ (U : {k // k ∈ fcover}), U.val) = _,
  rw funext H, -- many thanks Chris Hughes for that classy finish :-)
end 

lemma zariski.basis_is_compact (R : Type u) [comm_ring R] : basis_is_compact (D_f_form_basis R) :=
begin
  intros U HU,
  cases HU with f Hf,
  intros α Ui HUi cover,
  have H := lemma_standard_open_2 R f α Ui begin
    intro i,
    exact topological_space.is_open_of_is_topological_basis (D_f_form_basis R) (HUi i),
  end
  begin
    rw ←Hf,
    rw cover,
  end,
  cases H with γ Hγ,
  existsi γ,
  cases Hγ with f Hγ,
  cases Hγ with g Hγ,
  cases Hγ with Hfin Hγ,
  existsi Hfin, 
  existsi f,
  refine set.subset.antisymm _ _,
    refine set.Union_subset _,
    rw ←cover,
    intro j,
    apply set.subset_Union,    
  rw Hf,
  rw ←Hγ.2,
  intros x Hx,
  cases Hx with V HV,
  cases HV with HV Hx,
  cases HV with j Hj,
  change V = Spec.D' (g j) at Hj,
  suffices :  ∃ (i : γ), x ∈ Ui (f i),
    simpa using this,
  existsi j,
  apply Hγ.1 j,
  rwa ←Hj,
end
