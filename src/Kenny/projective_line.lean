import Kenny.sheaf_of_rings_on_opens instances.affine_scheme data.polynomial

universes u v w

open topological_space

namespace localization

variables {R : Type u} [comm_ring R]

theorem away.inv_self_mul_of (x : R) :
  away.inv_self x * of x = 1 :=
show mk (1 * x) (⟨x, _⟩ * 1) = 1,
by rw [one_mul, mul_one, mk_self]

theorem away.of_mul_inv_self (x : R) :
  of x * away.inv_self x = 1 :=
show mk (x * 1) (1 * ⟨x, _⟩) = 1,
by rw [one_mul, mul_one, mk_self]

theorem away.lift'_inv_self (x : R) {A : Type v} [comm_ring A]
  (f : R → A) [is_ring_hom f] (g hg) :
  lift' f g hg (away.inv_self x) = ((g ⟨x, 1, pow_one x⟩)⁻¹ : units A) :=
by rw [away.inv_self, lift'_mk, is_ring_hom.map_one f, one_mul]

theorem inj_Zariski_induced_localization_of (S : set R) [is_submonoid S] :
  function.injective (Zariski.induced (of : R → localization R S)) :=
λ p q h, subtype.eq $
calc  p.1
    = ideal.map of (ideal.comap of p.1)       : (map_comap _ _).symm
... = ideal.map of ((Zariski.induced of p).1) : rfl
... = ideal.map of ((Zariski.induced of q).1) : by rw h
... = ideal.map of (ideal.comap of q.1)       : rfl
... = q.1                                     : map_comap _ _

-- theorem Zariski_induced_localization_of_D (S : set R) [is_submonoid S] (r : R) (s : S) :
--   Zariski.induced of '' (Spec.DO (localization R S) (mk r s)).1 =
--   Spec.DO R r :=
-- set.ext $ λ p, ⟨λ ⟨q, hq, hqp⟩, by change mk r s ∉ q.1.1 at hq, _⟩
-- #exit

theorem map_eq (S : set R) [is_submonoid S] (I : ideal R) :
  (I.map (of : R → localization R S)).1 = { m | ∃ r ∈ I, ∃ s ∈ S, mk r ⟨s, H⟩ = m } :=
set.ext $ λ x, ⟨λ hx, submodule.span_induction hx
  (λ x ⟨r, hrI, hrx⟩, ⟨r, hrI, 1, is_submonoid.one_mem S, hrx⟩)
  ⟨0, I.zero_mem, 1, is_submonoid.one_mem S, rfl⟩
  (λ x y ⟨r1, hrI1, s1, hs1, ihx⟩ ⟨r2, hrI2, s2, hs2, ihy⟩, ⟨s1 * r2 + s2 * r1,
    I.add_mem (I.mul_mem_left hrI2) (I.mul_mem_left hrI1), s1 * s2,
    is_submonoid.mul_mem hs1 hs2, by rw [← ihx, ← ihy]; refl⟩)
  (λ c x ⟨r, hrI, s, hs, hx⟩, localization.induction_on c $ λ r2 s2,
    ⟨r2 * r, I.mul_mem_left hrI, s2.1 * s, is_submonoid.mul_mem s2.2 hs, hx ▸ rfl⟩),
λ ⟨r, hrI, s, hs, hx⟩, by rw [← hx, mk_eq]; exact
(I.map (of : R → localization R S)).mul_mem_right (ideal.mem_map_of_mem hrI)⟩

theorem mem_map (S : set R) [is_submonoid S] (I : ideal R) (x : localization R S) :
  x ∈ I.map (of : R → localization R S) ↔ ∃ r ∈ I, ∃ s ∈ S, mk r ⟨s, H⟩ = x :=
show x ∈ (I.map of).1 ↔ _, by rw map_eq; refl

theorem comap_map (S : set R) [is_submonoid S] (I : ideal R) :
  ((I.map (of : R → localization R S)).comap of).1 = { r | ∃ s ∈ S, r * s ∈ I } :=
begin
  change of ⁻¹' (I.map of).1 = _, rw map_eq, ext x, split,
  { rintros ⟨r, hrI, s, hs, hx⟩, rcases quotient.exact hx with ⟨t, htS, ht⟩,
    change (s * x - 1 * r) * t = 0 at ht, rw [sub_mul, one_mul, sub_eq_zero] at ht,
    refine ⟨s * t, is_submonoid.mul_mem hs htS, _⟩, rw [mul_left_comm, ← mul_assoc, ht], exact I.mul_mem_right hrI },
  { rintros ⟨s, hs, hxsI⟩, refine ⟨x * s, hxsI, s, hs, mk_mul_cancel_right x ⟨s, hs⟩⟩ }
end

theorem mem_comap_map (S : set R) [is_submonoid S] (I : ideal R) (x : R) :
  x ∈ (I.map (of : R → localization R S)).comap of ↔ ∃ s ∈ S, x * s ∈ I :=
show x ∈ ((I.map of).comap of).1 ↔ _, by rw comap_map; refl

theorem prime_map (S : set R) [is_submonoid S]
  (p : ideal R) (hp1 : p.is_prime) (hp2 : S ∩ p.1 = ∅) :
  (p.map (of : R → localization R S)).is_prime :=
begin
  rw set.eq_empty_iff_forall_not_mem at hp2, split,
  { intros h1,
    have h2 : ((p.map (of : R → localization R S)).comap of).1 = set.univ, { rw h1, refl },
    rw [comap_map, set.eq_univ_iff_forall] at h2,
    rcases h2 1 with ⟨s, hs, hsp⟩,
    rw one_mul at hsp,
    exact hp2 s ⟨hs, hsp⟩ },
  intros x y, refine localization.induction_on x (λ r1 s1, localization.induction_on y (λ r2 s2, _)),
  cases s1 with s1 hs1, cases s2 with s2 hs2,
  rw [mem_map, mem_map, mem_map], rintros ⟨r, hrp, s, hs, h1⟩,
  rcases quotient.exact h1 with ⟨t, hts, ht⟩,
  change (s * (r1 * r2) - s1 * s2 * r) * t = 0 at ht, rw [sub_mul, sub_eq_zero] at ht,
  have h2 : s1 * s2 * r * t ∈ p := p.mul_mem_right (p.mul_mem_left hrp), rw ← ht at h2,
  have hsp : s ∉ p := mt (and.intro hs) (hp2 s),
  have htp : t ∉ p := mt (and.intro hts) (hp2 t),
  replace h2 := (hp1.2 h2).resolve_right htp,
  replace h2 := (hp1.2 h2).resolve_left hsp,
  cases hp1.2 h2 with hrp1 hrp2,
  { exact or.inl ⟨r1, hrp1, s1, hs1, rfl⟩ },
  { exact or.inr ⟨r2, hrp2, s2, hs2, rfl⟩ }
end

end localization

variables {R : Type u} [comm_ring R]

theorem range_Zariski_induced_localization_of (S : set R) [is_submonoid S] :
  set.range (Zariski.induced (localization.of : R → localization R S)) = ⋂ s ∈ S, (Spec.DO R s).1 :=
set.ext $ λ p, ⟨λ ⟨q, hqp⟩, hqp ▸ set.mem_bInter (λ s hs hsq, p.2.1 $ p.1.eq_top_iff_one.2 $
  have localization.mk s ⟨s, hs⟩ = 1, from localization.mk_self,
  by rw ← hqp; change localization.of (1:R) ∈ q.1; rw [localization.of_one, ← this, localization.mk_eq]; exact q.1.mul_mem_right hsq),
λ hp, ⟨⟨ideal.map localization.of p.1, localization.prime_map _ _ p.2 (set.eq_empty_iff_forall_not_mem.2 $ λ r hr, set.mem_bInter_iff.1 hp r hr.1 hr.2)⟩,
subtype.eq $ ideal.ext $ λ x,
⟨λ hx, let ⟨s, hs, hxsp⟩ := (localization.mem_comap_map _ _ _).1 hx in
  (p.2.2 hxsp).resolve_right $ set.mem_bInter_iff.1 hp s hs,
λ hx, (localization.mem_comap_map _ _ _).2 ⟨1, is_submonoid.one_mem S, by rwa mul_one⟩⟩⟩⟩

@[simp] theorem Spec.D'_one : Spec.D' (1:R) = set.univ :=
set.eq_univ_of_forall $ λ p hp, p.2.1 $ p.1.eq_top_iff_one.2 hp

@[simp] theorem Spec.DO_one : Spec.DO R 1 = ⊤ :=
opens.ext Spec.D'_one

@[simp] theorem Spec.D'_pow_succ (x : R) (n : ℕ) : Spec.D' (x^(n+1)) = Spec.D' x :=
set.ext $ λ p, not_congr ⟨p.2.mem_of_pow_mem (n+1), p.1.mul_mem_right⟩

@[simp] theorem Spec.DO_pow_succ (x : R) {n : ℕ} : Spec.DO R (x^(n+1)) = Spec.DO R x :=
opens.ext $ Spec.D'_pow_succ x n

theorem range_Zariski_induced_localization_away_of (x : R) :
  set.range (Zariski.induced (localization.of : R → localization.away x)) = (Spec.DO R x).1 :=
(range_Zariski_induced_localization_of _).trans $ set.subset.antisymm
  (set.bInter_subset_of_mem ⟨1, pow_one x⟩)
  (set.subset_bInter $ λ r ⟨n, hxnr⟩, hxnr ▸ nat.cases_on n
    (by rw [pow_zero, Spec.DO_one]; exact set.subset_univ _)
    (λ n, by rw Spec.DO_pow_succ; exact set.subset.refl _))

theorem exists_Zariski_induced_of_not_mem (x : R) (p : Spec R) (hp : x ∉ p.1) :
  ∃ q : Spec (localization.away x), Zariski.induced localization.of q = p :=
((set.ext_iff _ _).1 (range_Zariski_induced_localization_away_of x) _).2 hp

theorem localization.mk_mem_iff (S : set R) [is_submonoid S] (I : ideal (localization R S))
  (r : R) (s : S) : localization.mk r s ∈ I ↔ localization.of r ∈ I :=
⟨λ hx, have localization.mk r s * localization.mk s 1 ∈ I := I.mul_mem_right hx,
by rwa [localization.mk_mul_mk, mul_one, localization.mk_mul_cancel_right] at this,
λ hx, by rw localization.mk_eq_mul_mk_one; exact I.mul_mem_right hx⟩

theorem Zariski_induced_localized_of_V (S : set R) [is_submonoid S]
  (E : set (localization R S)) :
  Zariski.induced localization.of '' Spec.V E = Spec.V { r | ∃ s : S, localization.mk r s ∈ E } ∩ set.range (Zariski.induced (localization.of : R → localization R S)) :=
set.ext $ λ p,
⟨λ ⟨q, hq, hqp⟩, ⟨λ r ⟨s, hrs⟩, hqp ▸ (localization.mk_mem_iff _ _ _ _).1 (hq hrs), q, hqp⟩,
λ ⟨hp, q, hqp⟩, ⟨q, λ x, localization.induction_on x $ λ r s hrs, (localization.mk_mem_iff _ _ _ _).2
  (show r ∈ (Zariski.induced localization.of q).1, from hqp.symm ▸ hp ⟨s, hrs⟩),
hqp⟩⟩

theorem set.image_compl_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : function.injective f) (s : set α) :
  f '' -s = set.range f \ f '' s :=
set.ext $ λ b, ⟨λ ⟨a, hnas, hab⟩, ⟨⟨a, hab⟩, λ ⟨x, hxs, hxb⟩, hnas (hf (hxb.trans hab.symm) ▸ hxs)⟩,
λ ⟨⟨a, hab⟩, hnbs⟩, ⟨a, λ has, hnbs (hab ▸ ⟨a, has, rfl⟩), hab⟩⟩

theorem set.diff_inter {α : Type u} (s t u : set α) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
set.ext $ λ x, by simp only [set.mem_diff, set.mem_inter_iff, set.mem_union, not_and, auto.classical.implies_iff_not_or, and_or_distrib_left]

theorem Zariski_induced_localized_of_D (S : set R) [is_submonoid S]
  (E : set (localization R S)) :
  Zariski.induced localization.of '' Spec.D E = Spec.D { r | ∃ s : S, localization.mk r s ∈ E } ∩ set.range (Zariski.induced (localization.of : R → localization R S)) :=
by rw [Spec.D, set.image_compl_of_injective (localization.inj_Zariski_induced_localization_of S), Zariski_induced_localized_of_V,
    set.diff_inter, set.diff_self, set.union_empty, set.inter_comm]; refl

theorem Zariski.is_open_iff (U : set (Spec R)) : is_open U ↔ ∃ E : set R, Spec.D E = U :=
⟨λ ⟨E, HE⟩, ⟨E, set.compl_compl U ▸ HE ▸ rfl⟩, λ ⟨E, HE⟩, ⟨E, HE ▸ (set.compl_compl $ Spec.V E).symm⟩⟩

theorem open_Zariski_induced_localization_of (x : R) (U : set (Spec (localization.away x))) (hu : is_open U) :
  is_open (Zariski.induced localization.of '' U) :=
let ⟨E, HEU⟩ := (Zariski.is_open_iff U).1 hu in by rw [← HEU, Zariski_induced_localized_of_D, range_Zariski_induced_localization_away_of];
exact is_open_inter ((Zariski.is_open_iff _).2 ⟨_, rfl⟩) (Spec.DO R x).2

@[simp] lemma congr_arg_Zariski {A : Type v} [comm_ring A]
  {f g : R → A} [is_ring_hom f] [is_ring_hom g] (h : f = g) (p) :
  Zariski.induced f p = Zariski.induced g p :=
subtype.eq $ ideal.ext $ λ x, show f x ∈ p.1 ↔ g x ∈ p.1, by rw h

@[simp] lemma Zariski_induced_id (p) :
  Zariski.induced (id : R → R) p = p :=
subtype.eq $ ideal.ext $ λ x, iff.rfl

@[simp] lemma Zariski_induced_comp {A : Type v} [comm_ring A] {B : Type w} [comm_ring B]
  (f : R → A) [is_ring_hom f] (g : A → B) [is_ring_hom g] (p) :
  Zariski.induced (g ∘ f) p = Zariski.induced f (Zariski.induced g p) :=
rfl

namespace projective_line

variables (R) [decidable_eq R]

def inr_aux : polynomial R → localization.away (polynomial.X : polynomial R) :=
polynomial.eval₂ (localization.of ∘ polynomial.C) (localization.away.inv_self (polynomial.X))

set_option class.instance_max_depth 52 -- not one lower
instance is_ring_hom_inr_aux : is_ring_hom (inr_aux R) :=
polynomial.eval₂.is_ring_hom _

def inverse : localization.away (polynomial.X : polynomial R) → localization.away (polynomial.X : polynomial R) :=
localization.lift'
  (inr_aux R)
  (λ p, ⟨inr_aux R p.1, localization.of p.1,
    by rcases p with ⟨_, n, rfl⟩; rw [inr_aux, polynomial.eval₂_pow, polynomial.eval₂_X,
      localization.of_pow, ← mul_pow, localization.away.inv_self_mul_of, one_pow],
    by rcases p with ⟨_, n, rfl⟩; rw [inr_aux, polynomial.eval₂_pow, polynomial.eval₂_X,
      localization.of_pow, ← mul_pow, localization.away.of_mul_inv_self, one_pow]⟩)
  (λ p, rfl)

instance is_ring_hom_inverse : is_ring_hom (inverse R) :=
localization.lift'.is_ring_hom _ _ _

theorem inverse_inverse : inverse R ∘ inverse R = id :=
@@localization.funext _ _ _ (inverse R ∘ inverse R) _ (is_ring_hom.comp _ _) is_ring_hom.id $ λ p,
polynomial.induction_on p
  (λ r, by simp only [inverse, function.comp_apply, localization.lift'_coe, localization.lift'_of, inr_aux, polynomial.eval₂_C]; refl)
  (λ p q hp hq, by rw [localization.coe_add, is_ring_hom.map_add (inverse R ∘ inverse R), hp, hq]; refl)
  (λ n r ih, by rw [pow_add, pow_one, ← mul_assoc, localization.coe_mul, is_ring_hom.map_mul (inverse R ∘ inverse R), ih];
    simp only [inverse, function.comp_apply, localization.lift'_coe, localization.lift'_of, inr_aux, polynomial.eval₂_X,
        localization.away.lift'_inv_self]; refl)

theorem Zariski_induced_inverse (p : Spec (localization.away (polynomial.X : polynomial R))) :
  Zariski.induced (inverse R) (Zariski.induced (inverse R) p) = p :=
calc  Zariski.induced (inverse R) (Zariski.induced (inverse R) p)
    = Zariski.induced (inverse R ∘ inverse R) p : (Zariski_induced_comp (inverse R) (inverse R) p).symm
... = Zariski.induced id p : congr_arg_Zariski (inverse_inverse R) p
... = p : Zariski_induced_id p

set_option class.instance_max_depth 32

inductive r : Spec (polynomial R) ⊕ Spec (polynomial R) → Spec (polynomial R) ⊕ Spec (polynomial R) → Prop
| inv : ∀ p : Spec (localization.away (polynomial.X : polynomial R)),
    r (sum.inl $ Zariski.induced localization.of p) (sum.inr $ Zariski.induced (inr_aux R) p)

end projective_line

def projective_line (R : Type u) [comm_ring R] [decidable_eq R] : Type u :=
quot (projective_line.r R)

namespace projective_line

variables (R) [decidable_eq R]

def inl (p : Spec (polynomial R)) : projective_line R :=
quot.mk _ $ sum.inl p

def inr (p : Spec (polynomial R)) : projective_line R :=
quot.mk _ $ sum.inr p

instance : topological_space (projective_line R) :=
{ is_open := λ s, is_open (inl R ⁻¹' s) ∧ is_open (inr R ⁻¹' s),
  is_open_univ := ⟨is_open_univ, is_open_univ⟩,
  is_open_inter := λ s t hs ht, ⟨is_open_inter hs.1 ht.1, is_open_inter hs.2 ht.2⟩,
  is_open_sUnion := λ S HS, ⟨by rw set.preimage_sUnion; exact is_open_bUnion (λ i his, (HS i his).1),
    by rw set.preimage_sUnion; exact is_open_bUnion (λ i his, (HS i his).2)⟩ }

theorem continuous_inl : continuous (inl R) :=
λ s hs, hs.1

theorem continuous_inr : continuous (inr R) :=
λ s hs, hs.2

theorem inj_indl : function.injective
  (Zariski.induced localization.of : Spec (localization.away (polynomial.X : polynomial R)) → Spec (polynomial R)) :=
localization.inj_Zariski_induced_localization_of (powers polynomial.X)

theorem inverse_comp_localization_of :
  inverse R ∘ localization.of = inr_aux R :=
funext $ λ p, by rw [inverse, function.comp_apply, localization.lift'_of]

theorem inj_indr : function.injective
  (Zariski.induced (inr_aux R) : Spec (localization.away (polynomial.X : polynomial R)) → Spec (polynomial R)) :=
have h2 : function.injective (Zariski.induced (inverse R)),
from (equiv.bijective { to_fun := Zariski.induced (inverse R), inv_fun := Zariski.induced (inverse R),
  left_inv := λ p, by rw [← Zariski_induced_comp, @@congr_arg_Zariski _ _ (inverse R ∘ inverse R) id (is_ring_hom.comp _ _) is_ring_hom.id (inverse_inverse R), Zariski_induced_id],
  right_inv := λ p, by rw [← Zariski_induced_comp, @@congr_arg_Zariski _ _ (inverse R ∘ inverse R) id (is_ring_hom.comp _ _) is_ring_hom.id (inverse_inverse R), Zariski_induced_id] }).1,
λ p1 p2 H, h2 $ inj_indl R $
by haveI : is_ring_hom (inverse R ∘ localization.of) := is_ring_hom.comp _ _;
calc  Zariski.induced localization.of (Zariski.induced (inverse R) p1)
    = Zariski.induced (inverse R ∘ localization.of) p1 : (Zariski_induced_comp _ _ _).symm
... = Zariski.induced (inr_aux R) p1 : congr_arg_Zariski (inverse_comp_localization_of R) p1
... = Zariski.induced (inr_aux R) p2 : H
... = Zariski.induced (inverse R ∘ localization.of) p2 : congr_arg_Zariski (inverse_comp_localization_of R).symm p2
... = Zariski.induced localization.of (Zariski.induced (inverse R) p2) : Zariski_induced_comp _ _ _

theorem exact (s t) (H : (quot.mk _ s : projective_line R) = quot.mk _ t) :
  s = t ∨ (∃ p, s = sum.inl (Zariski.induced localization.of p) ∧ t = sum.inr (Zariski.induced (inr_aux R) p)) ∨
  ∃ p, s = sum.inr (Zariski.induced (inr_aux R) p) ∧ t = sum.inl (Zariski.induced localization.of p) :=
begin
  replace H := quot.exact _ H, induction H,
  case eqv_gen.rel : _ _ h { cases h, exact or.inr (or.inl ⟨_, rfl, rfl⟩) },
  case eqv_gen.refl { left, refl },
  case eqv_gen.symm : _ _ _ ih { rcases ih with rfl | ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩,
    { exact or.inl rfl }, { exact or.inr (or.inr ⟨p, rfl, rfl⟩) },
    { exact or.inr (or.inl ⟨p, rfl, rfl⟩) } },
  case eqv_gen.trans : _ _ _ _ _ ih1 ih2 {
    rcases ih1 with rfl | ⟨p, rfl, rfl⟩ | ⟨p, rfl, rfl⟩,
    { exact ih2 },
    { rcases ih2 with rfl | ⟨q, ih2, rfl⟩ | ⟨q, ih2, rfl⟩,
      { exact or.inr (or.inl ⟨p, rfl, rfl⟩) },
      { cases ih2 },
      { replace ih2 := inj_indr R (sum.inr.inj ih2), subst ih2, exact or.inl rfl } },
    { rcases ih2 with rfl | ⟨q, ih2, rfl⟩ | ⟨q, ih2, rfl⟩,
      { exact or.inr (or.inr ⟨p, rfl, rfl⟩) },
      { replace ih2 := inj_indl R (sum.inl.inj ih2), subst ih2, exact or.inl rfl },
      { cases ih2 } } }
end

theorem inl_preimage_range_inr : inl R ⁻¹' set.range (inr R) = (Spec.DO (polynomial R) polynomial.X).1 :=
begin
  ext p, split,
  { rintros ⟨q, hq⟩ hp, rcases exact R _ _ hq with h | ⟨s, h1, h2⟩ | ⟨s, h1, h2⟩,
    { cases h }, { cases h1 },
    cases h2, exact s.2.1 (s.1.eq_top_of_is_unit_mem hp $ is_unit_of_mul_one _ _ $ localization.away.of_mul_inv_self _) },
  { rintros hp,
    rcases exists_Zariski_induced_of_not_mem _ _ hp with ⟨q, rfl⟩,
    use Zariski.induced (inr_aux R) q,
    symmetry, apply quot.sound, constructor }
end

theorem open_preimagelr : is_open (inl R ⁻¹' set.range (inr R)) :=
by rw inl_preimage_range_inr; exact D_fs_open _ _

set_option class.instance_max_depth 52
theorem inr_preimage_range_inl : inr R ⁻¹' set.range (inl R) = (Spec.DO (polynomial R) polynomial.X).1 :=
begin
  ext p, split,
  { rintros ⟨q, hq⟩ hp, rcases exact R _ _ hq with h | ⟨s, h1, h2⟩ | ⟨s, h1, h2⟩,
    { cases h },
    { cases h2,
      refine s.2.1 (s.1.eq_top_of_is_unit_mem hp $ is_unit_of_mul_one _ (localization.of polynomial.X) _),
      rw [inr_aux, polynomial.eval₂_X, localization.away.inv_self_mul_of] },
    { cases h1 } },
  { rintros hp,
    rcases exists_Zariski_induced_of_not_mem _ _ hp with ⟨q, rfl⟩,
    rw [← Zariski_induced_inverse R q, ← Zariski_induced_comp, congr_arg_Zariski.{u u} (inverse_comp_localization_of R)],
    split, apply quot.sound, constructor }
end
set_option class.instance_max_depth 32

theorem open_preimagerl : is_open (inr R ⁻¹' set.range (inl R)) :=
by rw inr_preimage_range_inl; exact D_fs_open _ _

theorem set.preimage_range {α : Type u} {β : Type v} {f : α → β} :
  f ⁻¹' set.range f = set.univ :=
set.eq_univ_of_forall $ λ x, ⟨x, rfl⟩

def opl : opens (projective_line R) :=
⟨set.range (inl R), by rw set.preimage_range; exact is_open_univ, open_preimagerl R⟩

def opr : opens (projective_line R) :=
⟨set.range (inr R), open_preimagelr R, by rw set.preimage_range; exact is_open_univ⟩

inductive pbool : Type u | ff | tt.

protected def covering : covering (⊤ : opens (projective_line R)) :=
{ γ := pbool,
  Uis := λ b, pbool.rec_on b (opl R) (opr R),
  Hcov := opens.ext $ set.eq_univ_of_forall $ λ x, quot.induction_on x $ λ p, sum.cases_on p
    (λ v, set.mem_sUnion.2 ⟨_, ⟨_, ⟨pbool.ff, rfl⟩, rfl⟩, v, rfl⟩)
    (λ v, set.mem_sUnion.2 ⟨_, ⟨_, ⟨pbool.tt, rfl⟩, rfl⟩, v, rfl⟩) }

def soropl : sheaf_of_rings_on_opens (projective_line R) (opl R) :=
sheaf_of_rings.pushforward (continuous_inl R) (structure_sheaf (polynomial R))

def soropr : sheaf_of_rings_on_opens (projective_line R) (opr R) :=
sheaf_of_rings.pushforward (continuous_inr R) (structure_sheaf (polynomial R))

def sorope : sheaf_of_rings_on_opens.equiv
  (sheaf_of_rings_on_opens.res_subset (soropl R) (opl R ⊓ opr R) lattice.inf_le_left)
  (sheaf_of_rings_on_opens.res_subset (soropr R) (opl R ⊓ opr R) lattice.inf_le_right) :=
sorry

def sor : sheaf_of_rings (projective_line R) :=
sheaf_of_rings_on_opens.sheaf_glue (projective_line.covering R).Uis
  (λ b, pbool.rec_on b (soropl R) (soropr R))
  (λ b₁ b₂, sorry)

end projective_line
