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

theorem prime_map_away (x : R)
  (p : ideal R) (hp1 : p.is_prime) (hp2 : x ∉ p) :
  (p.map (of : R → localization.away x)).is_prime :=
prime_map _ _ hp1 $ set.eq_empty_iff_forall_not_mem.2 $ λ r ⟨⟨n, hn⟩, hr⟩,
hp2 $ hp1.mem_of_pow_mem n (hn.symm ▸ hr)

theorem comap_map_away (x : R)
  (p : ideal R) (hp1 : p.is_prime) (hp2 : x ∉ p) :
  (p.map (localization.of : R → localization.away x)).comap localization.of = p :=
ideal.ext $ λ y, by rw localization.mem_comap_map; exact
⟨λ ⟨_, ⟨n, rfl⟩, h⟩, (hp1.2 h).resolve_right (mt (hp1.mem_of_pow_mem n) hp2),
λ hy, ⟨_, ⟨0, pow_zero x⟩, by rwa mul_one⟩⟩

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

theorem Zariski_induced_localization_of_V (S : set R) [is_submonoid S]
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

theorem Zariski_induced_localization_of_D (S : set R) [is_submonoid S]
  (E : set (localization R S)) :
  Zariski.induced localization.of '' Spec.D E = Spec.D { r | ∃ s : S, localization.mk r s ∈ E } ∩ set.range (Zariski.induced (localization.of : R → localization R S)) :=
by rw [Spec.D, set.image_compl_of_injective (localization.inj_Zariski_induced_localization_of S), Zariski_induced_localization_of_V,
    set.diff_inter, set.diff_self, set.union_empty, set.inter_comm]; refl

theorem Zariski.is_open_iff (U : set (Spec R)) : is_open U ↔ ∃ E : set R, Spec.D E = U :=
⟨λ ⟨E, HE⟩, ⟨E, set.compl_compl U ▸ HE ▸ rfl⟩, λ ⟨E, HE⟩, ⟨E, HE ▸ (set.compl_compl $ Spec.V E).symm⟩⟩

theorem open_Zariski_induced_localization_of (x : R) (U : set (Spec (localization.away x))) (hu : is_open U) :
  is_open (Zariski.induced localization.of '' U) :=
let ⟨E, HEU⟩ := (Zariski.is_open_iff U).1 hu in by rw [← HEU, Zariski_induced_localization_of_D, range_Zariski_induced_localization_away_of];
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

def ideal.principal (x : R) : ideal R :=
{ carrier := { r | ∃ y, x * y = r },
  zero := ⟨0, mul_zero x⟩,
  add := λ r s ⟨y, hy⟩ ⟨z, hz⟩, ⟨y + z, by rw [mul_add, hy, hz]⟩,
  smul := λ c r ⟨y, hy⟩, ⟨c * y, by rw [mul_left_comm, hy]; refl⟩ }

theorem ideal.mem_principal {x : R} : x ∈ ideal.principal x :=
⟨1, mul_one x⟩

theorem ideal.principal_le_iff {x : R} {I : ideal R} :
  ideal.principal x ≤ I ↔ x ∈ I :=
⟨λ hx, hx ideal.mem_principal, λ hx r ⟨y, hy⟩, hy ▸ I.mul_mem_right hx⟩

theorem exists_maximal_of_mem_nonunits {x : R} (hx : x ∈ nonunits R) :
  ∃ M : ideal R, M.is_maximal ∧ x ∈ M :=
by simpa only [ideal.principal_le_iff] using
  ideal.exists_le_maximal (ideal.principal x) ((ideal.ne_top_iff_one _).2 $ λ ⟨y, hy⟩, hx $ is_unit_of_mul_one _ _ hy)

noncomputable def of_Spec_top (R : Type u) [comm_ring R] : (Spec.locally_ringed_space R).O ⊤ → R :=
localization.lift id (λ r (hr : r ∈ S (⊤ : opens (Spec R))), classical.by_contradiction $ λ hrnu,
  let ⟨M, hm, hxm⟩ := exists_maximal_of_mem_nonunits hrnu in
  @hr ⟨M, hm.is_prime⟩ trivial hxm) ∘
of_presheaf_of_rings_extension _ (D_fs_standard_basis R) _ structure_presheaf_on_basis_is_sheaf_on_basis (D_fs_standard_basis R).1

instance of_Spec_top.is_ring_hom : is_ring_hom (of_Spec_top R) :=
by haveI := of_presheaf_of_rings_extension.is_ring_hom (D_fs_basis R) (D_fs_standard_basis R)
  (structure_presheaf_on_basis R) structure_presheaf_on_basis_is_sheaf_on_basis (D_fs_standard_basis R).1;
exact @@is_ring_hom.comp _ _ _ _inst _ _ _

section

variables {A : Type u} [comm_ring A] {B : Type v} [comm_ring B] (f : A → B) [is_ring_hom f]

theorem comap_Zariski_mem_Dfs {U : opens (Spec A)} (HU : U ∈ D_fs A) : opens.comap (Zariski.induced.continuous f) U ∈ D_fs B :=
let ⟨g, hg⟩ := HU in ⟨f g, by rw hg; exact opens.ext (Zariski.induced.preimage_D f g)⟩

theorem of_mem_S {U : opens (Spec A)} {r : A} (hr : r ∈ S U) : f r ∈ S (opens.comap (Zariski.induced.continuous f) U) :=
λ q hqu hrq, hr hqu hrq

def Zariski.induced.presheaf_on_basis (U : opens (Spec A)) (HUB : U ∈ D_fs A)
  (s : (structure_presheaf_on_basis A).to_presheaf_on_basis HUB) :
  (structure_presheaf_on_basis B).to_presheaf_on_basis (comap_Zariski_mem_Dfs f HUB) :=
localization.lift' (localization.of ∘ f)
  (λ z, localization.to_units ⟨f z.1, of_mem_S f z.2⟩)
  (λ z, rfl)
  s

instance Zariski.induced.presheaf_on_basis.is_ring_hom (U : opens (Spec A)) (HUB : U ∈ D_fs A) :
  is_ring_hom (Zariski.induced.presheaf_on_basis f U HUB) :=
@@localization.lift'.is_ring_hom _ _ _ _ (@@is_ring_hom.comp _ _ _ _inst_4 _ _ localization.of.is_ring_hom) _ _

def Zariski.induced.stalk_on_basis_elem (p : Spec B)
  (g : stalk_on_basis.elem (structure_presheaf_on_basis A).to_presheaf_on_basis (Zariski.induced f p)) :
  stalk_on_basis.elem (structure_presheaf_on_basis B).to_presheaf_on_basis p :=
⟨opens.comap (Zariski.induced.continuous f) g.1, comap_Zariski_mem_Dfs f g.2, g.3,
Zariski.induced.presheaf_on_basis f g.1 g.2 g.4⟩

def Zariski.induced.stalk_on_basis (p : Spec B)
  (s : stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis
        (D_fs_standard_basis A) (structure_presheaf_on_basis A) (Zariski.induced f p)) :
  stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis
        (D_fs_standard_basis B) (structure_presheaf_on_basis B) p :=
quotient.lift_on s (λ g, ⟦Zariski.induced.stalk_on_basis_elem f p g⟧) $ λ g1 g2 ⟨U, HUB, HFPU, HU1, HU2, hg⟩, begin
  clear_, cases g1 with U1 HUB1 HFPU1 s1, cases g2 with U2 HUB2 HFPU2 s2,
  dsimp only at HU1 HU2 hg ⊢, revert hg,
  refine localization.induction_on s1 (λ r1 t1, _),
  refine localization.induction_on s2 (λ r2 t2, _),
  intros hg, rcases quotient.exact hg with ⟨t, hts, ht⟩,
  change (t1.1 * r2 - t2.1 * r1) * t = 0 at ht,
  refine quotient.sound ⟨opens.comap (Zariski.induced.continuous f) U, comap_Zariski_mem_Dfs f HUB, HFPU,
    opens.comap_mono _ _ _ HU1, opens.comap_mono _ _ _ HU2, quotient.sound ⟨f t, of_mem_S f hts, _⟩⟩,
  change ((1 * f t1.1) * (f r2 * 1) - (1 * f t2.1) * (f r1 * 1)) * f t = 0,
  rw [one_mul, mul_one, one_mul, mul_one, ← is_ring_hom.map_mul f, ← is_ring_hom.map_mul f,
      ← is_ring_hom.map_sub f, ← is_ring_hom.map_mul f, ht, is_ring_hom.map_zero f]
end

theorem Zariski.induced.stalk_on_basis.map_one (p : Spec B) :
  Zariski.induced.stalk_on_basis f p 1 = 1 :=
quotient.sound ⟨⊤, (D_fs_standard_basis B).1, trivial,
  show ⊤ ≤ opens.comap (Zariski.induced.continuous f) ⊤, by rw opens.comap_top; exact le_refl ⊤,
  show (⊤ : opens (Spec B)) ≤ ⊤, from le_refl ⊤,
  show localization.mk (f 1 * 1) ⟨1 * f 1, _⟩ = 1, by simp only [mul_one, one_mul, localization.mk_self]⟩

theorem Zariski.induced.stalk_on_basis.map_add (p : Spec B) (x y) :
  Zariski.induced.stalk_on_basis f p (x + y) = Zariski.induced.stalk_on_basis f p x + Zariski.induced.stalk_on_basis f p y :=
quotient.induction_on₂ x y $ λ p q, begin
  cases p with U HUB hfpU s, cases q with V HVB hfpV t,
  refine localization.induction_on s (λ r1 s1, _),
  refine localization.induction_on t (λ r2 s2, _),
  refine quotient.sound ⟨opens.comap (Zariski.induced.continuous f) (U ∩ V),
    comap_Zariski_mem_Dfs f ((D_fs_standard_basis A).2 HUB HVB),
    ⟨hfpU, hfpV⟩,
    set.subset.refl _,
    set.subset.refl _,
    _⟩,
  show localization.mk (f (s1.1 * r2 + s2.1 * r1) * 1) ⟨1 * f (s1.1 * s2.1), _⟩ =
    localization.mk ((1 * f s1.1) * (f r2 * 1) + (1 * f s2.1) * (f r1 * 1)) ⟨(1 * f s1.1) * (1 * f s2.1), _⟩,
  simp only [mul_one, one_mul, is_ring_hom.map_add f, is_ring_hom.map_mul f]
end

theorem Zariski.induced.stalk_on_basis.map_mul (p : Spec B) (x y) :
  Zariski.induced.stalk_on_basis f p (x * y) = Zariski.induced.stalk_on_basis f p x * Zariski.induced.stalk_on_basis f p y :=
quotient.induction_on₂ x y $ λ p q, begin
  cases p with U HUB hfpU s, cases q with V HVB hfpV t,
  refine localization.induction_on s (λ r1 s1, _),
  refine localization.induction_on t (λ r2 s2, _),
  refine quotient.sound ⟨opens.comap (Zariski.induced.continuous f) (U ∩ V),
    comap_Zariski_mem_Dfs f ((D_fs_standard_basis A).2 HUB HVB),
    ⟨hfpU, hfpV⟩,
    set.subset.refl _,
    set.subset.refl _,
    _⟩,
  show localization.mk (f (r1 * r2) * 1) ⟨1 * f (s1.1 * s2.1), _⟩ =
    localization.mk ((f r1 * 1) * (f r2 * 1)) ⟨(1 * f s1.1) * (1 * f s2.1), _⟩,
  simp only [mul_one, one_mul, is_ring_hom.map_mul f]
end

instance Spec.is_prime (p : Spec R) : ideal.is_prime p.1 := p.2

def to_stalk_on_basis {X : Type u} [topological_space X] {B : set (opens X)}
  {HB : opens.is_basis B} {Bstd : ⊤ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B} {p : X}
  (F : presheaf_of_rings_on_basis X HB) (U : opens X) (HUB : U ∈ B) (hpU : p ∈ U) (s : F.1 HUB) :
  stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis Bstd F p :=
⟦⟨U, HUB, hpU, s⟩⟧

instance to_stalk_on_basis.is_ring_hom {X : Type u} [topological_space X] {B : set (opens X)}
  {HB : opens.is_basis B} {Bstd : ⊤ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B} {p : X}
  (F : presheaf_of_rings_on_basis.{u v} X HB) (U : opens X) (HUB : U ∈ B) (hpU : p ∈ U) :
  is_ring_hom (@to_stalk_on_basis _ _ _ _ Bstd _ F U HUB hpU) :=
{ map_one := quotient.sound ⟨U, HUB, hpU, set.subset.refl U.1, set.subset_univ U.1,
    (is_ring_hom.map_one (F.to_presheaf_on_basis.res _ HUB _)).trans (is_ring_hom.map_one (F.to_presheaf_on_basis.res _ HUB _)).symm⟩,
  map_mul := λ x y, quotient.sound ⟨U, HUB, hpU, set.subset.refl U.1, set.subset_inter (set.subset.refl U.1) (set.subset.refl U.1),
    by dsimp only; rw [is_ring_hom.map_mul (F.1.res _ _ _), is_ring_hom.map_mul (F.1.res _ _ _),
        ← presheaf_on_basis.Hcomp', ← presheaf_on_basis.Hcomp']; apply_instance⟩,
  map_add := λ x y, quotient.sound ⟨U, HUB, hpU, set.subset.refl U.1, set.subset_inter (set.subset.refl U.1) (set.subset.refl U.1),
    by dsimp only; rw [is_ring_hom.map_add (F.1.res _ _ _), is_ring_hom.map_add (F.1.res _ _ _),
        ← presheaf_on_basis.Hcomp', ← presheaf_on_basis.Hcomp']; apply_instance⟩ }

def stalk_on_basis_of (p : Spec R) (r : R) :
  stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis
    (D_fs_standard_basis R) (structure_presheaf_on_basis R) p :=
to_stalk_on_basis _ ⊤ (D_fs_standard_basis R).1 trivial (localization.of r)

instance stalk_on_basis_of.is_ring_hom (p : Spec R) : is_ring_hom (stalk_on_basis_of p) :=
is_ring_hom.comp _ _

def stalk_on_basis_of_localization (p : Spec R) (x : localization.at_prime p.1) :
  stalk_of_rings_on_standard_basis.stalk_of_rings_on_standard_basis
    (D_fs_standard_basis R) (structure_presheaf_on_basis R) p :=
localization.lift' (stalk_on_basis_of p)
  (λ r : -(p.1 : set R), units.map (to_stalk_on_basis _ (Spec.DO R r.1) ⟨r.1, rfl⟩ r.2) $
    localization.to_units ⟨r.1, set.subset.refl _⟩)
  (λ r, quotient.sound ⟨Spec.DO R r.1, ⟨r.1, rfl⟩, r.2, set.subset.refl _, set.subset_univ _, rfl⟩)
  x

instance stalk_on_basis_of_localization.is_ring_hom (p : Spec R) :
  is_ring_hom (stalk_on_basis_of_localization p) :=
localization.lift'.is_ring_hom _ _ _

theorem stalk_on_basis_of_localization.bijective (p : Spec R) :
  function.bijective (stalk_on_basis_of_localization p) :=
begin
  split,
  { intros x y,
    refine localization.induction_on x (λ r1 s1, _),
    refine localization.induction_on y (λ r2 s2, _),
    rintros h, replace h := quotient.exact h, rcases h with ⟨U, HUB, hpU, HU1, HU2, h⟩,
    dsimp only [opens.inter_eq] at HU1 HU2,
    replace h := quotient.exact h, rcases h with ⟨t, hts, ht⟩,
    change ((1 * s1.1) * (r2 * 1) - (1 * s2.1) * (r1 * 1)) * t = 0 at ht,
    rw lattice.top_inf_eq at HU1 HU2, simp only [mul_one, one_mul] at ht,
    refine quotient.sound ⟨t, hts hpU, ht⟩ },
  { intros s,
    refine quotient.induction_on s (λ g, _),
    rcases g with ⟨U, HUB, hpU, g⟩,
    refine localization.induction_on g (λ r s, _),
    refine ⟨localization.mk r ⟨s, s.2 hpU⟩, quotient.sound ⟨U, HUB, hpU, set.subset_inter (set.subset_univ _) s.2, set.subset.refl _, _⟩⟩,
    change localization.mk (r * 1) ⟨1 * s.1, _⟩ = localization.mk r ⟨s.1, _⟩,
    simp only [mul_one, one_mul], }
end

theorem stalk_on_basis_of_localization.unit (p : Spec R) (x) :
  is_unit (stalk_on_basis_of_localization p x) ↔ is_unit x :=
begin
  split,
  { rw [is_unit_iff_exists_inv, is_unit_iff_exists_inv],
    rintros ⟨y, hxy⟩, rcases (stalk_on_basis_of_localization.bijective p).2 y with ⟨y, rfl⟩,
    rw [← is_ring_hom.map_mul (stalk_on_basis_of_localization p), ← is_ring_hom.map_one (stalk_on_basis_of_localization p)] at hxy,
    exact ⟨y, (stalk_on_basis_of_localization.bijective p).1 hxy⟩ },
  { exact is_unit.map _ }
end

def Zariski.induced.stalk_on_basis.algebraic (p : Spec B)
  (s : localization.at_prime (Zariski.induced f p).1) : localization.at_prime p.1 :=
localization.lift' (localization.of ∘ f)
  (λ r : -((Zariski.induced f p).1 : set A), localization.to_units ⟨f r.1, r.2⟩)
  (λ s, rfl)
  s

theorem Zariski.induced.stalk_on_basis.stalk_on_basis_of_localization (p : Spec B) (s) :
  Zariski.induced.stalk_on_basis f p (stalk_on_basis_of_localization (Zariski.induced f p) s) =
  stalk_on_basis_of_localization p (Zariski.induced.stalk_on_basis.algebraic f p s) :=
localization.induction_on s $ λ r s, quotient.sound
⟨opens.comap (Zariski.induced.continuous f) (Spec.DO A s.1),
comap_Zariski_mem_Dfs f ⟨s.1, rfl⟩, s.2, set.subset_inter (set.subset_univ _) (set.subset.refl _),
show opens.comap (Zariski.induced.continuous f) (Spec.DO A s.1) ≤ ⊤ ⊓ Spec.DO B (1 * f s.1), by rw [one_mul, lattice.top_inf_eq]; exact le_refl _,
show localization.mk (f (r * 1) * 1) ⟨1 * f (1 * s.1), _⟩ = localization.mk (f r * 1 * 1) ⟨1 * (1 * f s.1), _⟩, by simp only [one_mul, mul_one]⟩

theorem Zariski.induced.stalk_on_basis.algebraic.hlocal (p : Spec B) (s)
  (H : is_unit (Zariski.induced.stalk_on_basis.algebraic f p s)) : is_unit s :=
begin
  refine localization.induction_on s (λ r s, _) H,
  change is_unit (localization.mk (f r * 1) ⟨1 * f s.1, _⟩) → is_unit (localization.mk r s),
  rw [is_unit_localization_mk, is_unit_localization_mk],
  rintros ⟨t, hr⟩, refine ⟨1, λ h, hr _⟩, rw mul_one at h ⊢, exact p.1.mul_mem_right h
end

theorem Zariski.induced.stalk_on_basis.hlocal (p : Spec B) (x)
  (H : is_unit (Zariski.induced.stalk_on_basis f p x)) : is_unit x :=
begin
  rcases (stalk_on_basis_of_localization.bijective $ Zariski.induced f p).2 x with ⟨s, rfl⟩,
  rw Zariski.induced.stalk_on_basis.stalk_on_basis_of_localization at H,
  rw stalk_on_basis_of_localization.unit at H ⊢,
  exact Zariski.induced.stalk_on_basis.algebraic.hlocal f p s H
end

set_option class.instance_max_depth 10
def Zariski.induced.locally_ringed_space {A : Type u} [comm_ring A] {B : Type v} [comm_ring B] (f : A → B) [is_ring_hom f] :
  locally_ringed_space.morphism (Spec.locally_ringed_space B) (Spec.locally_ringed_space A) :=
{ f := Zariski.induced f,
  Hf := Zariski.induced.continuous f,
  fO :=
  { map := λ U s, ⟨λ p hp, Zariski.induced.stalk_on_basis f p $ s.1 (Zariski.induced f p) hp,
      λ p hp, let ⟨V, HVB, hfpV, σ, hσ⟩ := s.2 (Zariski.induced f p) hp in
      ⟨opens.comap (Zariski.induced.continuous f) V, comap_Zariski_mem_Dfs f HVB, hfpV, Zariski.induced.presheaf_on_basis f V HVB σ,
      λ q hqUV, funext $ λ hq, by rw [hσ (Zariski.induced f q) hqUV]; refl⟩⟩,
    commutes := λ U V HVU, rfl },
  hom := λ U,
  { map_one := subtype.eq $ by funext p hp; apply Zariski.induced.stalk_on_basis.map_one,
    map_mul := λ x y, subtype.eq $ by funext p hp; simp only [Fext_mul.eq]; apply Zariski.induced.stalk_on_basis.map_mul,
    map_add := λ x y, subtype.eq $ by funext p hp; simp only [Fext_add.eq]; apply Zariski.induced.stalk_on_basis.map_add },
  hlocal := begin
    rintros p s, refine quotient.induction_on s (λ g hg, _), cases g with U hfpU σ,
    change is_unit (to_stalk (Spec.locally_ringed_space B).O.F p (opens.comap (Zariski.induced.continuous f) U) hfpU _) at hg,
    change is_unit (to_stalk (Spec.locally_ringed_space A).O.F (Zariski.induced f p) U hfpU σ),
    erw is_unit_to_stalk_on_basis at hg ⊢,
    exact Zariski.induced.stalk_on_basis.hlocal f p _ hg,
  end  }

end

section res_open

variables {X : Type u} [topological_space X]

def topological_space.opens.map_subtype_val {U : opens X} (V : opens U) : opens X :=
⟨subtype.val '' V.1, let ⟨W, HW, HWV⟩ := V.2 in by rw [← HWV, subtype.image_preimage_val]; exact is_open_inter HW U.2⟩

theorem map_subtype_val_inf {U : opens X} (V W : opens U) :
  (V ⊓ W).map_subtype_val = V.map_subtype_val ⊓ W.map_subtype_val :=
opens.ext $ eq.symm $ set.image_inter subtype.val_injective

def presheaf.res_open (F : presheaf X) (U : opens X) : presheaf U :=
{ F := λ V, F V.map_subtype_val,
  res := λ V W HWV, F.res _ _ (set.image_subset _ HWV),
  Hid := λ V, F.Hid _,
  Hcomp := λ V W S HSW HWV, F.Hcomp _ _ _ _ _ }

def covering.map_subtype_val {U : opens X} {V : opens U} (OC : covering V) : covering V.map_subtype_val :=
{ γ := OC.γ,
  Uis := λ i, (OC.Uis i).map_subtype_val,
  Hcov := opens.ext $ set.subset.antisymm
    (set.sUnion_subset $ λ t ⟨u, ⟨i, hiu⟩, hut⟩, hut ▸ hiu ▸ set.image_subset _ (subset_covering i))
    (λ v ⟨x, hxV, hxv⟩, let ⟨t, ⟨_, ⟨i, rfl⟩, rfl⟩, hxi⟩ := set.mem_sUnion.1 (((set.ext_iff _ _).1 (congr_arg subtype.val OC.Hcov) x).2 hxV) in
      hxv ▸ set.mem_sUnion.2 ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, x, hxi, rfl⟩) }

def presheaf_of_rings.res_open (F : presheaf_of_rings X) (U : opens X) : presheaf_of_rings U :=
{ Fring := λ V, F.Fring _,
  res_is_ring_hom := λ V W HWV, F.res_is_ring_hom _ _ _,
  .. F.1.res_open U }

theorem locality.res_open {F : presheaf X} (HF : locality F) (U : opens X) : locality (F.res_open U) :=
λ V OC s t H, HF OC.map_subtype_val s t H

theorem gluing.res_open {F : presheaf X} (HF : gluing F) (U : opens X) : gluing (F.res_open U) :=
λ V OC s H, HF OC.map_subtype_val s $ λ j k,
calc  F.res (OC.Uis j).map_subtype_val ((OC.Uis j).map_subtype_val ⊓ (OC.Uis k).map_subtype_val) _ (s j)
    = F.res (OC.Uis j ⊓ OC.Uis k).map_subtype_val ((OC.Uis j).map_subtype_val ⊓ (OC.Uis k).map_subtype_val)
        (by rw [map_subtype_val_inf]; refl)
        (F.res (OC.Uis j).map_subtype_val (OC.Uis j ⊓ OC.Uis k).map_subtype_val
          (set.image_subset _ $ set.inter_subset_left _ _)
          (s j)) : by rw ← presheaf.Hcomp'; refl
... = F.res (OC.Uis j ⊓ OC.Uis k).map_subtype_val ((OC.Uis j).map_subtype_val ⊓ (OC.Uis k).map_subtype_val)
        (by rw [map_subtype_val_inf]; refl)
        (F.res (OC.Uis k).map_subtype_val (OC.Uis j ⊓ OC.Uis k).map_subtype_val
          (set.image_subset _ $ set.inter_subset_right _ _)
          (s k)) : congr_arg _ (H j k)
... = F.res (OC.Uis k).map_subtype_val ((OC.Uis j).map_subtype_val ⊓ (OC.Uis k).map_subtype_val) _ (s k) : by rw ← presheaf.Hcomp'; refl

def sheaf.res_open (O : sheaf X) (U : opens X) : sheaf U :=
{ F := O.F.res_open U,
  locality := λ V, O.locality.res_open U,
  gluing := λ V, O.gluing.res_open U, }

def sheaf_of_rings.to_sheaf (O : sheaf_of_rings X) : sheaf X :=
{ F := O.F.to_presheaf, .. O }

def sheaf_of_rings.res_open (O : sheaf_of_rings X) (U : opens X) : sheaf_of_rings U :=
{ F := O.F.res_open U, .. O.to_sheaf.res_open U }

def of_stalk_of_rings_res_open (F : presheaf_of_rings X) (U : opens X) (x : U)
  (s : stalk_of_rings (F.res_open U) x) : stalk_of_rings F x.1 :=
quotient.lift_on s (λ g, to_stalk F x.1 g.1.map_subtype_val (set.mem_image_of_mem _ g.2) g.3) $
λ g1 g2 ⟨V, hxV, HV1, HV2, hx⟩, quotient.sound ⟨V.map_subtype_val, set.mem_image_of_mem _ hxV,
  set.image_subset _ HV1, set.image_subset _ HV2, hx⟩

theorem of_stalk_of_rings_res_open_to_stalk (F : presheaf_of_rings X) (U : opens X) (x : U)
  (V : opens U) (HV : x ∈ V) (s) :
  of_stalk_of_rings_res_open F U x (to_stalk (F.res_open U) x V HV s) =
  to_stalk F x.1 V.map_subtype_val (set.mem_image_of_mem _ HV) s :=
rfl

@[elab_as_eliminator] theorem stalk_of_rings.induction_on₂ {F : presheaf_of_rings.{u v} X} {p : X}
  {C : stalk_of_rings F p → stalk_of_rings F p → Prop} (s t : stalk_of_rings F p)
  (H : ∀ U HU x y, C (to_stalk F p U HU x) (to_stalk F p U HU y)) : C s t :=
quotient.induction_on₂ s t $ λ ⟨U, HU, x⟩ ⟨V, HV, y⟩,
show C (to_stalk F p U HU x) (to_stalk F p V HV y),
from to_stalk_res F p U (U ⊓ V) HU ⟨HU, HV⟩ (set.inter_subset_left _ _) x ▸
to_stalk_res F p V (U ⊓ V) HV ⟨HU, HV⟩ (set.inter_subset_right _ _) y ▸
H (U ⊓ V) ⟨HU, HV⟩ _ _

@[elab_as_eliminator] theorem stalk_of_rings.induction_on {F : presheaf_of_rings.{u v} X} {p : X}
  {C : stalk_of_rings F p → Prop} (s : stalk_of_rings F p)
  (H : ∀ U HU x, C (to_stalk F p U HU x)) : C s :=
quotient.induction_on s $ λ ⟨U, HU, x⟩, H U HU x

instance of_stalk_of_rings_res_open.is_ring_hom (F : presheaf_of_rings.{u v} X) (U : opens X) (x : U) :
  is_ring_hom (of_stalk_of_rings_res_open F U x) :=
{ map_one := show to_stalk _ _ _ _ 1 = 1, from is_ring_hom.map_one (to_stalk _ _ _ _),
  map_mul := λ s t, stalk_of_rings.induction_on₂ s t $ λ V HV p q,
    by rw [← is_ring_hom.map_mul (to_stalk (presheaf_of_rings.res_open F U) x V HV), of_stalk_of_rings_res_open_to_stalk,
        of_stalk_of_rings_res_open_to_stalk, of_stalk_of_rings_res_open_to_stalk,
        is_ring_hom.map_mul (to_stalk F x.1 V.map_subtype_val (set.mem_image_of_mem _ HV))],
  map_add := λ s t, stalk_of_rings.induction_on₂ s t $ λ V HV p q,
    by rw [← is_ring_hom.map_add (to_stalk (presheaf_of_rings.res_open F U) x V HV), of_stalk_of_rings_res_open_to_stalk,
        of_stalk_of_rings_res_open_to_stalk, of_stalk_of_rings_res_open_to_stalk,
        is_ring_hom.map_add (to_stalk F x.1 V.map_subtype_val (set.mem_image_of_mem _ HV))] }

def to_stalk_of_rings_res_open (F : presheaf_of_rings X) (U : opens X) (x : U)
  (s : stalk_of_rings F x.1) : stalk_of_rings (F.res_open U) x :=
quotient.lift_on s (λ g, to_stalk (F.res_open U) x (opens.comap continuous_subtype_val g.1) g.2 $
  F.1.res _ _ (set.image_preimage_subset _ _) g.3) $
λ g1 g2 ⟨V, hxV, HV1, HV2, hv⟩, quotient.sound ⟨opens.comap continuous_subtype_val V,
  hxV, opens.comap_mono _ _ _ HV1, opens.comap_mono _ _ _ HV2,
  have _ := congr_arg (F.res V (opens.comap continuous_subtype_val V).map_subtype_val (set.image_preimage_subset (subtype.val : U → X) _)) hv,
  by dsimp only [presheaf_of_rings.res_open, presheaf.res_open];
  rw [← presheaf.Hcomp', ← presheaf.Hcomp'] at this ⊢; exact this⟩

theorem to_stalk_of_rings_res_open_to_stalk (F : presheaf_of_rings X) (U : opens X) (x : U)
  (V : opens X) (HV : x.1 ∈ V) (s) :
  to_stalk_of_rings_res_open F U x (to_stalk F x.1 V HV s) =
  to_stalk (F.res_open U) x (opens.comap continuous_subtype_val V) HV (F.1.res _ _ (set.image_preimage_subset _ _) s) :=
rfl

def presheaf_of_rings.res_open.stalk_of_rings (F : presheaf_of_rings X) (U : opens X) (x : U) :
  stalk_of_rings (F.res_open U) x ≃r stalk_of_rings F x.1 :=
{ to_fun := of_stalk_of_rings_res_open F U x,
  inv_fun := to_stalk_of_rings_res_open F U x,
  left_inv := λ s, stalk_of_rings.induction_on s $ λ V HV s,
    by rw [of_stalk_of_rings_res_open_to_stalk, to_stalk_of_rings_res_open_to_stalk]; apply to_stalk_res;
      show subtype.val ⁻¹' (subtype.val '' V.1) ⊆ V.1; rw [set.preimage_image_eq _ subtype.val_injective],
  right_inv := λ s, stalk_of_rings.induction_on s $ λ V HV s,
    by rw [to_stalk_of_rings_res_open_to_stalk, of_stalk_of_rings_res_open_to_stalk]; apply to_stalk_res,
  hom := of_stalk_of_rings_res_open.is_ring_hom F U x }

theorem is_local_ring_iff : is_local_ring R ↔ ((0:R) ≠ 1 ∧ ∀ x y : R, is_unit (x + y) → is_unit x ∨ is_unit y) :=
⟨λ hr, ⟨hr.zero_ne_one, λ x y hxy, classical.or_iff_not_imp_left.2 $ λ hnx, classical.by_contradiction $ λ hny,
  absurd hxy $ (nonunits_ideal hr).add_mem hnx hny⟩,
λ hr, local_of_nonunits_ideal hr.1 $ λ x y hx hy hxy, or.cases_on (hr.2 x y hxy) hx hy⟩

theorem is_unit_congr {A : Type u} [comm_ring A] {B : Type v} [comm_ring B] (e : A ≃r B) (x : A) :
  is_unit (e.to_equiv x) ↔ is_unit x :=
⟨λ hx, e.left_inv x ▸ @@is_unit.map _ _ e.symm.to_equiv _ hx, is_unit.map _⟩

theorem is_local_ring_congr {A : Type u} [comm_ring A] {B : Type v} [comm_ring B] (e : A ≃r B) :
  is_local_ring A ↔ is_local_ring B :=
by rw [is_local_ring_iff, is_local_ring_iff]; exact
⟨λ ⟨h1, h2⟩, ⟨is_ring_hom.map_zero e.to_equiv ▸ is_ring_hom.map_one e.to_equiv ▸ λ h3, h1 (e.to_equiv.bijective.1 h3), λ x y,
  let ⟨r, hr⟩ := e.to_equiv.bijective.2 x, ⟨s, hs⟩ := e.to_equiv.bijective.2 y in
  by rw [← hr, ← hs, ← is_ring_hom.map_add e.to_equiv, is_unit_congr, is_unit_congr, is_unit_congr]; apply h2⟩,
λ ⟨h1, h2⟩, ⟨is_ring_hom.map_zero e.symm.to_equiv ▸ is_ring_hom.map_one e.symm.to_equiv ▸ λ h3, h1 (e.symm.to_equiv.bijective.1 h3), λ x y,
  let ⟨r, hr⟩ := e.symm.to_equiv.bijective.2 x, ⟨s, hs⟩ := e.symm.to_equiv.bijective.2 y in
  by rw [← hr, ← hs, ← is_ring_hom.map_add e.symm.to_equiv, is_unit_congr, is_unit_congr, is_unit_congr]; apply h2⟩⟩

def locally_ringed_space.res_open (OX : locally_ringed_space X) (U : opens X) : locally_ringed_space U :=
{ O := OX.O.res_open U,
  Hstalks := λ x, (is_local_ring_congr $ presheaf_of_rings.res_open.stalk_of_rings OX.O.F U x).2 (OX.Hstalks x.1) }

-- def covering.univ.res_open (cov : covering.univ X) (U : opens X) : covering.univ U :=
-- { γ := cov.γ,
--   Uis := λ i, opens.comap continuous_subtype_val (cov.Uis i),
--   Hcov := opens.ext $ set.eq_univ_of_forall $ λ x,
--     let ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, hxi⟩ := set.mem_sUnion.1 (((set.ext_iff _ _).1 (congr_arg subtype.val cov.Hcov) x.1).2 trivial) in
--     set.mem_sUnion.2 ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, hxi⟩ }

-- def scheme.res_open (O : scheme X) (U : opens X) : scheme U :=
-- { carrier := O.carrier.res_open U,
--   cov := O.cov.res_open U }

end res_open

def Zariski.coinduced (x : R) (p : Spec.DO R x) : Spec (localization.away x) :=
⟨p.1.1.map localization.of, localization.prime_map_away x p.1.1 p.1.2 p.2⟩

theorem Zariski.coinduced.continuous (x : R) : continuous (Zariski.coinduced x) :=
λ U HU, ⟨Zariski.induced localization.of '' U, open_Zariski_induced_localization_of x U HU,
set.ext $ λ p, ⟨λ ⟨q, hqU, hqp⟩,
  have q = (⟨p.1.1.map localization.of, localization.prime_map_away x p.1.1 p.1.2 p.2⟩ : Spec (localization.away x)),
  from subtype.eq $ by dsimp only; rw ← hqp; dsimp only [Zariski.induced]; erw localization.map_comap,
  show (⟨p.1.1.map localization.of, localization.prime_map_away x p.1.1 p.1.2 p.2⟩ : Spec (localization.away x)) ∈ U,
  from this ▸ hqU,
λ hp, ⟨_, hp, subtype.eq $ by dsimp only [Zariski.coinduced]; rw localization.comap_map_away x p.1.1 p.1.2 p.2⟩⟩⟩

theorem of_mem_map_subtype_val {x : R} {U : opens (Spec.DO R x)} {p : Spec R}
  (hp : p ∈ U.map_subtype_val) : x ∉ p.1 :=
let ⟨q, hqU, hqp⟩ := hp in hqp ▸ q.2

theorem mem_of_mem_map_subtype_val {x : R} {U : opens (Spec.DO R x)} {p : Spec R}
  (hp : p ∈ U.map_subtype_val) : (⟨p, of_mem_map_subtype_val hp⟩ : Spec.DO R x) ∈ U :=
let ⟨q, hqU, hqp⟩ := hp in have q = ⟨p, of_mem_map_subtype_val hp⟩, from subtype.eq hqp, this ▸ hqU

theorem Spec.D'_eq_D (x : R) : Spec.D' x = Spec.D {x} :=
set.ext $ λ r, not_congr $ iff.symm $ set.singleton_subset_iff

def Zariski.map_away {x : R} (U : opens (Spec (localization.away x))) : opens (Spec R) :=
opens.map (λ U, open_Zariski_induced_localization_of x U.1 U.2) U

theorem localization.map_DO {x : R} (r : R) (s : powers x) :
  Zariski.map_away (Spec.DO (localization.away x) (localization.mk r s)) = Spec.DO R (r * x) :=
opens.ext $ show Zariski.induced localization.of '' Spec.D' (localization.mk r s) = Spec.D' (r * x),
by rw [Spec.D'_eq_D, Zariski_induced_localization_of_D, range_Zariski_induced_localization_away_of, Spec.D'.product_eq_inter]; exact
set.ext (λ p, ⟨λ ⟨hp1, hp2⟩, ⟨λ hrp, hp1 $ λ r1 ⟨s1, hs1⟩,
    localization.comap_map_away x p.1 p.2 hp2 ▸ (localization.mk_mem_iff _ _ _ s1).1
    ((set.mem_singleton_iff.1 hs1).symm ▸ (localization.mk_mem_iff _ _ _ s).2 (ideal.mem_map_of_mem hrp)),
  hp2⟩,
λ ⟨hp1, hp2⟩, ⟨λ hp3, hp1 $ hp3 ⟨s, set.mem_singleton _⟩, hp2⟩⟩)

theorem localization.map_away_mem_D_fs {x : R} {U : opens (Spec (localization.away x))}
  (HU : U ∈ D_fs (localization.away x)) :
  Zariski.map_away U ∈ D_fs R :=
let ⟨y, hy⟩ := HU in localization.induction_on y (λ r s hrs, ⟨r * x, hrs.symm ▸ localization.map_DO r s⟩) hy

theorem powers_subset_S_map_away {x : R} {U : opens (Spec (localization.away x))} :
  powers x ⊆ S (Zariski.map_away U) :=
λ r hr, set.image_subset_iff.2 $ λ p hpU hrp, p.2.1 $ p.1.eq_top_of_is_unit_mem hrp ⟨localization.to_units ⟨r, hr⟩, rfl⟩

theorem mul_comm4 {α : Type u} [comm_semigroup α] (a b c d : α) :
  (a * b) * (c * d) = (a * c) * (b * d) :=
by rw [mul_assoc, mul_assoc, mul_left_comm b c d]

theorem mul_sub_mul {α : Type u} [ring α] (a b c d : α) :
  a * b - c * d = (a - c) * (b - d) + c * (b - d) + (a - c) * d :=
by rw [sub_mul, mul_sub, mul_sub, sub_mul, ← sub_add, ← add_sub_assoc, ← add_sub_assoc]; simp [add_right_comm]

theorem mem_S_map_away_of_mem_S {x : R} {p : R × powers x} {U : opens (Spec (localization.away x))}
  (hp : ⟦p⟧ ∈ S U) : p.1 ∈ S (Zariski.map_away U) :=
set.image_subset_iff.2 $ λ q hqU hpq, hp hqU $ prod.cases_on p (λ p1 p2, (localization.mk_mem_iff _ _ _ _).2) hpq

attribute [elab_as_eliminator] quotient.hrec_on₂
def Zariski.coinduced.presheaf_on_basis {x : R}
  (U : opens (Spec (localization.away x))) (HUB : U ∈ D_fs (localization.away x))
  (g : (structure_presheaf_on_basis (localization.away x)).to_presheaf_on_basis HUB) :
  (structure_presheaf_on_basis R).to_presheaf_on_basis (localization.map_away_mem_D_fs HUB) :=
quotient.lift_on g (λ r : localization.away x × S U, (quotient.hrec_on₂ r.1 r.2.1
  (λ s t ht, localization.mk (s.1 * t.2.1) ⟨s.2.1 * t.1,
    is_submonoid.mul_mem (powers_subset_S_map_away s.2.2) (mem_S_map_away_of_mem_S ht)⟩)
  (λ s1 s2 s3 s4 ⟨t1, hts1, ht1⟩ ⟨t2, hts2, ht2⟩, function.hfunext
    (congr_arg _ $ quotient.sound ⟨t2, hts2, ht2⟩) $ λ _ _ _, heq_of_eq $
    quotient.sound $ ⟨t1 * t2,
      powers_subset_S_map_away $ is_submonoid.mul_mem hts1 hts2,
      show (((s1.2 : R) * s2.1) * (s3.1 * s4.2) - (s3.2 * s4.1) * (s1.1 * s2.2)) * (t1 * t2) = 0,
      by rw [mul_comm4, mul_comm4 (s3.2 : R), mul_sub_mul, add_mul, add_mul, mul_comm4, ht1, zero_mul, zero_add,
          mul_comm4, ← neg_sub, neg_mul_eq_neg_mul_symm, mul_comm s4.1, mul_comm s2.1, ht2, neg_zero, mul_zero, zero_add,
          mul_comm4, ht1, zero_mul]⟩)
  r.2.2 :
  (structure_presheaf_on_basis R).to_presheaf_on_basis (localization.map_away_mem_D_fs HUB))) $
λ ⟨s1, s2, hs2⟩ ⟨s3, s4, hs4⟩, localization.induction_on s1 $ λ r1 d1,
localization.induction_on s2 (λ r2 d2 hrd2,
localization.induction_on s3 $ λ r3 d3,
localization.induction_on s4 (λ r4 d4 hrd4 ⟨t, hts, ht⟩,
localization.induction_on t (λ rt dt hrdts hrdt, begin
  show localization.mk (r1 * d2.1) ⟨d1.1 * r2, _⟩ = localization.mk (r3 * d4.1) ⟨d3.1 * r4, _⟩,
  change (localization.mk r2 d2 * localization.mk r3 d3 - localization.mk r4 d4 * localization.mk r1 d1) * localization.mk rt dt = 0 at hrdt,
  rw [localization.mk_mul_mk, localization.mk_mul_mk, sub_mul, sub_eq_zero, localization.mk_mul_mk, localization.mk_mul_mk] at hrdt,
  rcases quotient.exact hrdt.symm with ⟨t1, hts1, ht1⟩,
  refine quotient.sound ⟨dt.1 * rt * t1,
    is_submonoid.mul_mem (is_submonoid.mul_mem (powers_subset_S_map_away dt.2) (mem_S_map_away_of_mem_S hrdts)) (powers_subset_S_map_away hts1), _⟩,
  change ((d4.1 * d1.1 * dt.1) * (r2 * r3 * rt) - (d2.1 * d3.1 * dt.1) * (r4 * r1 * rt)) * t1 = 0 at ht1,
  change ((d1.1 * r2) * (r3 * d4.1) - (d3.1 * r4) * (r1 * d2.1)) * (dt.1 * rt * t1) = 0,
  rw [← ht1, sub_mul, sub_mul], simp only [mul_assoc, mul_left_comm]
end) hts ht) hs4) hs2

theorem Zariski.coinduced.presheaf_on_basis_res {x : R}
  (U : opens (Spec (localization.away x))) (HUB : U ∈ D_fs (localization.away x))
  (V : opens (Spec (localization.away x))) (HVB : V ∈ D_fs (localization.away x)) (HVU : V ⊆ U)
  (g : (structure_presheaf_on_basis (localization.away x)).to_presheaf_on_basis HUB) :
  Zariski.coinduced.presheaf_on_basis V HVB (presheaf_on_basis.res _ HUB HVB HVU g) =
  presheaf_on_basis.res _ (localization.map_away_mem_D_fs HUB) (localization.map_away_mem_D_fs HVB)
    (opens.map_mono _ _ _ HVU)
    (Zariski.coinduced.presheaf_on_basis U HUB g) :=
localization.induction_on g $ λ r ⟨s, hs⟩,
localization.induction_on r $ λ r1 r2, localization.induction_on s (λ s1 s2 hs, rfl) hs

def Zariski.coinduced.stalk_on_basis.elem {x : R} (p : Spec R) (V : opens (Spec (localization.away x)))
  (hp : p ∈ (opens.comap (Zariski.coinduced.continuous x) V).map_subtype_val)
  (g : stalk_on_basis.elem ((structure_presheaf_on_basis (localization.away x)).to_presheaf_on_basis)
    (Zariski.coinduced x ⟨p, of_mem_map_subtype_val hp⟩)) :
  stalk_on_basis.elem ((structure_presheaf_on_basis R).to_presheaf_on_basis) p :=
⟨Zariski.map_away g.1, localization.map_away_mem_D_fs g.2,
⟨Zariski.coinduced x ⟨p, of_mem_map_subtype_val hp⟩, g.3, subtype.eq $ localization.comap_map_away x p.1 p.2 (of_mem_map_subtype_val hp)⟩,
Zariski.coinduced.presheaf_on_basis g.1 g.2 g.4⟩

def Zariski.coinduced.stalk_on_basis {x : R} (p : Spec R) (U : opens (Spec (localization.away x)))
  (hp : p ∈ (opens.comap (Zariski.coinduced.continuous x) U).map_subtype_val)
  (s : stalk_on_basis ((structure_presheaf_on_basis (localization.away x)).to_presheaf_on_basis)
    (Zariski.coinduced x ⟨p, of_mem_map_subtype_val hp⟩)) :
  stalk_on_basis ((structure_presheaf_on_basis R).to_presheaf_on_basis) p :=
quotient.lift_on s (λ g, ⟦Zariski.coinduced.stalk_on_basis.elem p U hp g⟧) $
λ ⟨V1, HVB1, hpV1, s1⟩ ⟨V2, HVB2, hpV2, s2⟩ ⟨V, HVB, hpV, HV1, HV2, HV⟩,
quotient.sound ⟨Zariski.map_away V, localization.map_away_mem_D_fs HVB,
⟨Zariski.coinduced x ⟨p, of_mem_map_subtype_val hp⟩, hpV, subtype.eq $ localization.comap_map_away _ _ p.2 (of_mem_map_subtype_val hp)⟩,
set.image_subset _ HV1, set.image_subset _ HV2,
by dsimp only [Zariski.coinduced.stalk_on_basis.elem] at HV ⊢;
erw [← Zariski.coinduced.presheaf_on_basis_res _ _ _ _ HV1, ← Zariski.coinduced.presheaf_on_basis_res _ _ _ _ HV2, HV]⟩

def res_D_fs (x : R) : locally_ringed_space.morphism
  ((Spec.locally_ringed_space R).res_open (Spec.DO R x))
  (Spec.locally_ringed_space (localization.away x)) :=
{ f := Zariski.coinduced x,
  Hf := Zariski.coinduced.continuous x,
  fO :=
  { map := λ U s, ⟨λ p hp, Zariski.coinduced.stalk_on_basis p U hp $
      s.1 (Zariski.coinduced x ⟨p, of_mem_map_subtype_val hp⟩) (mem_of_mem_map_subtype_val hp),
      λ p hp, let ⟨V, HVB, hxV, σ, hσ⟩ := s.2 (Zariski.coinduced x ⟨p, of_mem_map_subtype_val hp⟩) (mem_of_mem_map_subtype_val hp) in
      ⟨Zariski.map_away V, localization.map_away_mem_D_fs HVB,
        ⟨_, hxV, subtype.eq $ localization.comap_map_away _ _ p.2 (of_mem_map_subtype_val hp)⟩,
        Zariski.coinduced.presheaf_on_basis V HVB σ,
        λ q hq1, funext $ λ hq2, by rw hσ; sorry⟩⟩,
    commutes := sorry },
  hom := sorry,
  hlocal := sorry }

#exit
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

def sorope1 : sheaf_of_rings_on_opens.morphism
  (sheaf_of_rings_on_opens.res_subset (soropl R) (opl R ⊓ opr R) lattice.inf_le_left)
  (sheaf_of_rings_on_opens.res_subset (soropr R) (opl R ⊓ opr R) lattice.inf_le_right) :=
{ η :=
  { map := λ V HV, _ ∘
      (Zariski.induced.locally_ringed_space (inr_aux R)).1.3.1 (opens.comap (continuous_inl R) V),
    commutes := by skip },
  hom := by skip }
#check (Zariski.induced.locally_ringed_space (localization.of : _ → localization.away (polynomial.X : polynomial R))).1.3.1
def sorope : sheaf_of_rings_on_opens.equiv
  (sheaf_of_rings_on_opens.res_subset (soropl R) (opl R ⊓ opr R) lattice.inf_le_left)
  (sheaf_of_rings_on_opens.res_subset (soropr R) (opl R ⊓ opr R) lattice.inf_le_right) :=
sorry

def sor : sheaf_of_rings (projective_line R) :=
sheaf_of_rings_on_opens.sheaf_glue (projective_line.covering R).Uis
  (λ b, pbool.rec_on b (soropl R) (soropr R))
  (λ b₁ b₂, sorry)

end projective_line
