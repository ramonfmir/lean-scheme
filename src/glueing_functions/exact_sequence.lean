import localization_UMP
import massot_indexed_products
import data.fintype
import data.set.finite
import group_theory.submonoid
import tactic.ring
import chris_ring_lemma
local attribute [instance] classical.prop_decidable
-- Chris' proof of exactness
universes u v w

-- 00EJ

open finset classical quotient 

section
variables {α : Type u} {β : Type v} {γ : Type w}

lemma is_ring_hom.inj_of_kernel_eq_zero [comm_ring α] [comm_ring β] {f : α → β} [hf : is_ring_hom f] 
    (h : ∀ {x}, f x = 0 → x = 0) : function.injective f := 
λ x y hxy, by rw [← sub_eq_zero_iff_eq, ← is_ring_hom.map_sub f] at hxy;
  exact sub_eq_zero_iff_eq.1 (h hxy)

instance indexed_product.is_ring_hom [comm_ring α] {I : Type v} {f : I → Type w} [∀ i, comm_ring (f i)]
(g : α → Π i : I, f i) [rh : ∀ i : I, is_ring_hom (λ a : α, g a i)] : is_ring_hom g :=
{ map_add := λ x y, funext $ λ i, @is_ring_hom.map_add _ _ _ _ _ (rh i) x y,
  map_mul := λ x y, funext $ λ i, @is_ring_hom.map_mul _ _ _ _ _ (rh i) x y,
  map_one := funext $ λ i, @is_ring_hom.map_one _ _ _ _ _ (rh i) }

open finset

lemma exists_sum_iff_mem_span_finset {x : β} [ring α] [module α β] {s : finset β} 
    : x ∈ span (↑s : set β) ↔ ∃ r : β → α, x = s.sum (λ y, r y • y) :=
⟨λ ⟨r, hr⟩, ⟨r, hr.2.symm ▸ sum_bij_ne_zero (λ a _ _, a)
  (λ a has ha, classical.by_contradiction (λ h, ha (by simp [hr.1 _ h])))
  (λ _ _ _ _ _ _, id)
  (λ b hbr hb, ⟨b, (finsupp.mem_support_iff).2 (λ h, hb (by simp [h])), hb, rfl⟩)
  (λ _ _ _, rfl)⟩,
λ ⟨r, hr⟩, hr.symm ▸ is_submodule.sum (λ c hc, is_submodule.smul _ (subset_span hc))⟩

lemma exists_sum_iff_mem_span_image_finset {x : β} [ring α] [module α β] {s : finset γ}
    {f : γ → β} : x ∈ span (↑(s.image f) : set β) ↔ 
    ∃ r : γ → α, x = s.sum (λ b, r b • f b) :=
⟨λ h, let ⟨r, hr⟩ := exists_sum_iff_mem_span_finset.1 h in
have hc : ∀ y ∈ s, ∃ z ∈ s, f z = f y := λ y hy, ⟨y, hy, rfl⟩,
⟨λ y, if ∃ hy : y ∈ s, y = some (hc y hy) then r (f y) else 0, 
  hr.symm ▸ sum_bij_ne_zero (λ a ha _, some (mem_image.1 ha)) 
    (λ a ha _, let ⟨h, _⟩ := some_spec (mem_image.1 ha) in h) 
    (λ a₁ a₂ ha₁ _ ha₂ _ h, 
      let ⟨_, h₁⟩ := some_spec (mem_image.1 ha₁) in
      let ⟨_, h₂⟩ := some_spec (mem_image.1 ha₂) in
      h₁ ▸ h₂ ▸ h ▸ rfl)
    (λ b hbs hb0,
      have hfb : f b ∈ image f s := mem_image.2 ⟨b, hbs, rfl⟩,
      have hb : b = some (mem_image.1 hfb) := classical.by_contradiction
        (λ h, have h' : ¬∃ (x : b ∈ s), b = some _ := not_exists.2 (λ hy : b ∈ s, h), 
        by rw [if_neg h', zero_smul] at hb0; exact hb0 rfl),
      ⟨f b, hfb, by rwa if_pos at hb0; exact ⟨hbs, hb⟩, hb⟩)
    (λ a ha ha0, let ⟨h₁, h₂⟩ := some_spec (mem_image.1 ha) in
      by rw [if_pos, h₂]; exact ⟨h₁, by simp only [h₂]⟩)⟩,
λ ⟨r, hr⟩, hr.symm ▸ is_submodule.sum (λ c hc, is_submodule.smul _ 
    (subset_span (mem_image.2 ⟨c, hc, rfl⟩)))⟩
 
lemma sum_pow_mem_span {α R : Type*} [comm_ring R] (s : finset α)
    (f : α → R) (n : α → ℕ) (r : α → R) : s.sum (λ a, r a • f a) ^ (s.sum n + 1) ∈ span 
    (↑(s.image (λ a, f a ^ n a)) : set R) :=
finset.induction_on s (by simp) $ λ a s has hi, 
begin
  rw [sum_insert has, add_pow],
  refine @is_submodule.sum R R _ _ (span _) _ _ _ _ _ (λ k hk, _),
  cases le_total (n a) k with hak hak,
  { rw [← nat.add_sub_cancel' hak, pow_add],
    simp only [mul_assoc, smul_eq_mul, mul_pow, mul_left_comm _ (f a ^ n a)],
    exact is_submodule.smul' _ (subset_span (mem_image.2 ⟨a, mem_insert_self _ _, rfl⟩)) },
  { rw [sum_insert has, add_assoc, add_comm (n a), nat.add_sub_assoc hak, pow_add],
    simp only [mul_assoc, smul_eq_mul, mul_pow, mul_left_comm _ (sum s _ ^ (sum s n + 1))],
    have : span ↑(image (λ a, f a ^ n a) s) ⊆ span ↑(image (λ a, f a ^ n a) (insert a s)) := 
      span_minimal is_submodule_span (set.subset.trans 
        (by rw [image_insert,coe_subset]; exact subset_insert _ _) subset_span),
    exact is_submodule.smul' _ (this hi), }
end

lemma one_mem_span_pow_of_mem_span {α R : Type*} [comm_ring R] {s : finset α}
    {f : α → R} (n : α → ℕ) (h : (1 : R) ∈ span (↑(s.image f) : set R)) : 
    (1 : R) ∈ span (↑(s.image (λ x, f x ^ n x)) : set R) :=
let ⟨r, hr⟩ := exists_sum_iff_mem_span_image_finset.1 h in
@one_pow R _ (s.sum n + 1) ▸ hr.symm ▸ sum_pow_mem_span _ _ _ _

end

variables {R : Type u} {γ : Type v} [comm_ring R] [fintype γ]
open localization

def tag00EJ.α (f : γ → R) (x : R) : Π i, loc R (powers (f i)) :=
  λ i, of_comm_ring R _ x

noncomputable def tag00EJ.β {f : γ → R}
    (r : Π i, loc R (powers (f i))) (j k : γ) :
    loc R (powers (f j * f k)) :=
localize_more_left (f j) (f k) (r j) - localize_more_right (f j) (f k) (r k)

-- β not a ring hom but it's β₁ - β₂ with ring homs defined below.

noncomputable def tag00EJ.β₁ {f : γ → R}
    (r : Π i, loc R (powers (f i))) (j k : γ) :
    loc R (powers (f j * f k)) :=
localize_more_left (f j) (f k) (r j)

noncomputable def tag00EJ.β₂ {f : γ → R}
    (r : Π i, loc R (powers (f i))) (j k : γ) :
    loc R (powers (f j * f k)) :=
localize_more_right (f j) (f k) (r k)

open tag00EJ 

lemma localize_more_left_eq (f g x : R) (n : ℕ) : 
    localize_more_left f g ⟦⟨x, ⟨f^n, n, rfl⟩⟩⟧ = ⟦⟨x * g^n, (f * g)^n, n, rfl⟩⟧ :=
begin
  let h,
  show ⟦_⟧ * classical.some h = ⟦_⟧,
  have := some_spec h,
  rw ← quotient.out_eq (some h) at *,
  rcases out (some h) with ⟨s₁, s₂, hs⟩, intro this,
  rcases quotient.exact this with ⟨r, hr₁, hr₂⟩,
  refine quot.sound ⟨r, hr₁, _⟩,
  rw [sub_mul, sub_eq_zero_iff_eq] at hr₂,
  have hr₂' : s₂ * r = f ^ n * s₁ * r,
  { simpa using hr₂ },
  suffices : (s₂ * (x * g ^ n) - ((f * g) ^ n * (x * s₁))) * r = 0,
  { rw ← this, simp },
  simp only [sub_mul, mul_pow, mul_assoc, mul_left_comm s₂,
      mul_comm r, mul_left_comm r, hr₂'],
  ring
end

lemma localize_more_right_eq (f g x : R) (n : ℕ) : 
    localize_more_right f g ⟦⟨x, ⟨g^n, n, rfl⟩⟩⟧ = ⟦⟨x * f^n, (f * g)^n, n, rfl⟩⟧ := 
begin
  let h,
  show ⟦_⟧ * classical.some h = ⟦_⟧,
  have := some_spec h,
  rw ← quotient.out_eq (some h) at *,
  rcases out (some h) with ⟨s₁, s₂, hs⟩, intro this,
  rcases quotient.exact this with ⟨r, hr₁, hr₂⟩,
  refine quot.sound ⟨r, hr₁, _⟩,
  rw [sub_mul, sub_eq_zero_iff_eq] at hr₂,
  have hr₂' : s₂ * r = g ^ n * s₁ * r,
  { simpa using hr₂ },
  suffices : (s₂ * (x * f ^ n) - ((f * g) ^ n * (x * s₁))) * r = 0,
  { rw ← this, simp },
  simp only [sub_mul, mul_pow, mul_assoc, mul_left_comm s₂, 
      mul_comm r, mul_left_comm r, hr₂'],
  ring
end

lemma lemma_standard_covering₁ {f : γ → R}
    (h : (1 : R) ∈ span (↑(univ.image f) : set R)) : function.injective (α f) :=
@is_ring_hom.inj_of_kernel_eq_zero _ _ _ _ (α f) 
  (@indexed_product.is_ring_hom _ _ _ _ _ (α f) 
  (λ i, by unfold α; apply_instance))
begin 
  assume x hx,
  replace hx := congr_fun hx,
  have : ∀ i, ∃ e : ℕ, f i ^ e * x = 0 := λ i, begin
    rcases (quotient.eq.1 (hx i)) with ⟨r, hr₁, hr₂⟩,
    cases hr₁ with e he,
    have : x * r = 0 := by simpa using hr₂,
    exact ⟨e, by rwa [mul_comm, he]⟩
  end,
  let e : γ → ℕ := λ i, classical.some (this i),
  have he : ∀ i, f i ^ e i * x = 0 := λ i, some_spec (this i),
  cases exists_sum_iff_mem_span_image_finset.1 (one_mem_span_pow_of_mem_span e h) with r hr,
  rw [← one_mul x, hr, sum_mul, ← @sum_const_zero _ _ (univ : finset γ)],
  refine finset.sum_congr rfl (λ i _, _),
  rw [smul_eq_mul, mul_assoc, he, mul_zero],
end

lemma lemma_standard_covering₂ (f : γ → R) 
    (H : (1:R) ∈ span (↑(univ.image f) : set R)) (s : Π i, loc R (powers (f i))) :
    β s = 0 ↔ ∃ r : R, α f r = s := 
⟨λ h : β s = 0,
let t := λ i, out (s i) in
let r := λ i, some (t i).2.2 in
have hst : ∀ i, s i = ⟦⟨(t i).1, (f i) ^ (r i), r i, rfl⟩⟧ := 
    λ i, by simp [r, some_spec (t i).2.2],
have hi : ∀ i, s i = ⟦⟨(t i).1, (t i).2.1, (t i).2.2⟩⟧ := λ i, by simp,
have hβ : _ := λ i j, sub_eq_zero_iff_eq.1 $ show β s i j = 0, by rw h; refl,
have hβ : ∀ i j,
    (⟦⟨(t i).1 * f j ^ r i, ⟨(f i * f j) ^ r i, r i, rfl⟩⟩⟧ : loc R (powers (f i * f j))) =
    ⟦⟨(t j).1 * f i ^ r j, ⟨(f i * f j) ^ r j, r j, rfl⟩⟩⟧ := by conv at hβ in (_ = _) {rw [hst, hst,
      localize_more_left_eq, localize_more_right_eq] }; exact hβ,
have ∀ i j, ∃ n, 
    ((f i * f j) ^ r i * ((t j).1 * f i ^ r j) - 
    ((f i * f j) ^ r j * ((t i).1 * f j ^ r i)))
    * (f i * f j) ^ n = 0 :=
  λ i j, let ⟨t, ⟨n, hn⟩, hnt⟩ := quotient.exact (hβ i j) 
      in ⟨n, by rw hn; exact hnt⟩,
let n := λ i j, some (this i j) + r i + r j in
have hn : ∀ i j, (f i ^ r i * (t j).1 - 
    f j ^ r j * (t i).1) * (f i * f j) ^ n i j = 0 := 
  λ i j, by rw [← zero_mul (f i ^ r i), 
      ← zero_mul (f j ^ r j), ← some_spec (this i j)];
    simp [n, pow_add, mul_pow];
    ring,
let N := finset.sum (univ : finset (_ × _)) (λ ij, n ij.1 ij.2) in
have Nlt : ∀ i j, n i j ≤ N := λ i j, 
  @single_le_sum _ _ _ (λ h : γ × γ, n h.1 h.2) _
  _ (λ _ _, nat.zero_le _) _ (mem_univ (i, j)),
have hN : ∀ i j, (f i ^ r i * (t j).1 - 
    f j ^ r j * (t i).1) * (f i * f j) ^ N = 0 := λ i j, 
  begin rw [← nat.sub_add_cancel (Nlt i j), 
      ← zero_mul ((f i * f j) ^ (N - n i j)), ← hn i j, 
      pow_add _ (N - n i j), mul_pow, mul_pow],
    simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc],
  end,
let ⟨a, ha⟩ := exists_sum_iff_mem_span_image_finset.1 
    (one_mem_span_pow_of_mem_span (λ i, N + r i) H) in
⟨univ.sum (λ j, a j * (f j) ^ N * (t j).1),
funext (λ i, (hst i).symm ▸ quot.sound ⟨(f i) ^ N, ⟨N, rfl⟩,
have (λ j, f i ^ r i * (a j * f j ^ N * (t j).fst) * f i ^ N) =
      (λ j, (a j • (f j) ^ (N + r j) * (t i).1) * (f i) ^ N) := funext (λ j, begin
  rw [← sub_eq_zero_iff_eq, smul_eq_mul],
  simp only [mul_assoc, mul_left_comm _ (a j)],
  rw [← mul_sub],
  suffices : (f i ^ r i * (f j ^ N * ((t j).fst * f i ^ N))) -
      (f j ^ (N + r j) * ((t i).fst * f i ^ N)) = 0,
  { rw [this, mul_zero] },
  rw ← hN i j,
  simp [pow_add, mul_pow],
  ring,
  end),
begin
  suffices : ((t i).fst - (f i ^ r i * sum univ (λ j, a j * f j ^ N * (t j).1))) * f i ^ N = 0,
    simpa using this,
  rw [mul_sum, sub_mul, sum_mul, this, ← sum_mul, ← sum_mul, ← ha, one_mul, sub_self]
end⟩)⟩,
λ ⟨r, hr⟩, hr ▸ show β (α f r) = λ i j, 0, from funext $ λ i, funext $ λ j, 
  sub_eq_zero_iff_eq.2 $ loc_commutes _ _ _⟩
