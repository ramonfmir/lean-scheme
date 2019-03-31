import ring_theory.localization
import algebra.pi_instances
import linear_algebra.linear_combination
import tactic.find

universes u v

local attribute [instance] classical.prop_decidable

variables {R : Type u} [comm_ring R] 
variables {γ : Type v} [fintype γ] 

#check finsupp.mem_support_iff
#print finset.coe_insert
#check finset.sum_insert
#print finsupp

#check mem_span_iff_lc

-- This is now : mem_span_iff_lc

lemma exists_sum_iff_mem_span_finset 
{α : Type u} {β : Type v} [comm_ring α] [add_comm_group β] [module α β]
{x : β} {S : finset β} 
:   x ∈ submodule.span α (↑S : set β) 
  ↔ ∃ r : β → α, x = S.sum (λ y, r y • y) :=
begin
  sorry,
end

#print ideal.span
#check @lc.mem_supported

lemma exists_sum_iff_mem_span_image_finset 
{α : Type u} {β : Type v} [comm_ring α] [comm_ring β] 
{x : β} [module α β] {s : finset γ} {f : γ → β} 
: x ∈ submodule.span α (↑(s.image f) : set β) ↔ 
  ∃ r : γ → α, x = s.sum (λ b, r b • f b) :=
begin
  split,
  { intros Hx,
    --unfold ideal.span at Hx,
    rw mem_span_iff_lc at Hx,
    rcases Hx with ⟨l, Hls, Hlt⟩,
    rw lc.total_apply at Hlt,
    use (l.to_fun ∘ f),
    rw ←Hlt,
    simp [finsupp.sum],
    rw lc.mem_supported at Hls,
    sorry, },
  { sorry, }
end

-- lemma exists_sum_iff_mem_span_image_finset 
-- {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] 
-- {x : β} [module α β] {s : finset γ}
--     {f : γ → β} : x ∈ ideal.span (↑(s.image f) : set β) ↔ 
--     ∃ r : γ → α, x = s.sum (λ b, r b • f b) :=
-- ⟨λ h, let ⟨r, hr⟩ := exists_sum_iff_mem_span_finset.1 h in
-- have hc : ∀ y ∈ s, ∃ z ∈ s, f z = f y := λ y hy, ⟨y, hy, rfl⟩,
-- ⟨λ y, if ∃ hy : y ∈ s, y = some (hc y hy) then r (f y) else 0, 
--   hr.symm ▸ sum_bij_ne_zero (λ a ha _, some (mem_image.1 ha)) 
--     (λ a ha _, let ⟨h, _⟩ := some_spec (mem_image.1 ha) in h) 
--     (λ a₁ a₂ ha₁ _ ha₂ _ h, 
--       let ⟨_, h₁⟩ := some_spec (mem_image.1 ha₁) in
--       let ⟨_, h₂⟩ := some_spec (mem_image.1 ha₂) in
--       h₁ ▸ h₂ ▸ h ▸ rfl)
--     (λ b hbs hb0,
--       have hfb : f b ∈ image f s := mem_image.2 ⟨b, hbs, rfl⟩,
--       have hb : b = some (mem_image.1 hfb) := classical.by_contradiction
--         (λ h, have h' : ¬∃ (x : b ∈ s), b = some _ := not_exists.2 (λ hy : b ∈ s, h), 
--         by rw [if_neg h', zero_smul] at hb0; exact hb0 rfl),
--       ⟨f b, hfb, by rwa if_pos at hb0; exact ⟨hbs, hb⟩, hb⟩)
--     (λ a ha ha0, let ⟨h₁, h₂⟩ := some_spec (mem_image.1 ha) in
--       by rw [if_pos, h₂]; exact ⟨h₁, by simp only [h₂]⟩)⟩,
-- λ ⟨r, hr⟩, hr.symm ▸ is_submodule.sum (λ c hc, is_submodule.smul _ 
--     (subset_span (mem_image.2 ⟨c, hc, rfl⟩)))⟩

-- Change to predicate.

def α (f : γ → R) : R → Π i, localization R (powers (f i)) :=
λ x i, localization.of x

instance α.is_ring_hom (f : γ → R) : is_ring_hom (α f) :=
{ map_one := funext $ λ i, is_ring_hom.map_one _,
  map_add := λ x y, funext $ λ i, is_ring_hom.map_add _,
  map_mul := λ x y, funext $ λ i, is_ring_hom.map_mul _, }

lemma is_ring_hom.inj_of_trivial_ker
{α : Type u} {β : Type v} [comm_ring α] [comm_ring β] {f : α → β} [is_ring_hom f] 
: (∀ {x}, f x = 0 → x = 0) → function.injective f := 
λ h x y hxy, 
  by rw [←sub_eq_zero_iff_eq, ←is_ring_hom.map_sub f] at hxy;
  exact sub_eq_zero_iff_eq.1 (h hxy)

lemma lemma_standard_covering₁ {f : γ → R} (h : (1 : R) ∈ ideal.span (set.range f)) 
: function.injective (α f) := 
begin
  have Hrh := @α.is_ring_hom _ _ _ _ f,
  have Hker := @is_ring_hom.inj_of_trivial_ker _ _ _ _ (α f) Hrh,
  apply Hker,
  intros x Hx,
  replace Hx := congr_fun Hx,
  have Hn : ∀ i, ∃ n : ℕ, f i ^ n * x = 0,
    intros i,
    rcases (quotient.eq.1 (Hx i)) with ⟨r, ⟨n, Hn⟩, Hr⟩,
    simp at Hr,
    rw mul_comm at Hr,
    use n,
    rw Hn,
    exact Hr,
  let e : γ → ℕ := λ i, classical.some (Hn i),
end
