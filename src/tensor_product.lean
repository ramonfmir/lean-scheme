import algebra.group_power linear_algebra.prod_module algebra.module
import data.finsupp data.set.basic tactic.ring Kenny_comm_alg.temp
noncomputable theory

universes u u₁ v v₁ w w₁

open classical set function
local attribute [instance] decidable_inhabited prop_decidable

namespace prod

@[simp] lemma prod_add_prod {α : Type u} {β : Type v} {γ : Type w}
  [comm_ring α] [module α β] [module α γ] (x₁ x₂ : β) (y₁ y₂ : γ) :
  (x₁, y₁) + (x₂, y₂) = (x₁ + x₂, y₁ + y₂) := rfl

@[simp] lemma smul_prod {α : Type u} {β : Type v} {γ : Type w}
  [comm_ring α] [module α β] [module α γ] (r : α) (x : β) (y : γ) :
  r • (x, y) = (r • x, r • y) := rfl

@[simp] lemma fst_smul {α : Type u} {β : Type v} {γ : Type w}
  [comm_ring α] [module α β] [module α γ] (r : α) (z : β × γ) :
  (r • z).fst = r • z.fst := rfl

@[simp] lemma snd_smul {α : Type u} {β : Type v} {γ : Type w}
  [comm_ring α] [module α β] [module α γ] (r : α) (z : β × γ) :
  (r • z).snd = r • z.snd := rfl

end prod

class type_singleton (α : Type u) : Type u :=
(default : α)
(unique : ∀ x : α, x = default)

namespace type_singleton

variables (α : Type u) [type_singleton α]
variables (β : Type v) [type_singleton β]

def equiv_unit : equiv α unit :=
{ to_fun    := λ x, unit.star,
  inv_fun   := λ x, type_singleton.default α,
  left_inv  := λ x, by rw type_singleton.unique x,
  right_inv := λ x, punit.cases_on x rfl }

def equiv_singleton : equiv α β :=
{ to_fun    := λ x, type_singleton.default β,
  inv_fun   := λ x, type_singleton.default α,
  left_inv  := λ x, by rw type_singleton.unique x,
  right_inv := λ x, by rw type_singleton.unique x }

end type_singleton

-- (moved to temp)

section bilinear

variables {α : Type u} [comm_ring α]
include α

variables {β : Type v} {γ : Type w} {α₁ : Type u₁} {β₁ : Type v₁}
variables [module α β] [module α γ] [module α α₁] [module α β₁]

structure is_bilinear_map {β γ α₁}
  [module α β] [module α γ] [module α α₁]
  (f : β → γ → α₁) : Prop :=
(add_pair : ∀ x y z, f (x + y) z = f x z + f y z)
(pair_add : ∀ x y z, f x (y + z) = f x y + f x z)
(smul_pair : ∀ r x y, f (r • x) y = r • f x y)
(pair_smul : ∀ r x y, f x (r • y) = r • f x y)

variables {f : β → γ → α₁} (hf : is_bilinear_map f)
include hf

theorem is_bilinear_map.zero_pair : ∀ y, f 0 y = 0 :=
λ y, calc f 0 y
        = f (0 + 0) y - f 0 y : by rw [hf.add_pair 0 0 y]; simp
    ... = 0 : by simp

theorem is_bilinear_map.pair_zero : ∀ x, f x 0 = 0 :=
λ x, calc f x 0
        = f x (0 + 0) - f x 0 : by rw [hf.pair_add x 0 0]; simp
    ... = 0 : by simp

theorem is_bilinear_map.linear_pair (y : γ) : is_linear_map (λ x, f x y) :=
{ add  := λ m n, hf.add_pair m n y,
  smul := λ r m, hf.smul_pair r m y }

theorem is_bilinear_map.pair_linear (x : β) : is_linear_map (λ y, f x y) :=
{ add  := λ m n, hf.pair_add x m n,
  smul := λ r m, hf.pair_smul r x m }

variables {g : α₁ → β₁} (hg : is_linear_map g)
include hg

theorem is_bilinear_map.comp : is_bilinear_map (λ x y, g (f x y)) :=
{ add_pair  := λ x y z, by rw [hf.add_pair, hg.add],
  pair_add  := λ x y z, by rw [hf.pair_add, hg.add],
  smul_pair := λ r x y, by rw [hf.smul_pair, hg.smul],
  pair_smul := λ r x y, by rw [hf.pair_smul, hg.smul] }

omit hf hg

variables (β γ)

structure module_iso (β γ) [module α β] [module α γ] extends equiv β γ :=
( linear : is_linear_map to_fun )

end bilinear

infix ` ≃ₘ `:25 := module_iso

namespace module_iso

variables (α : Type u) [comm_ring α]
variables (β : Type v) (γ : Type w) (α₁ : Type u₁) [module α β] [module α γ] [module α α₁]

variables {α β γ α₁}
include α

protected def refl : β ≃ₘ β :=
{ linear := is_linear_map.id
  ..equiv.refl β }

protected def symm (hbc : β ≃ₘ γ) : γ ≃ₘ β :=
{ linear := is_linear_map.inverse hbc.linear hbc.left_inv hbc.right_inv
  ..equiv.symm hbc.to_equiv }

protected def trans : β ≃ₘ γ → γ ≃ₘ α₁ → β ≃ₘ α₁ :=
λ hbc hca,
{ linear := is_linear_map.comp hca.linear hbc.linear
  ..equiv.trans hbc.to_equiv hca.to_equiv }

end module_iso

namespace multiset

variable {α : Type u}

--@[simp] theorem map_id (s : multiset α) : map id s = s :=
--quot.induction_on s $ λ l, congr_arg coe $ list.map_id _

end multiset

namespace list

theorem map_neg {α : Type u} [add_comm_group α] :
  ∀ L:list α, (L.map (λ x, -x)).sum = -L.sum
| []     := by simp
| (h::t) := by simp [map_neg t]

theorem sum_singleton {α : Type u} [add_group α] {x : α} :
  list.sum [x] = x :=
calc list.sum [x] = x + list.sum [] : list.sum_cons
              ... = x + 0 : congr_arg _ list.sum_nil
              ... = x : add_zero x

end list

namespace finsupp

variables {α : Type u} {β : Type v} [add_comm_group β] {a : α} {b b₁ b₂ : β}

variables {α₁ : Type u₁}

variables {γ : Type w} [add_comm_group γ]

@[simp] lemma single_neg : single a (-b) = -single a b :=
ext $ assume a',
begin
  by_cases h : a = a',
  { rw [h, neg_apply, single_eq_same, single_eq_same] },
  { rw [neg_apply, single_eq_of_ne h, single_eq_of_ne h, neg_zero] }
end

@[simp] lemma single_sub : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
by simp

theorem sum_neg_index' {g : α →₀ β} {h : α → β → γ}:
  (∀ (a : α) (b₁ b₂ : β), h a (b₁ - b₂) = h a b₁ - h a b₂) → finsupp.sum (-g) h = -finsupp.sum g h :=
begin
  intro H,
  rw ← zero_sub,
  rw sum_sub_index H,
  rw sum_zero_index,
  rw zero_sub
end

@[simp] theorem finsum_apply {S : finset α₁} {f : α₁ → α →₀ β} {z : α} :
  (S.sum f) z = S.sum (λ x, f x z) :=
eq.symm $ finset.sum_hom (λ g : α →₀ β, g z) rfl (λ x y, rfl)

end finsupp

namespace tensor_product

variables (α : Type u) [comm_ring α]
variables (β : Type v) (γ : Type w) (α₁ : Type u₁) (β₁ : Type v₁) (γ₁ : Type w₁)
variables [module α β] [module α γ] [module α α₁] [module α β₁] [module α γ₁]

def free_abelian_group : Type (max v w) := β × γ →₀ ℤ

instance free_abelian_group.has_coe_to_fun : has_coe_to_fun (free_abelian_group β γ) :=
finsupp.has_coe_to_fun

instance free_abelian_group.add_comm_monoid : add_comm_monoid (free_abelian_group β γ) :=
finsupp.add_comm_monoid

instance free_abelian_group.add_comm_group : add_comm_group (free_abelian_group β γ) :=
finsupp.add_comm_group

theorem structural_theorem (f : free_abelian_group β γ) :
  ∃ S : finset (free_abelian_group β γ), (∀ g ∈ S, ∃ (x : β) (y : γ) (n : ℤ) (H : n ≠ 0), g = finsupp.single (x, y) n) ∧ S.sum id = f :=
begin
--  apply finsupp.induction f,
  rcases f with ⟨S, f, hs⟩,
  existsi S.image (λ z, finsupp.single z $ f z),
  split,
  { intros g hg,
    rw finset.mem_image at hg,
    rcases hg with ⟨z, hzs, hg⟩,
    cases z with x y,
    exact ⟨x, y, f (x, y), (hs (x, y)).1 hzs, by simp [hg]⟩ },
  { rw @finset.sum_image _ _ _  _  _ _  _  (λ (z : β × γ),finsupp.single z (f z)) _,
  --finset.sum_image : ∀ {α : Type ?} {β : Type ?} {γ : Type ?} {f : α → β}
  -- [_inst_1 : add_comm_monoid β] [_inst_2 : decidable_eq α] [_inst_3 : decidable_eq γ] 
  --{s : finset γ} {g : γ → α}, (∀ (x : γ), x ∈ s → ∀ (y : γ), y ∈ s → g x = g y → x = y) 
  -- → finset.sum (finset.image g s) f = finset.sum s (λ (x : γ), f (g x))

    { apply finsupp.ext,
      intro z,
      by_cases hz : f z = 0,
      { simp,
        rw ← finset.sum_subset (finset.empty_subset S),
        { simpa using hz.symm },
        { intros x hx hnx,
          rw id,
          rw finsupp.single_apply,
          by_cases x = z; simp [h, hz] } },
      { simp,
        have h1 : finset.singleton z ⊆ S,
        { intros x hx,
          rw finset.mem_singleton at hx,
          rw hs, subst hx, exact hz },
        rw ← finset.sum_subset h1,
        { rw finset.sum_singleton,
          rw id,
          rw finsupp.single_apply,
          rw if_pos rfl,
          refl  },
        { intros x hx hnxz,
          rw finset.mem_singleton at hnxz,
          rw id,
          rw finsupp.single_apply,
          rw if_neg hnxz } } },
    { intros x hx y hy hxy,
      by_contradiction hnxy,
      have hxyx : (finsupp.single x (f x) : β × γ →₀ ℤ) x = (finsupp.single y (f y) : β × γ →₀ ℤ) x,
      { change finsupp.single x (f x) = finsupp.single y (f y) at hxy,
        rw hxy },
      rw finsupp.single_apply at hxyx,
      rw finsupp.single_apply at hxyx,
      rw if_pos rfl at hxyx,
      rw if_neg (ne.symm hnxy) at hxyx,
      rw hs at hx,
      exact hx hxyx } }
end

variables α {β γ}
include α

namespace relators

def pair_add : β → γ → γ → ℤ → free_abelian_group β γ :=
λ x y₁ y₂ n, finsupp.single (x, y₁) n + finsupp.single (x, y₂) n - finsupp.single (x, y₁ + y₂) n

def add_pair : β → β → γ → ℤ → free_abelian_group β γ :=
λ x₁ x₂ y n, finsupp.single (x₁, y) n + finsupp.single (x₂, y) n - finsupp.single (x₁ + x₂, y) n

def smul_trans : α → β → γ → ℤ → free_abelian_group β γ :=
λ r x y n, finsupp.single (r • x, y) n - finsupp.single (x, r • y) n

variables α β γ

def smul_aux : α → β × γ → ℤ → free_abelian_group β γ :=
λ r f y, finsupp.single (r • f.fst, f.snd) y

variables {α β γ}

theorem smul_aux_zero {r : α} (xy : β × γ) :
  smul_aux α β γ r xy (0:ℤ) = 0 :=
by simp [smul_aux]; refl

theorem smul_aux_add {r : α} (xy : β × γ) (m n : ℤ) :
  smul_aux α β γ r xy (m + n) = smul_aux α β γ r xy m + smul_aux α β γ r xy n :=
by simp [smul_aux]

theorem smul_aux_sub {r : α} (xy : β × γ) (m n : ℤ) :
  smul_aux α β γ r xy (m - n) = smul_aux α β γ r xy m - smul_aux α β γ r xy n :=
by simp [smul_aux]

theorem pair_add.neg (x : β) (y₁ y₂ : γ) (n : ℤ) :
  -pair_add α x y₁ y₂ n = pair_add α x y₁ y₂ (-n) :=
begin
  unfold pair_add,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  simp,
  repeat { rw add_comm, rw add_assoc }
end

theorem pair_add.smul (r : α) (x : β) (y₁ y₂ : γ) (n : ℤ) :
  finsupp.sum (pair_add α x y₁ y₂ n) (smul_aux α β γ r) = relators.pair_add α (r • x) y₁ y₂ n :=
begin
  unfold pair_add,
  rw finsupp.sum_sub_index smul_aux_sub,
  rw finsupp.sum_add_index,
  repeat { rw finsupp.sum_single_index },
  repeat { intros, simp [smul_aux] },
  repeat { refl }
end

theorem add_pair.neg (x₁ x₂ : β) (y : γ) (n : ℤ) :
  -add_pair α x₁ x₂ y n = add_pair α x₁ x₂ y (-n) :=
begin
  unfold add_pair,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  simp,
  repeat { rw add_comm, rw add_assoc }
end

theorem add_pair.smul (r : α) (x₁ x₂ : β) (y : γ) (n : ℤ) :
  finsupp.sum (add_pair α x₁ x₂ y n) (smul_aux α β γ r) = relators.add_pair α (r • x₁) (r • x₂) y n :=
begin
  unfold add_pair,
  rw finsupp.sum_sub_index smul_aux_sub,
  rw finsupp.sum_add_index,
  repeat { rw finsupp.sum_single_index },
  repeat { intros, simp [smul_aux, smul_add] },
  repeat { refl }
end

theorem smul_trans.neg (r : α) (x : β) (y : γ) (n : ℤ) :
  -smul_trans α r x y n = smul_trans α r x y (-n) :=
begin
  unfold smul_trans,
  rw finsupp.single_neg,
  rw finsupp.single_neg,
  simp
end

theorem smul_trans.smul (r r' : α) (x : β) (y : γ) (n : ℤ) :
  finsupp.sum (smul_trans α r' x y n) (smul_aux α β γ r) = relators.smul_trans α r' (r • x) y n :=
begin
  unfold smul_trans,
  rw finsupp.sum_sub_index smul_aux_sub,
  repeat { rw finsupp.sum_single_index },
  repeat { intros, simp [smul_aux, smul_add, smul_smul, mul_comm] },
  repeat { refl },
end

end relators

variables (α β γ)

def relators : set (free_abelian_group β γ) :=
{f | (∃ x y₁ y₂ n, f = relators.pair_add α x y₁ y₂ n) ∨
  (∃ x₁ x₂ y n, f = relators.add_pair α x₁ x₂ y n) ∨
  (∃ r x y n, f = relators.smul_trans α r x y n)}

theorem relators.zero_mem : (0 : free_abelian_group β γ ) ∈ relators α β γ :=
or.inl ⟨0, 0, 0, 0, by simpa [relators.pair_add, finsupp.single_zero]⟩

theorem relators.neg_mem : ∀ f, f ∈ relators α β γ → -f ∈ relators α β γ :=
begin
  intros f hf,
  rcases hf with hf | hf | hf;
  rcases hf with ⟨a, b, c, d, hf⟩,
  { from or.inl ⟨a, b, c, -d, by rw [hf, relators.pair_add.neg]⟩ },
  { from or.inr (or.inl ⟨a, b, c, -d, by rw [hf, relators.add_pair.neg]⟩) },
  { from or.inr (or.inr ⟨a, b, c, -d, by rw [hf, relators.smul_trans.neg]⟩) }
end

def closure : set (free_abelian_group β γ) :=
{f | ∃ (L : list (free_abelian_group β γ)),
  (∀ x ∈ L, x ∈ relators α β γ) ∧ L.sum = f}

def r : free_abelian_group β γ → free_abelian_group β γ → Prop :=
λ f g, f - g ∈ closure α β γ

local infix ≈ := r α β γ

theorem refl (f : free_abelian_group β γ) : f ≈ f :=
⟨[], by simp⟩

theorem symm (f g : free_abelian_group β γ) : f ≈ g → g ≈ f :=
λ ⟨L, hL, hLfg⟩, ⟨L.map (λ x, -x),
  λ x hx, let ⟨y, hyL, hyx⟩ := list.exists_of_mem_map hx in
    by rw ← hyx; exact relators.neg_mem α β γ y (hL y hyL),
  by simp [list.map_neg, hLfg]⟩

theorem trans (f g h : free_abelian_group β γ) : f ≈ g → g ≈ h → f ≈ h :=
λ ⟨L₁, hL₁, hLfg₁⟩ ⟨L₂, hL₂, hLfg₂⟩,
⟨L₁ ++ L₂,
 λ x hx, by rw [list.mem_append] at hx; from or.cases_on hx (hL₁ x) (hL₂ x),
 by simp [hLfg₁, hLfg₂]⟩

instance : setoid (free_abelian_group β γ) :=
⟨r α β γ, refl α β γ, symm α β γ, trans α β γ⟩

end tensor_product

def tensor_product {α} (β γ) [comm_ring α] [module α β] [module α γ] : Type (max v w) :=
quotient (tensor_product.setoid α β γ)

local infix ` ⊗ `:100 := tensor_product

namespace tensor_product

variables (α : Type u) [comm_ring α]
variables (β : Type v) (γ : Type w) (α₁ : Type u₁) (β₁ : Type v₁) (γ₁ : Type w₁)
variables [module α β] [module α γ] [module α α₁] [module α β₁] [module α γ₁]

include α

def add : β ⊗ γ → β ⊗ γ → β ⊗ γ :=
quotient.lift₂ (λ f g, ⟦f + g⟧ : free_abelian_group β γ → free_abelian_group β γ → β ⊗ γ) $
λ f₁ f₂ g₁ g₂ ⟨L₁, hL₁, hLfg₁⟩ ⟨L₂, hL₂, hLfg₂⟩, quotient.sound
⟨L₁ ++ L₂,
 λ x hx, by rw [list.mem_append] at hx; from or.cases_on hx (hL₁ x) (hL₂ x),
 by rw [@list.sum_append _ _ L₁ L₂, hLfg₁, hLfg₂]; simp⟩

protected theorem add_assoc (f g h : β ⊗ γ) : add α β γ (add α β γ f g) h = add α β γ f (add α β γ g h) :=
quotient.induction_on₃ f g h $ λ m n k, quotient.sound $ by simp

def zero : β ⊗ γ := ⟦0⟧

protected theorem zero_add (f : β ⊗ γ) : add α β γ (zero α β γ) f = f :=
quotient.induction_on f $ λ m, quotient.sound $ by simp

protected theorem add_zero (f : β ⊗ γ) : add α β γ f (zero α β γ) = f :=
quotient.induction_on f $ λ m, quotient.sound $ by simp

def neg : β ⊗ γ → β ⊗ γ :=
quotient.lift (λ f, ⟦-f⟧ : free_abelian_group β γ → β ⊗ γ) $
λ f g ⟨L, hL, hLfg⟩, quotient.sound ⟨L.map (λ x, -x),
  λ x hx, let ⟨y, hyL, hyx⟩ := list.exists_of_mem_map hx in
    by rw ← hyx; exact relators.neg_mem α β γ y (hL y hyL),
  by simp [list.map_neg, hLfg]⟩

protected theorem add_left_neg (f : β ⊗ γ) : add α β γ (neg α β γ f) f = zero α β γ :=
quotient.induction_on f $ λ m, quotient.sound $ by simp

protected theorem add_comm (f g : β ⊗ γ) : add α β γ f g = add α β γ g f :=
quotient.induction_on₂ f g $ λ m n, quotient.sound $ by simp

instance : add_comm_group (β ⊗ γ) :=
{ add          := add α β γ,
  add_assoc    := tensor_product.add_assoc α β γ,
  zero         := zero α β γ,
  zero_add     := tensor_product.zero_add α β γ,
  add_zero     := tensor_product.add_zero α β γ,
  neg          := neg α β γ,
  add_left_neg := tensor_product.add_left_neg α β γ,
  add_comm     := tensor_product.add_comm α β γ }

theorem mem_closure_of_finset {f : free_abelian_group β γ} :
  (∃ (S : finset (free_abelian_group β γ)) g,
     S.sum g = f ∧ ∀ x ∈ S, g x ∈ relators α β γ) →
  f ∈ closure α β γ :=
λ ⟨S, g, hSf, hSr⟩, begin
  cases S with ms hms,
  cases quot.exists_rep ms with L hL,
  existsi L.map g,
  split,
  { intros x hxL,
    rcases list.exists_of_mem_map hxL with ⟨y, hyL, hyx⟩,
    have hyms : y ∈ ms,
    { unfold has_mem.mem,
      unfold multiset.mem,
      rw ← hL,
      rw quot.lift_on,
      rwa @quot.lift_beta _ (list.perm.setoid (free_abelian_group β γ)).r,
      exact multiset.mem._proof_1 y },
    rw ← hyx,
    exact hSr y hyms },
  { change multiset.sum (multiset.map g ms) = f at hSf,
    rw ← hL at hSf,
    rw ← multiset.coe_sum (list.map g L),
    exact hSf }
end

private lemma zero_eq_zero : (0 : free_abelian_group β γ) = (0 : β × γ →₀ ℤ) := rfl

private lemma sum_zero_index (f : β × γ → ℤ → free_abelian_group β γ) :
  @finsupp.sum (β × γ) ℤ (free_abelian_group β γ) int.has_zero _ (0 : free_abelian_group β γ) f = 0 :=
begin
  rw zero_eq_zero,
  simp [finsupp.sum],
  refl
end

set_option pp.all true
private lemma sum_zero_index' (f : β × γ → ℤ → α₁) :
  @finsupp.sum (β × γ) ℤ α₁ int.has_zero _ (0 : free_abelian_group β γ) f = 0 :=
begin
  rw zero_eq_zero,
  simp [finsupp.sum]
end

def smul : α → β ⊗ γ → β ⊗ γ :=
λ r, quotient.lift (λ f, ⟦f.sum (relators.smul_aux α β γ r)⟧ : free_abelian_group β γ → β ⊗ γ) $
λ f g ⟨L, hL, hLfg⟩, quotient.sound
begin
  clear _fun_match,
  induction L generalizing f g,
  { existsi [],
    have : f = g,
      by simpa [add_neg_eq_zero] using hLfg.symm,
    simp [this] },
  { specialize L_ih (λ z hzt, hL z (or.inr hzt)) L_tl.sum (0:free_abelian_group β γ),
    specialize L_ih ⟨L_tl,
      λ z hzt, hL z (or.inr hzt),
      eq.symm (sub_zero _)⟩,
    specialize L_ih (eq.symm $ sub_zero _),
    rcases L_ih with ⟨L', hL', hLfg'⟩,
    rw [sum_zero_index] at hLfg',
    simp at hLfg',
    rcases hL L_hd (or.inl rfl) with h | h | h,
    { rcases h with ⟨x, y₁, y₂, n, h⟩,
      existsi list.cons (relators.pair_add α (r • x) y₁ y₂ n) L',
      split,
      { exact λ z hz, or.cases_on (list.eq_or_mem_of_mem_cons hz)
          (λ hzh, or.inl ⟨r • x, y₁, y₂, n, hzh⟩)
          (λ hzt, hL' z hzt) },
      { rw ← finsupp.sum_sub_index,
        rw ← hLfg,
        rw list.sum_cons,
        rw @list.sum_cons _ _ L',
        rw finsupp.sum_add_index,
        rw ← hLfg',
        rw h,
        rw relators.pair_add.smul,
        all_goals { intros, simp [relators.smul_aux], try {refl} } } },
    { rcases h with ⟨x₁, x₂, y, n, h⟩,
      existsi list.cons (relators.add_pair α (r • x₁) (r • x₂) y n) L',
      split,
      { exact λ z hz, or.cases_on (list.eq_or_mem_of_mem_cons hz)
          (λ hzh, or.inr $ or.inl ⟨r • x₁, r • x₂, y, n, hzh⟩)
          (λ hzt, hL' z hzt) },
      { rw ← finsupp.sum_sub_index,
        rw ← hLfg,
        rw list.sum_cons,
        rw @list.sum_cons _ _ L',
        rw finsupp.sum_add_index,
        rw ← hLfg',
        rw h,
        rw relators.add_pair.smul,
        all_goals { intros, simp [relators.smul_aux], try {refl} } } },
    { rcases h with ⟨r', x, y, n, h⟩,
      existsi list.cons (relators.smul_trans α r' (r • x) y n) L',
      split,
      { exact λ z hz, or.cases_on (list.eq_or_mem_of_mem_cons hz)
          (λ hzh, or.inr $ or.inr ⟨r', r • x, y, n, hzh⟩)
          (λ hzt, hL' z hzt) },
      { rw ← finsupp.sum_sub_index,
        rw ← hLfg,
        rw list.sum_cons,
        rw @list.sum_cons _ _ L',
        rw finsupp.sum_add_index,
        rw ← hLfg',
        rw h,
        rw relators.smul_trans.smul,
        all_goals { intros, simp [relators.smul_aux], try {refl} } } } }
end

protected theorem smul_add (r : α) (f g : β ⊗ γ) : smul α β γ r (add α β γ f g) = add α β γ (smul α β γ r f) (smul α β γ r g) :=
quotient.induction_on₂ f g $ λ m n, quotient.sound $ by rw [finsupp.sum_add_index]; all_goals { intros, simp [relators.smul_aux], try {refl} }

protected theorem add_smul (r₁ r₂ : α) (f : β ⊗ γ) : smul α β γ (r₁ + r₂) f = add α β γ (smul α β γ r₁ f) (smul α β γ r₂ f) :=
quotient.induction_on f $ λ m, quotient.sound $
begin
  unfold relators.smul_aux,
  simp [add_smul],
  rcases structural_theorem β γ m with ⟨S, hS, hSm⟩,
  rw ← hSm,
  apply symm,
  apply mem_closure_of_finset,
  existsi S,
  revert m hS hSm,
  apply finset.induction_on S,
  { intros m hS hSm,
    existsi id,
    split,
    { simp,
      rw sum_zero_index,
      rw sum_zero_index,
      rw sum_zero_index,
      simp },
    { intros x hx,
      exfalso,
      exact hx } },
  { intros g T hgT ih m hS hSm,
    rcases hS g (finset.mem_insert_self g T) with ⟨x, y, n, H, h⟩,
    rcases ih (T.sum id) (λ g' hg', hS g' $
      finset.mem_insert_of_mem hg') rfl with ⟨φ', hst', hss'⟩,
    existsi (λ f, if f = g then finsupp.single (r₁ • x, y) n +
      finsupp.single (r₂ • x, y) n -
      finsupp.single (r₁ • x + r₂ • x, y) n else φ' f),
    split,
    { rw finset.sum_insert,
      rw finset.sum_insert,
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw if_pos rfl,
      rw h,
      rw id.def,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      have h1 : finset.sum T
        (λ (f : free_abelian_group β γ),
           ite (f = finsupp.single (x, y) n)
             (finsupp.single (r₁ • x, y) n + finsupp.single (r₂ • x, y) n -
                finsupp.single (r₁ • x + r₂ • x, y) n)
             (φ' f)) = finset.sum T φ',
      { apply finset.sum_congr,
        { refl },
        { intros g' hg',
          have h1 : g' ≠ g,
          { intro hgg',
            rw hgg' at hg',
            exact hgT hg' },
          rw h at h1,
          rw if_neg h1 } },
      rw h1,
      rw hst',
      unfold prod.fst,
      unfold prod.snd,
      simp,
      all_goals { intros,
        try {rw finsupp.single_zero},
        try {rw finsupp.single_zero},
        try {rw finsupp.single_add},
        try {refl},
        try {refl},
        try {exact hgT} } },
    { intros f' hf',
      rw finset.mem_insert at hf',
      cases hf',
      { dsimp,
        rw if_pos hf',
        from or.inr (or.inl ⟨r₁ • x, r₂ • x, y, n, rfl⟩) },
      { have h1 : f' ≠ g,
        { intro hfg',
          rw hfg' at hf',
          exact hgT hf' },
        dsimp,
        rw if_neg h1,
        from hss' f' hf' } } }
end

protected theorem mul_smul (r₁ r₂ : α) (f : β ⊗ γ) : smul α β γ (r₁ * r₂) f = smul α β γ r₁ (smul α β γ r₂ f) :=
quotient.induction_on f $ λ m, quotient.sound $
begin
  unfold relators.smul_aux,
  simp [mul_smul],
  rcases structural_theorem β γ m with ⟨S, hS, hSm⟩,
  rw ← hSm,
  apply symm,
  apply mem_closure_of_finset,
  existsi S,
  existsi (λ f, 0 : free_abelian_group β γ → free_abelian_group β γ),
  revert m hS hSm,
  apply finset.induction_on S,
  { intros m hS hSm,
    split,
    { simp,
      rw sum_zero_index,
      rw sum_zero_index,
      rw sum_zero_index,
      simp },
    { intros x hx,
      exfalso,
      exact hx } },
  { intros g T hgT ih m hS hSm,
    rcases hS g (finset.mem_insert_self g T) with ⟨x, y, n, H, h⟩,
    rcases ih (T.sum id) (λ g' hg', hS g' $
      finset.mem_insert_of_mem hg') rfl with ⟨hst', hss'⟩,
    split,
    { rw finset.sum_insert,
      rw finset.sum_insert,
      rw finset.sum_const_zero,
      rw finset.sum_const_zero at hst',
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_add_index,
      rw h,
      rw id.def,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      unfold prod.fst,
      unfold prod.snd,
      rw add_comm_group.zero_add,
      rw hst',
      simp,
      all_goals { intros,
        try {rw finsupp.single_zero},
        try {rw finsupp.single_zero},
        try {rw finsupp.single_add},
        try {refl},
        try {refl},
        try {exact hgT} } },
    { intros f' hf',
      dsimp,
      exact relators.zero_mem α β γ } }
end

protected theorem one_smul (f : β ⊗ γ) : smul α β γ 1 f = f :=
quotient.induction_on f $ λ m, quotient.sound $ by simp [relators.smul_aux]

instance : module α (β ⊗ γ) :=
{ smul     := smul α β γ,
  smul_add := tensor_product.smul_add α β γ,
  add_smul := tensor_product.add_smul α β γ,
  mul_smul := tensor_product.mul_smul α β γ,
  one_smul := tensor_product.one_smul α β γ }

@[simp] lemma add_quot (f g : free_abelian_group β γ) : @has_add.add (β ⊗ γ) _ (⟦f⟧ : β ⊗ γ) ⟦g⟧ = ⟦f + g⟧ := rfl
@[simp] lemma neg_quot (f : free_abelian_group β γ) : @has_neg.neg (β ⊗ γ) _ (⟦f⟧ : β ⊗ γ) = ⟦-f⟧ := rfl

variables {α β γ}

def tprod : β → γ → β ⊗ γ :=
λ x y, ⟦finsupp.single (x, y) 1⟧

infix ` ⊗ₛ `:100 := tprod

variables {r r₁ r₂ : α} {x x₁ x₂ : β} {y y₁ y₂ : γ}

theorem tprod_unfold : x ⊗ₛ y = tprod x y := rfl

theorem tprod.is_bilinear_map : is_bilinear_map (@tprod α _ β γ _ _) :=
{ add_pair   := λ x y z, quotient.sound $ setoid.symm $
    ⟨[(finsupp.single (x, z) 1 +
         finsupp.single (y, z) 1 -
         finsupp.single (x + y, z) 1 : free_abelian_group β γ)],
     λ u hu, or.inr $ or.inl ⟨x, y, z, 1, list.eq_of_mem_singleton hu⟩,
     list.sum_singleton⟩,
  pair_add   := λ x y z, quotient.sound $ setoid.symm $
    ⟨[(finsupp.single (x, y) 1 +
         finsupp.single (x, z) 1 -
         finsupp.single (x, y + z) 1 : free_abelian_group β γ)],
     λ u hu, or.inl ⟨x, y, z, 1, list.eq_of_mem_singleton hu⟩,
     list.sum_singleton⟩,
  smul_pair  := λ r x y, quotient.sound $ setoid.symm $
    begin
      simp [relators.smul_aux],
      rw finsupp.sum_single_index,
      exact finsupp.single_zero
    end,
  pair_smul := λ r x y, quotient.sound $ setoid.symm $
    begin
      simp [relators.smul_aux],
      rw finsupp.sum_single_index,
      unfold prod.fst,
      unfold prod.snd,
      existsi ([(finsupp.single (r • x, y) 1 -
        finsupp.single (x, r • y) 1 : free_abelian_group β γ)]),
      split,
      { intros z hz,
        rw list.mem_singleton at hz,
        rw hz,
        from or.inr (or.inr ⟨r, x, y, 1, by simp [relators.smul_trans]⟩) },
      simp [list.sum_singleton],
      { rw finsupp.single_zero,
        refl }
    end }

@[simp] lemma add_tprod : (x₁ + x₂) ⊗ₛ y = x₁ ⊗ₛ y + x₂ ⊗ₛ y :=
tprod.is_bilinear_map.add_pair x₁ x₂ y

@[simp] lemma tprod_add : x ⊗ₛ (y₁ + y₂) = x ⊗ₛ y₁ + x ⊗ₛ y₂ :=
tprod.is_bilinear_map.pair_add x y₁ y₂

@[simp] lemma smul_tprod : (r • x) ⊗ₛ y = r • x ⊗ₛ y :=
tprod.is_bilinear_map.smul_pair r x y

@[simp] lemma tprod_smul : x ⊗ₛ (r • y) = r • x ⊗ₛ y :=
tprod.is_bilinear_map.pair_smul r x y

@[simp] lemma zero_tprod : (0:β) ⊗ₛ y = 0 :=
tprod.is_bilinear_map.zero_pair y

@[simp] lemma tprod_zero {x : β} : x ⊗ₛ (0:γ) = 0 :=
tprod.is_bilinear_map.pair_zero x

namespace universal_property

variables {β γ α₁}
variables {f : β → γ → α₁} (hf : is_bilinear_map f)
include β γ α₁ hf

def factor_aux : free_abelian_group β γ → α₁ :=
λ g : free_abelian_group β γ, (g.sum (λ z n, n • (f z.fst z.snd)))

theorem factor_equiv : ∀ g₁ g₂ : free_abelian_group β γ, g₁ ≈ g₂ → factor_aux hf g₁ = factor_aux hf g₂ :=
λ g₁ g₂ ⟨L, hL, hgL⟩,
begin
  clear _fun_match _x,
  induction L generalizing hgL hL g₂ g₁,
  { simp at hgL,
    replace hgL := hgL.symm,
    rw add_neg_eq_zero at hgL,
    rw hgL },
  { specialize L_ih L_tl.sum 0,
    specialize L_ih (λ x hx, hL x (list.mem_cons_of_mem L_hd hx)),
    specialize L_ih (sub_zero _).symm,
    rw ← sub_eq_zero,
    unfold factor_aux at L_ih ⊢,
    rw ← finsupp.sum_sub_index,
    rw ← hgL,
    rw @list.sum_cons _ _ L_tl,
    rw finsupp.sum_add_index,
    rw L_ih,
    rw sum_zero_index',
    specialize hL L_hd,
    specialize hL (or.inl rfl),
    rcases hL with h | h | h,
    { rcases h with ⟨x, y₁, y₂, n, h⟩,
      rw h,
      unfold relators.pair_add,
      rw finsupp.sum_sub_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw ← smul_add,
      rw ← smul_sub,
      rw hf.pair_add,
      simp,
      { dsimp, rw zero_smul },
      { dsimp, rw zero_smul },
      { dsimp, rw zero_smul },
      { intros, dsimp, rw zero_smul },
      { intros, simp, rw add_smul },
      { intros, simp [add_smul] } },
    { rcases h with ⟨x₁, x₂, y, n, h⟩,
      rw h,
      unfold relators.add_pair,
      rw finsupp.sum_sub_index,
      rw finsupp.sum_add_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw ← smul_add,
      rw ← smul_sub,
      rw hf.add_pair,
      simp,
      { dsimp, rw zero_smul },
      { dsimp, rw zero_smul },
      { dsimp, rw zero_smul },
      { intros, dsimp, rw zero_smul },
      { intros, simp, rw add_smul },
      { intros, simp [add_smul] } },
    { rcases h with ⟨r, x, y, n, h⟩,
      rw h,
      unfold relators.smul_trans,
      rw finsupp.sum_sub_index,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      rw ← smul_sub,
      rw hf.smul_pair,
      rw hf.pair_smul,
      simp,
      { dsimp, rw zero_smul },
      { dsimp, rw zero_smul },
      { intros, simp [add_smul] } },
    { intros, dsimp, rw zero_smul },
    { intros, simp, rw add_smul },
    { intros, simp [add_smul] } }
end

def factor : β ⊗ γ → α₁ :=
quotient.lift (factor_aux hf) (factor_equiv hf)

theorem factor_add : ∀ g₁ g₂ : β ⊗ γ, factor hf (g₁ + g₂) = factor hf g₁ + factor hf g₂ :=
λ x y, quotient.induction_on₂ x y
begin
  intros m n,
  simp [universal_property.factor],
  simp [universal_property.factor_aux],
  rw finsupp.sum_add_index,
  { intros, dsimp, rw zero_smul },
  { intros, simp [add_smul] }
end

theorem factor_smul : ∀ (r : α) (g : β ⊗ γ), factor hf (r • g) = r • factor hf g :=
λ r x, quotient.induction_on x
begin
  intros m,
  simp [has_scalar.smul, smul, relators.smul_aux],
  rcases structural_theorem β γ m with ⟨S, hS, hSm⟩,
  rw ← hSm,
  revert m hS hSm,
  apply finset.induction_on S,
  { intros m hS hSm,
    unfold universal_property.factor,
    unfold universal_property.factor_aux,
    simp [finsupp.sum_zero_index],
    rw sum_zero_index,
    rw sum_zero_index',
    simp },
  { intros n T hnT ih m hS hSm,
    unfold universal_property.factor,
    unfold universal_property.factor_aux,
    simp,
    specialize ih (finset.sum T id),
    specialize ih (λ g hg, hS g (finset.mem_insert_of_mem hg)),
    specialize ih rfl,
    unfold universal_property.factor at ih,
    unfold universal_property.factor_aux at ih,
    simp at ih,
    rw finset.sum_insert,
    rw finsupp.sum_add_index,
    rw finsupp.sum_add_index,
    rw finsupp.sum_add_index,
    rw ih,
    specialize hS n (finset.mem_insert_self n T),
    rcases hS with ⟨x', y', n', H', hn'⟩,
    rw hn',
    rw finsupp.sum_single_index,
    rw finsupp.sum_single_index,
    rw finsupp.sum_single_index,
    rw hf.smul_pair,
    simp [smul_add, smul_smul, mul_comm],
    { dsimp, rw zero_smul },
    { dsimp, rw zero_smul },
    { rw finsupp.single_zero, refl },
    { intros, dsimp, rw zero_smul },
    { intros, simp [add_smul] },
    { intros, dsimp, rw zero_smul },
    { intros, simp [add_smul] },
    { intros, rw finsupp.single_zero, refl },
    { intros, rw finsupp.single_add },
    { exact hnT } }
end

theorem factor_linear : is_linear_map (factor hf) :=
{ add  := factor_add hf,
  smul := factor_smul hf }

theorem factor_commutes : ∀ x y, factor hf (x ⊗ₛ y) = f x y :=
begin
  intros,
  simp [function.comp, tprod, factor, factor_aux],
  simp [finsupp.sum_single_index]
end

theorem factor_unique (h : β ⊗ γ → α₁) (H : is_linear_map h)
  (hh : ∀ x y, h (x ⊗ₛ y) = f x y) :
  h = factor hf :=
begin
  apply funext,
  intro x,
  apply quotient.induction_on x,
  intro y,
  unfold universal_property.factor,
  unfold universal_property.factor_aux,
  simp,
  rcases structural_theorem β γ y with ⟨S, hS, hSy⟩,
  revert hSy hS y,
  apply finset.induction_on S,
  { intros y hS hSy,
    rw ← hSy,
    rw finset.sum_empty,
    rw sum_zero_index',
    exact H.zero },
  { intros n T hnT ih y hS hSy,
    rw ← hSy,
    rw finset.sum_insert,
    rw ← add_quot,
    rw H.add,
    rw finsupp.sum_add_index,
    rw id.def,
    specialize ih (T.sum id),
    specialize ih (λ z hz, hS z (finset.mem_insert_of_mem hz)),
    specialize ih rfl,
    rw ih,
    specialize hS n,
    specialize hS (finset.mem_insert_self n T),
    rcases hS with ⟨x', y', n', H', hn'⟩,
    rw hn',
    rw finsupp.sum_single_index,
    specialize hh x' y',
    simp [function.comp, tprod] at hh,
    clear H' hn',
    suffices : h ⟦finsupp.single (x', y') n'⟧ = n' • (f x' y'),
    { rw this },
    cases n',
    { induction n' with n' ih',
      { rw int.of_nat_zero,
        rw finsupp.single_zero,
        dsimp, rw zero_smul,
        exact H.zero },
      { rw int.of_nat_succ,
        rw finsupp.single_add,
        rw ← add_quot,
        rw H.add,
        rw [ih', hh],
        simp, rw add_smul,
        rw one_smul } },
    { induction n' with n' ih',
      { rw int.neg_succ_of_nat_eq,
        rw finsupp.single_neg,
        simp,
        rw ← neg_quot,
        rw H.neg,
        rw hh },
      { rw int.neg_succ_of_nat_coe,
        rw int.neg_succ_of_nat_eq at ih',
        rw int.coe_nat_add,
        rw finsupp.single_neg at ih' ⊢,
        rw ← neg_quot at ih' ⊢,
        rw H.neg at ih' ⊢,
        rw nat.succ_eq_add_one,
        rw finsupp.single_add,
        rw ← add_quot,
        rw H.add,
        rw neg_add,
        rw int.coe_nat_add,
        rw int.coe_nat_eq 1,
        rw int.of_nat_one,
        rw ih',
        rw hh,
        simp [add_smul] } },
    { dsimp, rw zero_smul },
    { intros, dsimp, rw zero_smul },
    { intros, simp [add_smul] },
    { exact hnT } }
end

end universal_property

instance universal_property {f : β → γ → α₁} (hf : is_bilinear_map f) :
  type_singleton { h : β ⊗ γ → α₁ // ∃ (H : is_linear_map h), ∀ x y, h (x ⊗ₛ y) = f x y } :=
{ default := ⟨universal_property.factor hf,
    universal_property.factor_linear hf,
    universal_property.factor_commutes hf⟩,
  unique  := λ ⟨h, H, hh⟩, subtype.eq $
    universal_property.factor_unique hf h H hh }

variables {β γ α₁}
protected theorem ext {f g : β ⊗ γ → α₁} (hf : is_linear_map f) (hg : is_linear_map g)
  (h : ∀ x y, f (x ⊗ₛ y) = g (x ⊗ₛ y)) (z : β ⊗ γ) : f z = g z :=
have h1 : _ := universal_property.factor_unique
  (tprod.is_bilinear_map.comp hg)
  f hf h,
have h2 : _ := universal_property.factor_unique
  (tprod.is_bilinear_map.comp hg)
  g hg (λ x y, rfl),
congr_fun (h1.trans h2.symm) z

variables (β γ)

protected def id : β ⊗ α ≃ₘ β :=
let hba1 : β → α → β := λ x y, y • x in
have hba2 : is_bilinear_map hba1,
by refine {..}; intros; simp [hba1, smul_add, add_smul, smul_smul, mul_comm, mul_left_comm],
let hba3 : β ⊗ α → β := universal_property.factor hba2 in
have hba4 : _ := universal_property.factor_linear hba2,
have hba5 : _ := universal_property.factor_commutes hba2,
let hb1 : β → β ⊗ α := λ x, x ⊗ₛ 1 in
have hb2 : is_linear_map hb1, from
{ add  := λ x y, add_tprod,
  smul := λ r x, smul_tprod },
have hbb1 : ∀ (x : β) (y : α), hb1 (hba3 (x ⊗ₛ y)) = x ⊗ₛ y,
from λ x y, calc
        hb1 (hba3 (x ⊗ₛ y))
      = (y • x) ⊗ₛ 1 : congr_arg hb1 (hba5 _ _)
  ... = y • x ⊗ₛ 1 : smul_tprod
  ... = x ⊗ₛ (y • 1) : eq.symm $ tprod_smul
  ... = x ⊗ₛ y : by simp,
{ to_fun    := hba3,
  inv_fun   := hb1,
  left_inv  := tensor_product.ext (hb2.comp hba4) is_linear_map.id hbb1,
  right_inv := λ x, by simp *,
  linear    := hba4 }

protected def comm : β ⊗ γ ≃ₘ γ ⊗ β :=
let hbg1 : β → γ → γ ⊗ β := λ x y, y ⊗ₛ x in
have hbg2 : is_bilinear_map hbg1, from
{ add_pair  := λ x y z, tprod_add,
  pair_add  := λ x y z, add_tprod,
  smul_pair := λ r x y, tprod_smul,
  pair_smul := λ r x y, smul_tprod },
let hbg3 : β ⊗ γ → γ ⊗ β := universal_property.factor hbg2 in
have hbg4 : _ := universal_property.factor_linear hbg2,
have hbg5 : _ := universal_property.factor_commutes hbg2,
let hgb1 : γ → β → β ⊗ γ := λ y x , x ⊗ₛ y in
have hgb2 : is_bilinear_map hgb1, from
{ add_pair  := λ x y z, tprod_add,
  pair_add  := λ x y z, add_tprod,
  smul_pair := λ r x y, tprod_smul,
  pair_smul := λ r x y, smul_tprod },
let hgb3 : γ ⊗ β → β ⊗ γ := universal_property.factor hgb2 in
have hgb4 : _ := universal_property.factor_linear hgb2,
have hgb5 : _ := universal_property.factor_commutes hgb2,
have hbb1 : ∀ x y, (hgb3 ∘ hbg3) (x ⊗ₛ y) = x ⊗ₛ y,
from λ x y, by simp [function.comp, *],
have hbb2 : is_linear_map (hgb3 ∘ hbg3) := hgb4.comp hbg4,
have hbb3 : _ := tensor_product.ext hbb2 is_linear_map.id hbb1,
have hgg1 : ∀ y x, (hbg3 ∘ hgb3) (y ⊗ₛ x) = y ⊗ₛ x,
from λ x y, by simp [function.comp, *],
have hgg2 : is_linear_map (hbg3 ∘ hgb3) := hbg4.comp hgb4,
have hgg3 : _ := tensor_product.ext hgg2 is_linear_map.id hgg1,
{ to_fun    := hbg3,
  inv_fun   := hgb3,
  left_inv  := hbb3,
  right_inv := hgg3,
  linear    := hbg4 }

protected def prod_tensor : (β × γ) ⊗ α₁ ≃ₘ β ⊗ α₁ × γ ⊗ α₁ :=
let ha1 : β × γ → α₁ → β ⊗ α₁ × γ ⊗ α₁ :=
  λ z r, (z.fst ⊗ₛ r, z.snd ⊗ₛ r) in
have ha2 : is_bilinear_map ha1, from
{ add_pair  := λ x y z, prod.ext_iff.2 ⟨add_tprod, add_tprod⟩,
  pair_add  := λ x y z, prod.ext_iff.2 ⟨tprod_add, tprod_add⟩,
  smul_pair := λ r x y, prod.ext_iff.2 ⟨smul_tprod, smul_tprod⟩ ,
  pair_smul := λ r x y, prod.ext_iff.2 ⟨tprod_smul, tprod_smul⟩ },
let ha3 : (β × γ) ⊗ α₁ → β ⊗ α₁ × γ ⊗ α₁ :=
  universal_property.factor ha2 in
have ha4 : _ := universal_property.factor_linear ha2,
have ha5 : _ := universal_property.factor_commutes ha2,
let hb1 : β → α₁ → (β × γ) ⊗ α₁ :=
  λ x r, (x, 0) ⊗ₛ r in
have hb2 : is_bilinear_map hb1, from
{ add_pair  := λ x y z, calc
          (x + y, (0:γ)) ⊗ₛ z
        = (x + y, 0 + 0) ⊗ₛ z : congr_arg (λ r, (x + y, r) ⊗ₛ z) (zero_add 0).symm
    ... = ((x, 0) + (y, 0)) ⊗ₛ z : rfl
    ... = (x, 0) ⊗ₛ z + (y, 0) ⊗ₛ z : add_tprod,
  pair_add  := λ x y z, tprod_add,
  smul_pair := λ r x y, calc
          (r • x, (0:γ)) ⊗ₛ y
        = (r • (x, 0)) ⊗ₛ y : by simp only [prod.smul_prod, smul_zero]
    ... = r • (x, 0) ⊗ₛ y : smul_tprod,
  pair_smul := λ r x y, tprod_smul },
let hb3 : β ⊗ α₁ → (β × γ) ⊗ α₁ :=
  universal_property.factor hb2 in
have hb4 : _ := universal_property.factor_linear hb2,
have hb5 : _ := universal_property.factor_commutes hb2,
have hb6 : ∀ x, ha3 (hb3 x) = prod.inl x := tensor_product.ext (ha4.comp hb4) prod.is_linear_map_prod_inl $ λ x y, calc
          ha3 (hb3 (x ⊗ₛ y))
        = ha3 ((x, 0) ⊗ₛ y) : congr_arg ha3 (hb5 x y)
    ... = (x ⊗ₛ y, 0 ⊗ₛ y) : ha5 (x, 0) y
    ... = (x ⊗ₛ y, 0) : congr_arg (λ z, (x ⊗ₛ y, z)) zero_tprod,
let hc1 : γ → α₁ → (β × γ) ⊗ α₁ :=
  λ x r, (0, x) ⊗ₛ r in
have hc2 : is_bilinear_map hc1, from
{ add_pair   := λ x y z, calc
          ((0:β), x + y) ⊗ₛ z
        = (0 + 0, x + y) ⊗ₛ z : congr_arg (λ r, (r, x + y) ⊗ₛ z) (zero_add 0).symm
    ... = ((0, x) + (0, y)) ⊗ₛ z : rfl
    ... = (0, x) ⊗ₛ z + (0, y) ⊗ₛ z : add_tprod,
  pair_add   := λ x y z, tprod_add,
  smul_pair := λ r x y, calc
          ((0:β), r • x) ⊗ₛ y
        = (r • (0, x)) ⊗ₛ y : by simp only [prod.smul_prod, smul_zero]
    ... = r • (0, x) ⊗ₛ y : smul_tprod,
  pair_smul := λ r x y, tprod_smul },
let hc3 : γ ⊗ α₁ → (β × γ) ⊗ α₁ :=
  universal_property.factor hc2 in
have hc4 : _ := universal_property.factor_linear hc2,
have hc5 : _ := universal_property.factor_commutes hc2,
have hc6 : ∀ y, ha3 (hc3 y) = prod.inr y := tensor_product.ext (ha4.comp hc4) prod.is_linear_map_prod_inr $ λ x y, calc
          ha3 (hc3 (x ⊗ₛ y))
        = ha3 ((0, x) ⊗ₛ y) : congr_arg ha3 (hc5 x y)
    ... = (0 ⊗ₛ y, x ⊗ₛ y) : ha5 (0, x) y
    ... = (0, x ⊗ₛ y) : congr_arg (λ z, (z, x ⊗ₛ y)) zero_tprod,
let hd1 : β ⊗ α₁ × γ ⊗ α₁ → (β × γ) ⊗ α₁ :=
  λ z, hb3 z.fst + hc3 z.snd in
have hd2 : is_linear_map hd1, from
{ add  := λ x y, calc
          hb3 (x + y).fst + hc3 (x + y).snd
        = hb3 (x.fst + y.fst) + hc3 (x.snd + y.snd) : rfl
    ... = (hb3 x.fst + hb3 y.fst) + hc3 (x.snd + y.snd) : congr_arg (λ z, z + hc3 (x.snd + y.snd)) (hb4.add x.fst y.fst)
    ... = (hb3 x.fst + hb3 y.fst) + (hc3 x.snd + hc3 y.snd) : congr_arg (λ z, (hb3 x.fst + hb3 y.fst) + z) (hc4.add x.snd y.snd)
    ... = hb3 x.fst + (hb3 y.fst + (hc3 x.snd + hc3 y.snd)) : add_assoc _ _ _
    ... = hb3 x.fst + ((hc3 x.snd + hc3 y.snd) + hb3 y.fst) : congr_arg _ (add_comm _ _)
    ... = hb3 x.fst + (hc3 x.snd + (hc3 y.snd + hb3 y.fst)) : congr_arg _ (add_assoc _ _ _)
    ... = hb3 x.fst + (hc3 x.snd + (hb3 y.fst + hc3 y.snd)) : by have := congr_arg (λ z, hb3 x.fst + (hc3 x.snd + z)) (add_comm (hc3 y.snd) (hb3 y.fst)); dsimp at this; exact this
    ... = (hb3 x.fst + hc3 x.snd) + (hb3 y.fst + hc3 y.snd) : eq.symm $ add_assoc _ _ _,
  smul := λ r x, calc
          hb3 (r • x.fst) + hc3 (r • x.snd)
        = hb3 (r • x.fst) + r • (hc3 x.snd) : congr_arg _ (hc4.smul r x.snd)
    ... = r • (hb3 x.fst) + r • (hc3 x.snd) : congr_arg (λ z, z + r • (hc3 x.snd)) (hb4.smul r x.fst)
    ... = r • (hb3 x.fst + hc3 x.snd) : eq.symm $ @smul_add _ _ _ _ r (hb3 x.fst) (hc3 x.snd)
    ... = r • hd1 x : rfl },
have h1 : is_linear_map (hd1 ∘ ha3), from hd2.comp ha4,
have h2 : _ := tensor_product.ext h1 is_linear_map.id (λ x y, by simp [function.comp, *, add_tprod.symm]),
have h3 : ∀ z, (ha3 ∘ hd1) z = id z, from λ z, calc
        ha3 (hd1 z)
      = ha3 (hb3 z.fst + hc3 z.snd) : rfl
  ... = ha3 (hb3 z.fst) + ha3 (hc3 z.snd) : ha4.add _ _
  ... = prod.inl z.fst + prod.inr z.snd : by rw [hb6, hc6]
  ... = (z.fst + 0, 0 + z.snd) : rfl
  ... = z : by cases z; simp [prod.inl, prod.inr],
{ to_fun    := ha3,
  inv_fun   := hd1,
  left_inv  := h2,
  right_inv := h3,
  linear    := ha4 }

protected def assoc : (β ⊗ γ) ⊗ α₁ ≃ₘ β ⊗ (γ ⊗ α₁) :=
let ha1 (z : α₁) : β → γ → β ⊗ (γ ⊗ α₁) :=
  λ x y, x ⊗ₛ (y ⊗ₛ z) in
have ha2 : Π (z : α₁), is_bilinear_map (ha1 z), from λ z,
{ add_pair  := λ m n k, add_tprod,
  pair_add  := λ m n k, calc
          m ⊗ₛ ((n + k) ⊗ₛ z)
        = m ⊗ₛ (n ⊗ₛ z + k ⊗ₛ z) : congr_arg (λ b, m ⊗ₛ b) add_tprod
    ... = m ⊗ₛ (n ⊗ₛ z) + m ⊗ₛ (k ⊗ₛ z) : tprod_add,
  smul_pair := λ r m n, smul_tprod,
  pair_smul := λ r m n, calc
          m ⊗ₛ ((r • n) ⊗ₛ z)
        = m ⊗ₛ (r • n ⊗ₛ z) : congr_arg _ smul_tprod
    ... = r • m ⊗ₛ (n ⊗ₛ z) : tprod_smul },
let ha3 : β ⊗ γ → α₁ → β ⊗ (γ ⊗ α₁) :=
  λ xy z, universal_property.factor (ha2 z) xy in
have ha4 : _ := λ z, universal_property.factor_linear (ha2 z),
have ha5 : _ := λ z, universal_property.factor_commutes (ha2 z),
have ha6 : is_bilinear_map ha3, from
{ add_pair  := λ m n k, (ha4 k).add m n,
  pair_add  := λ m n k, (tensor_product.ext (ha4 $ n + k) ((ha4 n).map_add (ha4 k)) $ λ x y, calc
            ha3 (x ⊗ₛ y) (n + k)
          = x ⊗ₛ (y ⊗ₛ (n + k)) : ha5 (n + k) x y
      ... = x ⊗ₛ (y ⊗ₛ n + y ⊗ₛ k) : congr_arg ((⊗ₛ) x) tprod_add
      ... = x ⊗ₛ (y ⊗ₛ n) + x ⊗ₛ (y ⊗ₛ k) : tprod_add
      ... = x ⊗ₛ (y ⊗ₛ n) + ha3 (x ⊗ₛ y) k : congr_arg (λ b, x ⊗ₛ (y ⊗ₛ n) + b) (ha5 k _ _).symm
      ... = ha3 (x ⊗ₛ y) n + ha3 (x ⊗ₛ y) k : congr_arg (λ b, b + ha3 (x ⊗ₛ y) k) (ha5 n _ _).symm)
    m,
  smul_pair := λ r x y, (ha4 y).smul r x,
  pair_smul := λ r x y, (tensor_product.ext (ha4 $ r • y) (ha4 y).map_smul_right $ λ m n, calc
            ha3 (m ⊗ₛ n) (r • y)
          = m ⊗ₛ (n ⊗ₛ (r • y)) : ha5 (r • y) m n
      ... = m ⊗ₛ (r • n ⊗ₛ y) : congr_arg _ tprod_smul
      ... = r • m ⊗ₛ (n ⊗ₛ y) : tprod_smul
      ... = r • ha3 (m ⊗ₛ n) y : congr_arg _ (ha5 y m n).symm)
    x },
let ha7 : (β ⊗ γ) ⊗ α₁ → β ⊗ (γ ⊗ α₁) :=
  universal_property.factor ha6 in
have ha8 : _ := universal_property.factor_linear ha6,
have ha9 : _ := universal_property.factor_commutes ha6,
let hb1 (x : β) : γ → α₁ → (β ⊗ γ) ⊗ α₁ :=
  λ y z, (x ⊗ₛ y) ⊗ₛ z in
have hb2 : Π (x : β), is_bilinear_map (hb1 x), from λ x,
{ add_pair  := λ m n k, calc
          (x ⊗ₛ (m + n)) ⊗ₛ k
        = (x ⊗ₛ m + x ⊗ₛ n) ⊗ₛ k : congr_arg (λ z, z ⊗ₛ k) tprod_add
    ... = (x ⊗ₛ m) ⊗ₛ k + (x ⊗ₛ n) ⊗ₛ k : add_tprod,
  pair_add  := λ m n k, tprod_add,
  smul_pair := λ r m n, calc
          (x ⊗ₛ (r • m)) ⊗ₛ n
        = (r • x ⊗ₛ m) ⊗ₛ n : congr_arg (λ z, z ⊗ₛ n) tprod_smul
    ... = r • (x ⊗ₛ m) ⊗ₛ n : smul_tprod,
  pair_smul := λ r m n, tprod_smul },
let hb3 : β → γ ⊗ α₁ → (β ⊗ γ) ⊗ α₁ :=
  λ x, universal_property.factor (hb2 x) in
have hb4 : _ := λ x, universal_property.factor_linear (hb2 x),
have hb5 : _ := λ x, universal_property.factor_commutes (hb2 x),
have hb6 : is_bilinear_map hb3, from
{ add_pair  := λ m n k, (tensor_product.ext (hb4 $ m + n) ((hb4 m).map_add (hb4 n)) $ λ x y, calc
            hb3 (m + n) (x ⊗ₛ y)
          = ((m + n) ⊗ₛ x) ⊗ₛ y : (hb5 $ m + n) x y
      ... = (m ⊗ₛ x + n ⊗ₛ x) ⊗ₛ y : congr_arg (λ z, z ⊗ₛ y) add_tprod
      ... = (m ⊗ₛ x) ⊗ₛ y + (n ⊗ₛ x) ⊗ₛ y : add_tprod
      ... = (m ⊗ₛ x) ⊗ₛ y + hb3 n (x ⊗ₛ y) : congr_arg _ ((hb5 n) x y).symm
      ... = hb3 m (x ⊗ₛ y) + hb3 n (x ⊗ₛ y) : congr_arg (λ z, z + hb3 n (x ⊗ₛ y)) ((hb5 m) x y).symm)
    k,
  pair_add  := λ m n k, (hb4 m).add n k,
  smul_pair := λ r x y, (tensor_product.ext (hb4 $ r • x) (hb4 x).map_smul_right $ λ m n, calc
            hb3 (r • x) (m ⊗ₛ n)
          = ((r • x) ⊗ₛ m) ⊗ₛ n : (hb5 $ r • x) m n
      ... = (r • x ⊗ₛ m) ⊗ₛ n : congr_arg (λ z, z ⊗ₛ n) smul_tprod
      ... = r • (x ⊗ₛ m) ⊗ₛ n : smul_tprod
      ... = r • hb3 x (m ⊗ₛ n) : congr_arg _ ((hb5 $ x) m n).symm)
    y,
  pair_smul := λ r x y, (hb4 x).smul r y },
let hb7 : β ⊗ (γ ⊗ α₁) → (β ⊗ γ) ⊗ α₁ :=
  universal_property.factor hb6 in
have hb8 : _ := universal_property.factor_linear hb6,
have hb9 : _ := universal_property.factor_commutes hb6,
have hc1 : _ := λ z, tensor_product.ext (hb8.comp $ ha6.linear_pair z) (tprod.is_bilinear_map.linear_pair z) $ λ x y, calc
        hb7 (ha3 (x ⊗ₛ y) z)
      = hb7 (x ⊗ₛ (y ⊗ₛ z)) : congr_arg hb7 (ha5 z x y)
  ... = hb3 x (y ⊗ₛ z) : hb9 x (y ⊗ₛ z)
  ... = (x ⊗ₛ y) ⊗ₛ z : hb5 x y z,
have hc2 : _ := tensor_product.ext (hb8.comp ha8) is_linear_map.id $ λ xy z, calc
        hb7 (ha7 (xy ⊗ₛ z))
      = hb7 (ha3 xy z) : congr_arg hb7 (ha9 xy z)
  ... = xy ⊗ₛ z : hc1 z xy,
have hd1 : _ := λ x, tensor_product.ext (ha8.comp $ hb6.pair_linear x) (tprod.is_bilinear_map.pair_linear x) $ λ y z, calc
        ha7 (hb3 x (y ⊗ₛ z))
      = ha7 ((x ⊗ₛ y) ⊗ₛ z) : congr_arg ha7 (hb5 x y z)
  ... = ha3 (x ⊗ₛ y) z : ha9 (x ⊗ₛ y) z
  ... = x ⊗ₛ (y ⊗ₛ z) : ha5 z x y,
have hd2 : _ := tensor_product.ext (ha8.comp hb8) is_linear_map.id $ λ x yz, calc
        ha7 (hb7 (x ⊗ₛ yz))
      = ha7 (hb3 x yz) : congr_arg ha7 (hb9 x yz)
  ... = x ⊗ₛ yz : hd1 x yz,
{ to_fun    := ha7,
  inv_fun   := hb7,
  left_inv  := hc2,
  right_inv := hd2,
  linear    := ha8 }

variables {α β γ α₁ β₁ γ₁}
variables {f : β → γ} (hf : is_linear_map f)
variables {g : β₁ → γ₁} (hg : is_linear_map g)
include hf hg
def tprod_map : β ⊗ β₁ → γ ⊗ γ₁ :=
let h1 : β → β₁ → γ ⊗ γ₁ :=
  λ x y, f x ⊗ₛ g y in
have h2 : is_bilinear_map h1 :=
{ add_pair  := λ m n k, by simp [h1]; rw [hf.add, add_tprod],
  pair_add  := λ m n k, by simp [h1]; rw [hg.add, tprod_add],
  smul_pair := λ r m n, by simp [h1]; rw [hf.smul, smul_tprod],
  pair_smul := λ r m n, by simp [h1]; rw [hg.smul, tprod_smul] },
universal_property.factor h2

theorem tprod_map.linear : is_linear_map (tprod_map hf hg) :=
universal_property.factor_linear _

theorem tprod_map.commutes (x : β) (y : β₁) :
  tprod_map hf hg (x ⊗ₛ y) = f x ⊗ₛ g y :=
universal_property.factor_commutes
  (tprod_map._proof_1 hf hg) x y

end tensor_product

def is_ring_hom.to_module {α : Type u} {β : Type v}
  [comm_ring α] [comm_ring β]
  (f : α → β) [is_ring_hom f] : module α β :=
{ smul     := λ r x, f r * x,
  smul_add := λ r x y, by simp [mul_add],
  add_smul := λ r₁ r₂ x, by simp [is_ring_hom.map_add f, add_mul],
  mul_smul := λ r₁ r₂ x, by simp [is_ring_hom.map_mul f, mul_assoc],
  one_smul := λ x, by simp [is_ring_hom.map_one f] }