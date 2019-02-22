import ring_theory.ideals

noncomputable theory
local attribute [instance] classical.prop_decidable

universe u

open lattice

section maximal_ideal

parameters {α : Type u} [comm_ring α] (P : ideal α)

instance ideal.has_subset : has_subset (ideal α) :=
{ subset := λ I J, I.1 ⊆ J.1, }

instance ideal.partial_order : partial_order (ideal α) :=
{ le := λ I J, I ⊆ J,
  le_refl := λ I, by apply set.subset.refl,
  le_trans := λ I J K, by apply set.subset.trans,
  le_antisymm := λ I J HIJ HJI, ideal.ext $ λ x, ⟨λ Hx, HIJ Hx, λ Hx, HJI Hx⟩, }

instance find_maximal_ideal.partial_order : partial_order {S : ideal α // P ⊆ S} := 
begin
  apply subtype.partial_order _,
  apply_instance,
end

#print notation

instance find_maximal_ideal.inhabited : inhabited {S : ideal α // P ⊆ S} :=
⟨⟨P, set.subset.refl P⟩⟩

private theorem find_maximal_ideal.aux :
  ∃ (M : {S : ideal α // P ⊆ S}), ∀ x, M ≤ x → x = M :=
begin
  apply zorn.zorn_partial_order,
  intros c Hc,
  use [{y | ∃ S ∈ (subtype.val '' c), y ∈ S}],
  { -- zero
  },
  { -- add 
  },
  { -- mul 
  },
  { intros x Hx,
    have HS : ∀ {S}, S ∈ c → x ∈ (subtype.val S),
      rintros ⟨S, PS⟩ HSc,
      exact PS Hx,
    intros y Hy,
    simp at Hy,
    rcases Hy with ⟨z, Hz⟩,
    rw ←Hz,
    intros w Hw,
    simp at Hw,
    rcases Hw with ⟨Hw1, Hw2⟩,

    },
  {}
end

-- λ c x hx hc, ⟨⟨{y | ∃ S : {S : set α // P ⊆ S ∧ is_proper_ideal S}, S ∈ c ∧ y ∈ S.val},
--   λ z hz, ⟨x, hx, x.2.1 hz⟩,
--   { zero_ := ⟨x, hx, @@is_ideal.zero _ x.1 x.2.2.to_is_ideal⟩,
--     add_  := λ x y ⟨Sx, hxc, hx⟩ ⟨Sy, hyc, hy⟩,
--       or.cases_on (hc Sx Sy hxc hyc)
--         (λ hxy, ⟨Sy, hyc, @@is_ideal.add _ Sy.2.2.to_is_ideal (hxy hx) hy⟩)
--         (λ hyx, ⟨Sx, hxc, @@is_ideal.add _ Sx.2.2.to_is_ideal hx (hyx hy)⟩),
--     smul  := λ x y ⟨Sy, hyc, hy⟩,
--       ⟨Sy, hyc, @@is_ideal.mul_left _ Sy.2.2.to_is_ideal hy⟩,
--     ne_univ := λ h, by rw set.eq_univ_iff_forall at h;
--       rcases h 1 with ⟨S, hsc, hs⟩; apply S.2.2.ne_univ;
--       exact @@is_submodule.univ_of_one_mem _ S.1
--         S.2.2.to_is_ideal.to_is_submodule hs }⟩,
-- λ S hsc z hzs, ⟨S, hsc, hzs⟩⟩

def find_maximal_ideal : set α :=
(classical.some find_maximal_ideal.aux).1

theorem find_maximal_ideal.contains : P ⊆ find_maximal_ideal :=
(classical.some find_maximal_ideal.aux).2.1

def find_maximal_ideal.is_maximal_ideal :
  is_maximal_ideal find_maximal_ideal :=
let M : {S : set α // P ⊆ S ∧ is_proper_ideal S} :=
classical.some find_maximal_ideal.aux in
{ eq_or_univ_of_subset := λ T ht hmt, or_iff_not_imp_right.2 $
    λ h, congr_arg subtype.val $
    classical.some_spec find_maximal_ideal.aux
    ⟨T, set.subset.trans M.2.1 hmt, { ne_univ := h, .. ht }⟩ hmt,
  ..M.2.2 }

end maximal_ideal

section nonunits

parameters {α : Type u} [comm_ring α]
parameters (x : α) (hx : x ∈ nonunits α)

include hx

theorem ne_univ_of_nonunits : span ({x}:set α) ≠ set.univ :=
begin
  intro h,
  rw [span_singleton, set.eq_univ_iff_forall] at h,
  exact hx (h 1)
end

def find_maximal_ideal.of_nonunits : set α :=
@@find_maximal_ideal _ (span ({x}:set α))
{ ne_univ := ne_univ_of_nonunits }

theorem find_maximal_ideal.of_nonunits.mem :
  x ∈ find_maximal_ideal.of_nonunits :=
@@find_maximal_ideal.contains _ (span ({x}:set α))
{ ne_univ := ne_univ_of_nonunits } $
subset_span $ set.mem_singleton x

def find_maximal_ideal.of_nonunits.is_maximal_ideal :
  is_maximal_ideal find_maximal_ideal.of_nonunits :=
@@find_maximal_ideal.is_maximal_ideal _ (span ({x}:set α))
{ ne_univ := ne_univ_of_nonunits }

end nonunits

section zero_ne_one

parameters {α : Type u} [comm_ring α]
parameters (hzo : (0:α) ≠ 1)

include hzo

def find_maximal_ideal.of_zero_ne_one : set α :=
find_maximal_ideal.of_nonunits 0 $
λ ⟨y, h⟩, hzo $ by simpa using h

def find_maximal_ideal.of_zero_ne_one.is_maximal_ideal :
  is_maximal_ideal find_maximal_ideal.of_zero_ne_one :=
find_maximal_ideal.of_nonunits.is_maximal_ideal 0 $
λ ⟨y, h⟩, hzo $ by simpa using h

end zero_ne_one

end is_ideal