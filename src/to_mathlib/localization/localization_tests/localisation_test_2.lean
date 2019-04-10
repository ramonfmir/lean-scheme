/-
  Second localization test. If e^2 = e then R[1/e] ≅ R[1/(1-e)]. 
-/

import to_mathlib.localization.localization_alt

-- By Kenny.

example {R : Type*} [comm_ring R] (e : R) (he : e * e = e) : localization_alt.is_localization (powers e) (ideal.quotient.mk (ideal.span {1-e})) :=
begin
  have H1 : ideal.quotient.mk (ideal.span {1 - e}) e = 1,
  { exact eq.symm (ideal.quotient.eq.2 $ ideal.subset_span $ or.inl rfl) },
  have H2 : (1 - e) * e = 0,
  { rw [sub_mul, he, one_mul, sub_self] },
  refine ⟨_, _, _⟩,
  { rintros ⟨_, n, rfl⟩, use 1,
    change ideal.quotient.mk _ (e^n * 1) = _,
    rw [mul_one, is_semiring_hom.map_pow (ideal.quotient.mk (ideal.span {1-e})) e n, H1, one_pow] },
  { rintro ⟨x⟩, use (1,x), exact one_mul _ },
  { ext x, split; intro hx,
    { replace hx := ideal.quotient.eq_zero_iff_mem.1 hx,
      replace hx := ideal.mem_span_singleton'.1 hx,
      refine ⟨⟨(x, ⟨e, 1, pow_one e⟩), _⟩, rfl⟩,
      cases hx with y hx, change x * e = 0, rw [← hx, mul_assoc, H2, mul_zero] },
    { rcases hx with ⟨⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩, rfl⟩, change x * e^n = 0 at hx,
      apply ideal.quotient.eq_zero_iff_mem.2,
      apply ideal.mem_span_singleton'.2,
      change ∃ a, a * (1-e) = x, induction n with n ih generalizing x,
      { rw [pow_zero, mul_one] at hx, subst hx, use 0, rw zero_mul },
      rw [pow_succ, ← mul_assoc] at hx, cases ih _ hx with y hy,
      use x + y, rw [add_mul, hy, ← mul_add, sub_add_cancel, mul_one] } },
end
