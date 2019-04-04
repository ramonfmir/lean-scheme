
--variable {R}

-----------------------------------------------------------

section structure_presheaf

-- Needed.

-- variables {U V : opens (Spec R)} (BU : U ∈ D_fs R) (BV : V ∈ D_fs R) (H : V ⊆ U)

-- lemma structure_presheaf.res.inverts_data
-- : inverts_data 
--     (powers (of (some BU))) 
--     (structure_presheaf_on_basis.res R BU BV H) :=
-- begin
--   rintros ⟨s, Hs⟩,
--   rcases (indefinite_description _ Hs) with ⟨n, Hn⟩,
--   rw ←@is_semiring_hom.map_pow R _ _ _ of (@is_ring_hom.is_semiring_hom _ _ _ _ of of.is_ring_hom) _ _ at Hn,
--   dsimp only [subtype.coe_mk],
--   rw ←Hn,
--   dsimp [structure_presheaf_on_basis.res],
--   rw is_localization_initial_comp,
--   have Hinv := inverts_data.of_basis_subset BU BV H ⟨(some BU)^n, ⟨n, rfl⟩⟩,
--   dsimp only [subtype.coe_mk] at Hinv,
--   rcases Hinv with ⟨inv, Hinv⟩,
--   let x := structure_presheaf.map_to R BV inv,
--   sorry,
  -- use x,
  -- have := 
  --   is_localization_initial_comp 
  --     (S V)
  --     (of : R → localization R ())
  --     (of.is_localization_data (S V))
  --     (of : R → localization R (powers (some BV)))
  --     (another.inverts_data R BV)
  --     (some BU ^ n),
  -- rw ←this,
  -- rw Hn,
  -- rw is_ring_hom.map_mul 
  --   (is_localization_initial 
  --     (powers (some BV))
  --     (of : R → localization R (powers (some BV)))
  --     (of.is_localization_data (powers (some BV)))
  --     (of : R → (structure_presheaf_on_basis R).F BV)
  --     (structure_presheaf.inverts_data BV)),
-- end

-- lemma structure_presheaf.res.has_denom_data
-- : has_denom_data 
--     (powers (of (some BU))) 
--     (structure_presheaf_on_basis.res R BU BV H) :=
-- begin
--   intros x,
--   sorry,
-- end

-- lemma structure_presheaf.res.ker_le
-- : ker (structure_presheaf_on_basis.res R BU BV H) ≤ submonoid_ann (powers (of (some BU))) :=
-- begin 
--   intros x Hx,
--   sorry,
-- end

-- lemma structure_presheaf.res.localization
-- : is_localization_data 
--     (powers (of (some BU))) 
--     (structure_presheaf_on_basis.res R BU BV H) :=
-- { inverts := structure_presheaf.res.inverts_data R BU BV H,
--   has_denom := structure_presheaf.res.has_denom_data R BU BV H, 
--   ker_le := structure_presheaf.res.ker_le R BU BV H }

end structure_presheaf