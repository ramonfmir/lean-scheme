import topology.basic
import sheaves.presheaf_of_rings
import sheaves.stalk_of_rings

universe u

section stalk_of_rings_is_ring

parameters {α : Type u} [topological_space α] 
parameters (F : presheaf_of_rings α) (x : α)

-- Zero.

private def stalk_of_rings_zero : stalk_of_rings F x := 
⟦{U := opens.univ, HxU := trivial, s:= 0}⟧

instance stalk_of_rings_has_zero : has_zero (stalk_of_rings F x) := 
{zero := stalk_of_rings_zero}

-- One.

-- private
def stalk_of_rings_one : stalk_of_rings F x := 
⟦{U := opens.univ, HxU := trivial, s:= 1}⟧

instance stalk_of_rings_has_one : has_one (stalk_of_rings F x) := 
{one := stalk_of_rings_one}

-- Add.

private def stalk_of_rings_add_aux : 
stalk.elem F.to_presheaf x → 
stalk.elem F.to_presheaf x → 
stalk F.to_presheaf x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
HxU := ⟨s.HxU, t.HxU⟩, 
s := F.res s.U _ (set.inter_subset_left _ _) s.s + 
     F.res t.U _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_add : has_add (stalk_of_rings F x) := 
{add := quotient.lift₂ (stalk_of_rings_add_aux) $
begin
    intros a1 a2 b1 b2 H1 H2, 
    let F' := F.to_presheaf,
    rcases H1 with ⟨U1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩,
    apply quotient.sound,
    use [U1 ∩ U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    have HresU1' : 
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res a1.U U1 HU1a1U) (a1.s))) =
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res b1.U U1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res a2.U U2 HU2a2U) (a2.s))) =
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res b2.U U2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf.Hcomp' F') },
    rw [HresU1', HresU2'],
end}

-- -- Mul. TODO: Basically the same as add, what can be done about this?

private def stalk_of_rings_mul_aux : 
stalk.elem F.to_presheaf x → 
stalk.elem F.to_presheaf x → 
stalk F.to_presheaf x :=
λ s t, 
⟦{U := s.U ∩ t.U, 
HxU := ⟨s.HxU, t.HxU⟩, 
s := F.res s.U _ (set.inter_subset_left _ _) s.s * 
     F.res t.U _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_mul : has_mul (stalk_of_rings F x) := 
{mul := quotient.lift₂ (stalk_of_rings_mul_aux) $ 
begin
    intros a1 a2 b1 b2 H1 H2, 
    let F' := F.to_presheaf,
    rcases H1 with ⟨U1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩,
    apply quotient.sound,
    use [U1 ∩ U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    have HresU1' : 
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res a1.U U1 HU1a1U) (a1.s))) =
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res b1.U U1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res a2.U U2 HU2a2U) (a2.s))) =
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res b2.U U2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf.Hcomp' F') },
    rw [HresU1', HresU2'],
end}

instance stalk_of_rings_is_ring : comm_ring (stalk_of_rings F x) := 
{   add := stalk_of_rings_has_add.add,
    add_assoc := sorry,
    zero := stalk_of_rings_zero,
    zero_add := sorry,
    add_zero := sorry,
    neg := sorry,
    add_left_neg := sorry,
    add_comm := sorry,
    mul := stalk_of_rings_has_mul.mul,
    mul_assoc := sorry,
    one := stalk_of_rings_one,
    one_mul := sorry,
    mul_one := sorry,
    left_distrib := sorry,
    right_distrib := sorry,
    mul_comm := sorry,
}

-- Neg.

-- private def stalk_sub_aux : 
-- stalk_on_basis.elem F.to_presheaf_on_basis x → 
-- stalk_on_basis F.to_presheaf_on_basis x :=
-- λ s, ⟦{U := s.U, BU := s.BU, Hx := s.Hx, s := -s.s}⟧

-- instance stalk_of_rings_has_neg : has_neg (stalk_of_rings_on_standard_basis F x) :=
-- {neg := quotient.lift (stalk_sub_aux F x) $ 
-- begin
--     intros a b H,
--     rcases H with ⟨U, ⟨BU, ⟨HxU, ⟨HUaU, HUbU, HresU⟩⟩⟩⟩,
--     apply quotient.sound,
--     use [U, BU, HxU, HUaU, HUbU],
--     repeat { rw @is_ring_hom.map_neg _ _ _ _ _ (F.res_is_ring_hom _ _ _) },
--     rw HresU,
-- end}

-- -- Mul. TODO: Basically the same as add, what can be done about this?

-- private def stalk_of_rings_mul_aux : 
-- stalk_on_basis.elem F.to_presheaf_on_basis x → 
-- stalk_on_basis.elem F.to_presheaf_on_basis x → 
-- stalk_on_basis F.to_presheaf_on_basis x :=
-- λ s t, 
-- ⟦{U := s.U ∩ t.U, 
-- BU := Bstandard.2 s.BU t.BU,
-- Hx := ⟨s.Hx, t.Hx⟩, 
-- s := F.res s.BU _ (set.inter_subset_left _ _) s.s * 
--      F.res t.BU _ (set.inter_subset_right _ _) t.s}⟧

-- instance stalk_of_rings_has_mul : has_mul (stalk_of_rings_on_standard_basis F x) := 
-- {mul := quotient.lift₂ (stalk_of_rings_mul_aux Bstandard F x) $ 
-- begin
--     intros a1 a2 b1 b2 H1 H2, 
--     let F' := F.to_presheaf_on_basis,
--     rcases H1 with ⟨U1, ⟨BU1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩⟩,
--     rcases H2 with ⟨U2, ⟨BU2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩⟩,
--     have BU1U2 := Bstandard.2 BU1 BU2,
--     apply quotient.sound,
--     use [U1 ∩ U2, BU1U2, ⟨HxU1, HxU2⟩],
--     use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
--     repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--     have HresU1' : 
--         (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res a1.BU BU1 HU1a1U) (a1.s))) =
--         (F'.res BU1 BU1U2 (set.inter_subset_left _ _) ((F'.res b1.BU BU1 HU1b1U) (b1.s)))
--     := by rw HresU1,
--     have HresU2' :
--         (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res a2.BU BU2 HU2a2U) (a2.s))) =
--         (F'.res BU2 BU1U2 (set.inter_subset_right _ _) ((F'.res b2.BU BU2 HU2b2U) (b2.s)))
--     := by rw HresU2,
--     repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU1' },
--     repeat { rw ←(presheaf_on_basis.Hcomp' F') at HresU2' },
--     repeat { rw ←(presheaf_on_basis.Hcomp' F') },
--     rw [HresU1', HresU2'],
-- end}

-- -- Stalks are rings.

-- instance stalk_of_rings_is_ring : comm_ring (stalk_of_rings_on_standard_basis F x) :=
-- {   add := (stalk_of_rings_has_add Bstandard F x).add,
--     add_assoc := 
--     begin
--         intros a b c,
--         refine quotient.induction_on₃ a b c _,
--         rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
--         have BUVW := Bstandard.2 (Bstandard.2 BU BV) BW,
--         have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
--         := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
--         apply quotient.sound,
--         use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩],
--         use [set.subset.refl _, HUVWsub],
--         dsimp,
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { erw ←presheaf_on_basis.Hcomp' },
--         rw add_assoc,
--     end,
--     zero := (stalk_of_rings_has_zero Bstandard F x).zero,
--     zero_add := 
--     begin
--         intros a,
--         refine quotient.induction_on a _,
--         rintros ⟨U, BU, HxU, sU⟩,
--         apply quotient.sound,
--         have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
--         use [U, BU, HxU, HUsub, set.subset.refl U],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
--         try { apply_instance },
--         rw zero_add,
--         refl,
--     end,
--     add_zero :=
--     begin
--         intros a,
--         refine quotient.induction_on a _,
--         rintros ⟨U, BU, HxU, sU⟩,
--         apply quotient.sound,
--         have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
--         use [U, BU, HxU, HUsub, set.subset.refl U],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         dsimp, -- TODO: Can I get rid of this???
--         erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
--         try { apply_instance },
--         rw add_zero,
--         refl,
--     end,
--     neg := has_neg.neg,
--     add_left_neg := 
--     begin
--         intros a,
--         refine quotient.induction_on a _,
--         rintros ⟨U, BU, HxU, sU⟩,
--         apply quotient.sound,
--         have HUUU : U ⊆ U ∩ U := λ x HxU, ⟨HxU, HxU⟩,
--         have HUuniv : U ⊆ opens.univ := λ x HxU, trivial,
--         use [U, BU, HxU, HUUU, HUuniv],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         erw (is_ring_hom.map_neg ((F.to_presheaf_on_basis).res _ _ _));
--         try { apply_instance },
--         rw add_left_neg,
--         erw (is_ring_hom.map_zero ((F.to_presheaf_on_basis).res _ _ _));
--         try { apply_instance },
--     end,
--     add_comm := 
--     begin
--         intros a b,
--         refine quotient.induction_on₂ a b _,
--         rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩,
--         apply quotient.sound,
--         have BUV : U ∩ V ∈ B := Bstandard.2 BU BV,
--         have HUVUV : U ∩ V ⊆ U ∩ V := λ x HxUV, HxUV,
--         have HUVVU : U ∩ V ⊆ V ∩ U := λ x ⟨HxU, HxV⟩, ⟨HxV, HxU⟩,
--         use [U ∩ V, BUV, ⟨HxU, HxV⟩, HUVUV, HUVVU],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         rw add_comm,
--     end,
--     mul := (stalk_of_rings_has_mul Bstandard F x).mul,
--     mul_assoc := 
--     begin
--         intros a b c,
--         refine quotient.induction_on₃ a b c _,
--         rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
--         have BUVW := Bstandard.2 (Bstandard.2 BU BV) BW,
--         have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
--         := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
--         apply quotient.sound,
--         use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩],
--         use [set.subset.refl _, HUVWsub],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         rw mul_assoc,
--     end,
--     one := (stalk_of_rings_has_one Bstandard F x).one,
--     one_mul := 
--     begin
--         intros a,
--         refine quotient.induction_on a _,
--         rintros ⟨U, BU, HxU, sU⟩,
--         apply quotient.sound,
--         have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
--         use [U, BU, HxU, HUsub, set.subset.refl U],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         erw (is_ring_hom.map_one ((F.to_presheaf_on_basis).res _ _ _));
--         try { apply_instance },
--         rw one_mul,
--         refl,
--     end,
--     mul_one := 
--     begin
--         intros a,
--         refine quotient.induction_on a _,
--         rintros ⟨U, BU, HxU, sU⟩,
--         apply quotient.sound,
--         have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
--         use [U, BU, HxU, HUsub, set.subset.refl U],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         dsimp, -- TODO: Same problem here..!!!
--         erw (is_ring_hom.map_one ((F.to_presheaf_on_basis).res _ _ _));
--         try { apply_instance },
--         rw mul_one,
--         refl,
--     end,
--     left_distrib := 
--     begin
--         intros a b c,
--         refine quotient.induction_on₃ a b c _,
--         rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
--         have BUVW := Bstandard.2 (Bstandard.2 BU BV) BW,
--         have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W) 
--         := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
--         have HUVWsub2 : U ∩ V ∩ W ⊆ U ∩ V ∩ (U ∩ W)
--         := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨⟨HxU, HxV⟩, ⟨HxU, HxW⟩⟩,
--         apply quotient.sound,
--         use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWsub, HUVWsub2],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         rw mul_add,
--     end,
--     right_distrib := 
--     begin
--         intros a b c,
--         refine quotient.induction_on₃ a b c _,
--         rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩ ⟨W, BW, HxW, sW⟩,
--         have BUVW := Bstandard.2 (Bstandard.2 BU BV) BW,
--         have HUVWrfl : U ∩ V ∩ W ⊆ U ∩ V ∩ W := λ x Hx, Hx,
--         have HUVWsub : U ∩ V ∩ W ⊆ U ∩ W ∩ (V ∩ W)
--         := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨⟨HxU, HxW⟩, ⟨HxV, HxW⟩⟩,
--         apply quotient.sound,
--         use [U ∩ V ∩ W, BUVW, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWrfl, HUVWsub],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw (F.res_is_ring_hom _ _ _).map_add },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         rw add_mul,
--     end,
--     mul_comm := 
--     begin
--         intros a b,
--         refine quotient.induction_on₂ a b _,
--         rintros ⟨U, BU, HxU, sU⟩ ⟨V, BV, HxV, sV⟩,
--         apply quotient.sound,
--         have BUV : U ∩ V ∈ B := Bstandard.2 BU BV,
--         have HUVUV : U ∩ V ⊆ U ∩ V := λ x HxUV, HxUV,
--         have HUVVU : U ∩ V ⊆ V ∩ U := λ x ⟨HxU, HxV⟩, ⟨HxV, HxU⟩,
--         use [U ∩ V, BUV, ⟨HxU, HxV⟩, HUVUV, HUVVU],
--         repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
--         repeat { rw ←presheaf_on_basis.Hcomp' },
--         rw mul_comm,
--     end,
-- }

end stalk_of_rings_is_ring