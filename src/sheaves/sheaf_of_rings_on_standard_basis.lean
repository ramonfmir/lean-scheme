import topology.opens
import sheaves.presheaf_of_rings_on_basis
import sheaves.presheaf_of_rings_extension
import sheaves.sheaf_on_standard_basis
import sheaves.sheaf_of_rings

open topological_space

universe u

variables {α : Type u} [T : topological_space α] 
variables {B : set (opens α)} {HB : opens.is_basis B}
variables (Bstd : opens.univ ∈ B ∧ ∀ {U V}, U ∈ B → V ∈ B → U ∩ V ∈ B)

#print sheaf_on_standard_basis.is_sheaf_on_standard_basis 
#print is_sheaf_on_basis
#check covering_standard_basis

-- Key part is to prove that is_sheaf_on_basis → is_sheaf_on_standard_basis

theorem extension_is_sheaf_of_rings 
(F : presheaf_of_rings_on_basis α HB) 
(HF : sheaf_on_standard_basis.is_sheaf_on_standard_basis Bstd F.to_presheaf_on_basis)
: is_sheaf_of_rings (F ᵣₑₓₜ Bstd) := 
begin
  show is_sheaf (F ᵣₑₓₜ Bstd).to_presheaf,
  apply extension_is_sheaf,
  intros U BU OC s Hinter,
  let OC' : covering_standard_basis B U 
    := { to_covering := OC.to_covering, BUis := OC.BUis },
  rcases (HF BU OC') with ⟨Hloc, Hglue⟩,
  have Hglue' := λ k, Hglue s,
  have : ∀ i j k, (F.to_presheaf_on_basis).res (OC.BUis i)
  -- have Hs : ∀ (i j),
  --   sheaf_on_standard_basis.res_to_inter_left Bstd (F.to_presheaf_on_basis) _ _ (s i) =
  --   sheaf_on_standard_basis.res_to_inter_right Bstd (F.to_presheaf_on_basis) _ _ (s j),
  --   intros i j,
  --   have := Hinter i j,
  --   dsimp,
  --   erw ←OC.Hintercov,
  end