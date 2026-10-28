/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSixTwoRecovery.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSixTwoCounts

/-!
The exact coordinate-shape characterization of the six-two family.
Magnitude supports and recovered signs construct parameters for every lattice vector of this shape.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def SixTwoShape (x : IntegerCoordinates) : Prop :=
  (∀ i, x i = -6 ∨ x i = -2 ∨ x i = 0 ∨ x i = 2 ∨ x i = 6) ∧
  hammingNorm (halfResidue x 0) = 8 ∧ (evenMagnitudeSupport x 6).card = 1

theorem sixTwoFamily_shape (x : IntegerCoordinates) (hx : x ∈ sixTwoFamily) : SixTwoShape x := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨?_,?_,?_⟩
  · intro i
    simp only [sixTwoFamilyVector,sixTwoVector,signedSupport]
    split_ifs <;> simp
  · simp only [sixTwoFamilyVector,sixTwo_residue]
    simpa [hammingNorm,supportWord] using p.1.prop.2
  · simp only [sixTwoFamilyVector,sixTwo_support_six,Finset.card_singleton]

theorem sixTwoFamily_iff (x : IntegerCoordinates) :
    x ∈ sixTwoFamily ↔ x ∈ leech ∧ SixTwoShape x := by
  constructor
  · intro hx
    exact ⟨(sixTwoFamily_properties x hx).1,sixTwoFamily_shape x hx⟩
  · rintro ⟨hx,hshape⟩
    have hp (i : Omega) : x i % 2 = 0 := by
      rcases hshape.1 i with h | h | h | h | h <;> simp [h]
    have hc : halfResidue x 0 ∈ golay := by
      obtain ⟨m,(rfl | rfl),hh,hc,hs⟩ := (mem_leech x).mp hx
      · exact hc
      · have hh := hh ((0,0),0)
        have hp := hp ((0,0),0)
        omega
    let T := support (halfResidue x 0)
    have hTc : supportWord T ∈ golay := by
      have he : supportWord T = halfResidue x 0 := binarySupportEquiv.left_inv _
      rw [he]; exact hc
    have hTk : T.card = 8 := hshape.2.1
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hshape.2.2
    have haa : x a * x a = 36 := by
      have hm : a ∈ evenMagnitudeSupport x 6 := by rw [ha]; simp
      exact (Finset.mem_filter.mp hm).2
    have haT : a ∈ T := by
      rcases hshape.1 a with h | h | h | h | h <;>
        simp_all [T,support,halfResidue,integerReduction] <;> decide
    let s : T → Bit := fun i => if x i.val = 2 ∨ x i.val = 6 then 0 else 1
    have he : x = sixTwoVector T ⟨a,haT⟩ s := by
      funext i
      have hsix : x i * x i = 36 ↔ i = a := by
        have hh : (i ∈ evenMagnitudeSupport x 6) ↔ i = a := by rw [ha,Finset.mem_singleton]
        simpa [evenMagnitudeSupport] using hh
      rcases hshape.1 i with h | h | h | h | h <;>
        simp_all [sixTwoVector,signedSupport,s,T,support,halfResidue,integerReduction] <;> decide
    have hsign := (sixTwo_mem_iff T ⟨a,haT⟩ s hTc).mp (he ▸ hx)
    let p : SixTwoParameters := ⟨⟨T,hTc,hTk⟩,⟨a,haT⟩,⟨s,hsign⟩⟩
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,he.symm⟩

end Atlas.Lattices
