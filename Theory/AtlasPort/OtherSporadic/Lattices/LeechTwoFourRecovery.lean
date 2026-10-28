/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechTwoFourRecovery.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechTwoFourFamilies

/-!
Recovery of two-four vector parameters from coordinate magnitudes.
Canonical magnitude supports and signs prove the exact family-membership characterization.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def TwoFourShape (x : IntegerCoordinates) (k u : ℕ) : Prop :=
  (∀ i, x i = -4 ∨ x i = -2 ∨ x i = 0 ∨ x i = 2 ∨ x i = 4) ∧
  (evenMagnitudeSupport x 2).card = k ∧ (evenMagnitudeSupport x 4).card = u

def magnitudeSigns (x : IntegerCoordinates) (r : ℤ) : evenMagnitudeSupport x r → Bit :=
  fun i => if x i.val = r then 0 else 1

theorem magnitudeSupports_disjoint (x : IntegerCoordinates) :
    Disjoint (evenMagnitudeSupport x 2) (evenMagnitudeSupport x 4) := by
  apply Finset.disjoint_left.mpr
  intro i ht hu
  have ht : x i * x i = 2 * 2 := (Finset.mem_filter.mp ht).2
  have hu : x i * x i = 4 * 4 := (Finset.mem_filter.mp hu).2
  omega

theorem twoFour_reconstruction (x : IntegerCoordinates)
    (hx : ∀ i, x i = -4 ∨ x i = -2 ∨ x i = 0 ∨ x i = 2 ∨ x i = 4) :
    x = twoFourVector (evenMagnitudeSupport x 2) (evenMagnitudeSupport x 4)
      (magnitudeSigns x 2) (magnitudeSigns x 4) := by
  funext i
  rcases hx i with h | h | h | h | h <;>
    simp [twoFourVector,signedSupport,evenMagnitudeSupport,magnitudeSigns,h]

theorem twoFourFamily_shape (k u : ℕ) (x : IntegerCoordinates) (hx : x ∈ twoFourFamily k u) :
    TwoFourShape x k u := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨?_,?_,?_⟩
  · intro i
    have hd : ¬(i ∈ p.1.val ∧ i ∈ p.2.1.val) :=
      fun h => Finset.disjoint_left.mp p.2.1.prop.1 h.1 h.2
    simp only [twoFourFamilyVector,twoFourSignedVector,twoFourVector,signedSupport]
    split_ifs <;> simp_all
  · simp only [twoFourFamilyVector,twoFourSignedVector,twoFour_support_two _ _ p.2.1.prop.1]
    exact p.1.prop.2
  · simp only [twoFourFamilyVector,twoFourSignedVector,twoFour_support_four _ _ p.2.1.prop.1]
    exact p.2.1.prop.2

theorem twoFourFamily_iff (k u : ℕ) (x : IntegerCoordinates) :
    x ∈ twoFourFamily k u ↔ x ∈ leech ∧ TwoFourShape x k u := by
  constructor
  · intro hx
    exact ⟨(twoFourFamily_properties k u x hx).1,twoFourFamily_shape k u x hx⟩
  · rintro ⟨hx,hshape⟩
    let T := evenMagnitudeSupport x 2
    let U := evenMagnitudeSupport x 4
    let s := magnitudeSigns x 2
    let t := magnitudeSigns x 4
    have he : x = twoFourVector T U s t := twoFour_reconstruction x hshape.1
    have hc : supportWord T ∈ golay := by
      have hcon := (mem_leech x).mp hx
      obtain ⟨m,(rfl | rfl),hp,hc,hs⟩ := hcon
      · rw [he,twoFour_residue] at hc
        exact hc
      · have hz := twoFour_parity T U s t ((0,0),0)
        have hp := hp ((0,0),0)
        rw [← he] at hz
        omega
    have hsign : ∑ i : T, s i = (U.card : Bit) :=
      (twoFour_mem_iff T U s t hc).mp (he ▸ hx)
    let p : TwoFourParameters k u :=
      ⟨⟨T,hc,hshape.2.1⟩,⟨U,magnitudeSupports_disjoint x,hshape.2.2⟩,⟨s,hsign⟩,t⟩
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,he.symm⟩

end Atlas.Lattices
