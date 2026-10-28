/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechTwoFourFamilies.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechTwoFourCounts

/-!
Finite families of two-four vectors and their cardinalities.
Injectivity of the support/sign parametrization turns parameter counts into vector counts.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev TwoFourParameters (k u : ℕ) :=
  (T : CodeSupports k) × (U : OutsideSupports T.val u) × TwoFourSigns T.val U.val

def twoFourFamilyVector (k u : ℕ) (p : TwoFourParameters k u) : IntegerCoordinates :=
  twoFourSignedVector p.1.val p.2.1.val p.2.2

theorem twoFourFamilyVector_injective (k u : ℕ) : Function.Injective (twoFourFamilyVector k u) := by
  rintro ⟨⟨T,hT⟩,⟨U,hU⟩,s⟩ ⟨⟨T',hT'⟩,⟨U',hU'⟩,s'⟩ h
  have ht := congrArg (fun x => evenMagnitudeSupport x 2) h
  simp only [twoFourFamilyVector,twoFourSignedVector,twoFour_support_two _ _ hU.1,
    twoFour_support_two _ _ hU'.1] at ht
  cases ht
  have hu := congrArg (fun x => evenMagnitudeSupport x 4) h
  simp only [twoFourFamilyVector,twoFourSignedVector,twoFour_support_four _ _ hU.1,
    twoFour_support_four _ _ hU'.1] at hu
  cases hu
  have hs : s = s' := twoFourSignedVector_injective T U hU.1 h
  cases hs
  rfl

theorem twoFourParameters_card (k u : ℕ) (hk : 0 < k) :
    Nat.card (TwoFourParameters k u) =
      golayWeightCount k * Nat.choose (24 - k) u * (2 ^ (k - 1) * 2 ^ u) := by
  rw [Nat.card_sigma]
  have hh (T : CodeSupports k) : Nat.card ((U : OutsideSupports T.val u) × TwoFourSigns T.val U.val) =
      Nat.choose (24 - k) u * (2 ^ (k - 1) * 2 ^ u) := by
    rw [Nat.card_sigma]
    simp_rw [twoFourSigns_card _ _ (by omega : 0 < T.val.card),T.prop.2]
    have he (U : OutsideSupports T.val u) : U.val.card = u := U.prop.2
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card,outsideSupports_card,T.prop.2]
    simp only [Nat.cast_id]
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card,codeSupports_card]
  simp only [Nat.cast_id]
  ring

def twoFourFamily (k u : ℕ) : Finset IntegerCoordinates := Finset.univ.image (twoFourFamilyVector k u)

theorem twoFourFamily_card (k u : ℕ) (hk : 0 < k) :
    (twoFourFamily k u).card =
      golayWeightCount k * Nat.choose (24 - k) u * (2 ^ (k - 1) * 2 ^ u) := by
  rw [twoFourFamily,Finset.card_image_of_injective _ (twoFourFamilyVector_injective k u),
    Finset.card_univ,← Nat.card_eq_fintype_card,twoFourParameters_card k u hk]

theorem twoFourFamily_properties (k u : ℕ) (x : IntegerCoordinates) (hx : x ∈ twoFourFamily k u) :
    x ∈ leech ∧ (∀ i, x i % 2 = 0) ∧ integerDot x x = 4 * (k : ℤ) + 16 * (u : ℤ) := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  refine ⟨(twoFour_mem_iff _ _ _ _ p.1.prop.1).mpr p.2.2.1.prop,twoFour_parity _ _ _ _,?_⟩
  change integerDot (twoFourVector _ _ _ _) (twoFourVector _ _ _ _) = _
  rw [twoFour_norm _ _ p.2.1.prop.1,p.1.prop.2,p.2.1.prop.2]

theorem twoFour_shape_counts :
    (twoFourFamily 8 0).card = 97152 ∧
    (twoFourFamily 12 0).card = 5275648 ∧
    (twoFourFamily 8 1).card = 3108864 ∧
    (twoFourFamily 8 2).card = 46632960 ∧
    (twoFourFamily 12 1).card = 126615552 ∧
    (twoFourFamily 16 0).card = 24870912 := by
  rw [twoFourFamily_card 8 0 (by decide),twoFourFamily_card 12 0 (by decide),
    twoFourFamily_card 8 1 (by decide),twoFourFamily_card 8 2 (by decide),
    twoFourFamily_card 12 1 (by decide),twoFourFamily_card 16 0 (by decide)]
  simp only [golay_weight_distribution]
  norm_num [Nat.choose]

end Atlas.Lattices
