module

public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCentersQuotient
public import Theory.SpecificGroups.SL2.BinaryLocalRecognition

/-!
# Recognition of the actual three-center quotient image

The first two framed transvections give noncommuting involutions in the
literal image of the three-generator point-local subgroup. Binary Dickson
recognition therefore kills its intrinsic two-core and gives either an odd
dihedral group or SL₂ over a binary subfield degree greater than one.

This proves the recognition alternative G.4.9(a), Aschbacher--Smith, printed
p.341, for the actual image and actors constructed by the three-center step.
It adds no local classification, field generation, or quotient geometry premise.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenterConfiguration
open InvolutionTypes
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {X : Subgroup (Sp F)} {a : Sp F}

/-- The actual three-center quotient image has trivial intrinsic two-core. -/
theorem quotientImage_twoCore_eq_bot (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    pCore 2 D.quotientImage = ⊥ := by
  obtain ⟨h1, h2⟩ := D.image_pair_orderOf ha
  exact Matrix.SpecialLinearGroup.binary_subgroup_twoCore_eq_bot_of_noncommuting_involutions
    D.quotientImage D.firstImage D.secondImage h1 h2 (D.image_pair_noncommute ha)

/-- The actual three-center image is odd dihedral or a binary SL₂ subfield model. -/
theorem quotientImage_recognition {n : ℕ} (hF : Nat.card F = 2^n)
    (D : ThreeCenterConfiguration X a) (ha : IsB1 a) :
    (∃ m : ℕ, Odd m ∧ 1 < m ∧ Nonempty (D.quotientImage ≃* DihedralGroup m)) ∨
    (∃ k : ℕ, 1 < k ∧ k ∣ n ∧
      Nonempty (D.quotientImage ≃* SL(2,GaloisField 2 k))) := by
  obtain ⟨h1, h2⟩ := D.image_pair_orderOf ha
  exact Matrix.SpecialLinearGroup.binary_subgroup_recognition_of_noncommuting_involutions
    hF D.quotientImage D.firstImage D.secondImage h1 h2 (D.image_pair_noncommute ha)

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ThreeCenterConfiguration
