module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CensusApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairTransport

/-!
# Native kernel placement of the pure-four source witness

At maximal two-local level the source's pure four-group belongs to census
row 7. The checked displacement-product rank identifies that row with the
literal pair of masks 818 and 1449 in max1. Composing the two ambient
conjugators transports the source witness, its full centralizer and its
whole original normalizer together.

Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489. This discharges
the four-group positioning step. Placement of the full native centralizer
and the subsequent pure elementary extensions remains a separate premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers
open ElementaryNormalizerCover
open ElementaryNormalizerCover.PureTwoA.NativePair
attribute [local irreducible] modelGroup matrixA matrixB

/-- The maximal pure-four branch has a literal native pair marking, with one
conjugator on its witness, centralizer and normalizer. -/
theorem maximal_pure_four_native (Z : Subgroup Model) [IsElementaryAbelian 2 Z]
    (hcard : Nat.card Z = 4) (hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z)
    (hmax : IsMaximalTwoLocal (normalizer (Z : Set Model))) :
    ∃ g : Model,
      Z.map (MulAut.conj g).toMonoidHom = nativePair ∧
      (centralizer (Z : Set Model)).map (MulAut.conj g).toMonoidHom =
        centralizer (nativePair : Set Model) ∧
      (normalizer (Z : Set Model)).map (MulAut.conj g).toMonoidHom =
        normalizer (nativePair : Set Model) := by
  obtain ⟨k, hZ, _, _⟩ := maximal_pure_four_group_seven Z hcard hpure hmax
  obtain ⟨h, hP, _, _⟩ := row_seven_geometry
  have he : Z.map (MulAut.conj (h * k⁻¹)).toMonoidHom = nativePair := by
    rw [hZ, map_map, hP]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨h * k⁻¹, he, ?_, ?_⟩
  · rw [← he]
    exact map_centralizer_equiv (Z : Set Model) (MulAut.conj (h * k⁻¹))
  · rw [map_equiv_normalizer_eq, he]

/-- Apply native positioning to the literal pure witness with the source's
equality of whole normalizers retained. -/
theorem source_pure_four_native (X Z : Subgroup Model)
    [IsElementaryAbelian 2 Z] (hcard : Nat.card Z = 4)
    (hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hNZ : normalizer (X : Set Model) = normalizer (Z : Set Model)) :
    ∃ g : Model,
      Z.map (MulAut.conj g).toMonoidHom = nativePair ∧
      Z.map (MulAut.conj g).toMonoidHom ≤ LinearFive.M ∧
      (centralizer (Z : Set Model)).map (MulAut.conj g).toMonoidHom =
        centralizer (nativePair : Set Model) ∧
      (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom =
        normalizer (nativePair : Set Model) := by
  have hm : IsMaximalTwoLocal (normalizer (Z : Set Model)) := hNZ ▸ hmax
  obtain ⟨g, hZ, hC, hN⟩ := maximal_pure_four_native Z hcard hpure hm
  exact ⟨g, hZ, hZ.trans_le nativePair_le_max1, hC, by rw [hNZ]; exact hN⟩

end Janko4.LocalStructure.PureFirstNormalizers
