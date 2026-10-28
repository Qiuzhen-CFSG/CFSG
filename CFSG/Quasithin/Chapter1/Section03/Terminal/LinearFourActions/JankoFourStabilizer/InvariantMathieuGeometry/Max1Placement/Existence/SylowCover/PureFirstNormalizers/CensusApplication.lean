module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.CensusGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Ordinary
public import Theory.Quasithin.EvenCharacteristic

/-!
# The pure-four source witness has only census row seven

The literal max4-plane comparison excludes census row two at maximal TWO-local
level. Combining this with the existing complete two-row pure-four census
leaves row seven. The source consumer accepts the actual equality of whole
normalizers supplied by `NonsingularImages.source_maximal_reduction`, retaining
one ambient conjugator on the pure witness, its full centralizer, and the
original normalizer. The optional fixed order-256 centralizer placement is
consumed by the existing h8-to-F endpoint, without a circular pure cover.

Source: Kleidman--Wilson (1988), Corollary 1.2.2 and Section 2.1,
pp.488--489. This only resolves the order-four subcase; larger pure groups and
the exact native-eight normalizer placement remain independent obligations.
-/
public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.PureFirstNormalizers
open ElementaryNormalizerCover
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers
attribute [local irreducible] modelGroup matrixA matrixB

/-- The first pure census row has a strictly larger two-local normalizer. -/
theorem first_four_two_not_maximal :
    ¬ IsMaximalTwoLocal (normalizer (firstFourGroup 2 : Set Model)) := by
  intro hmax
  obtain ⟨g,hg⟩ := first_four_two_conjugate_plane
  have hm := Theory.Quasithin.isMaximalTwoLocal_map (MulAut.conj g) hmax
  rw [map_equiv_normalizer_eq,hg] at hm
  have he := hm.eq_of_le max4_isTwoLocal plane_normalizer_lt_max4.le
  exact plane_normalizer_lt_max4.ne he

/-- Any pure four-group with maximal TWO-local normalizer belongs to census
row 7, with its full centralizer and normalizer transported by the same element. -/
theorem maximal_pure_four_group_seven (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : Nat.card X = 4) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ g : Model,
      X = (firstFourGroup 7).map (MulAut.conj g).toMonoidHom ∧
      centralizer (X : Set Model) =
        (centralizer (firstFourGroup 7 : Set Model)).map (MulAut.conj g).toMonoidHom ∧
      normalizer (X : Set Model) =
        (normalizer (firstFourGroup 7 : Set Model)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i,g,hi,hX,hC,hN⟩ := pure_first_four_group_geometry X hcard hpure
  rcases hi with rfl | rfl
  · apply False.elim
    apply first_four_two_not_maximal
    rw [hN] at hmax
    exact (Theory.Quasithin.isMaximalTwoLocal_map_iff (MulAut.conj g) _).mp hmax
  · exact ⟨g,hX,hC,hN⟩

/-- Apply the two-row exclusion to the literal pure witness returned by the
nonsingular source reduction. Its whole normalizer is exactly the original one. -/
theorem source_pure_four_witness (X Z : Subgroup Model)
    [IsElementaryAbelian 2 Z] (hcard : Nat.card Z = 4)
    (hpure : ∀ z ∈ Z, z ≠ 1 → IsConj a z)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hNZ : normalizer (X : Set Model) = normalizer (Z : Set Model)) :
    ∃ g : Model,
      Z = (firstFourGroup 7).map (MulAut.conj g).toMonoidHom ∧
      centralizer (Z : Set Model) =
        (centralizer (firstFourGroup 7 : Set Model)).map (MulAut.conj g).toMonoidHom ∧
      normalizer (X : Set Model) =
        (normalizer (firstFourGroup 7 : Set Model)).map (MulAut.conj g).toMonoidHom := by
  have hm : IsMaximalTwoLocal (normalizer (Z : Set Model)) := hNZ ▸ hmax
  obtain ⟨g,hZ,hC,hN⟩ := maximal_pure_four_group_seven Z hcard hpure hm
  exact ⟨g,hZ,hC,hNZ.trans hN⟩

/-- Once the remaining pure witness has the literal exceptional full-centralizer
position, the exact independent order-256 normalizer premise gives the native F
endpoint for the original normalizer. This does not assert that position. -/
theorem source_pure_exceptional_endpoint (h8 : PureTwoA.EightNormalizerPlacement)
    (X Z : Subgroup Model) (g : Model)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hNZ : normalizer (X : Set Model) = normalizer (Z : Set Model))
    (hC : (centralizer (Z : Set Model)).map (MulAut.conj g).toMonoidHom =
      ElementaryEightGeometry.nativeEight 1) :
    ∃ k : Model, normalizer (X : Set Model) =
      LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom := by
  have hm : IsMaximalTwoLocal (normalizer (Z : Set Model)) := hNZ ▸ hmax
  obtain ⟨k,hk⟩ := PureTwoA.fused_eight_maximal h8 Z g hC hm
  exact ⟨k,hNZ.trans hk⟩

end Janko4.LocalStructure.PureFirstNormalizers
