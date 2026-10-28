module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.Comparison
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.ThirdConjugacy.PCComparison

/-!
# The certified max4 eight is conjugate to the third literal Sylow row

An explicit ambient word sends all eight elements of the independently
certified max4 eight to the specified kernel-mask subgroup. The checked
PC-word evaluations identify its three generators with precisely g17*g18,
g19 and g20. Subgroup maps use the actual inclusions into Janko4.Model.
The left conjugator is the inverse of the computed right conjugator.

Source context: Kleidman–Wilson (1988), pp.484–510; Aschbacher–Smith A.3.12;
and the literal ATLAS attribution retained in the model modules.
No presentation relation, catalogue or normalizer upper bound is assumed.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Subgroup Janko4 Janko4.LocalStructure.SylowNormalEights.MatrixWords
open ThirdConjugacy

/-- The exact prescribed third row, with its actual ambient inclusion. -/
theorem thirdEight_eq_targetEight : U 2 = ThirdConjugacy.targetEight := by
  change (closure {pcGenerator 17 * pcGenerator 18, pcGenerator 19, pcGenerator 20}).map
    OuterReduction.OddIndex.twoSubgroup.subtype = _
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  change closure {(pcGenerator 17 : Model) * (pcGenerator 18 : Model),
    (pcGenerator 19 : Model), (pcGenerator 20 : Model)} = _
  simp only [pc_pair_eq_kernelMask, pc19_eq_kernelMask, pc20_eq_kernelMask,
    ThirdConjugacy.targetEight]

/-- The actual ambient comparison, in the orientation required by Max4Transport. -/
theorem max4Eight_conjugacy :
    ∃ k : Model, max4Eight.map (MulAut.conj k).toMonoidHom = U 2 := by
  refine ⟨ThirdConjugacy.conjugator, ?_⟩
  rw [thirdEight_eq_targetEight]
  exact ThirdConjugacy.map_max4Eight_eq_targetEight

/-- The existing row consumer now needs only the independently owned full
normalizer bound; the conjugacy premise is discharged. -/
theorem row_two_of_max4_eight_normalizer
    (hN : normalizer (max4Eight : Set Model) ≤
      Janko4.LocalStructure.SymmetricLinear.max4Subgroup) :
    EightNormalizerAlternative (U 2) :=
  row_two_of_max4_eight_conjugacy max4Eight_conjugacy hN

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
