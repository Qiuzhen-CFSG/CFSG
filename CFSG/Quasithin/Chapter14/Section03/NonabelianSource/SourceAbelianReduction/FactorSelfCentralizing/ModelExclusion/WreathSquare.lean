module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.LocalStructure
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.ResidualFourSquare

/-!
# The square subgroup in the marked terminal image

The concrete wreath recognition supplies an actual S₃ × S₃ subgroup of
relative index at most two in the terminal image of the marked centralizer.
The existing quotient construction pulls this subgroup back to the literal
centralizer in the cyclic quotient, retaining its quaternion kernel.

This discharges the finite recognition premise of the extension construction.
The independent source placement of an elementary four-group remains the
explicit `TerminalFourSource` hypothesis.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The marked quotient-centralizer extension, retaining only the independent
four-group placement premise and all original ambient hypotheses. -/
theorem quotientCentralizerSource_of_terminal_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hfour : TerminalFourSource F (sourceResidual M Mc)) :
    QuotientCentralizerSource F (sourceResidual M Mc) :=
  quotientCentralizerSource_of_terminal_four_and_wreath_recognition
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hfour
    BinaryFourPlus.exists_square_of_residual_four

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
