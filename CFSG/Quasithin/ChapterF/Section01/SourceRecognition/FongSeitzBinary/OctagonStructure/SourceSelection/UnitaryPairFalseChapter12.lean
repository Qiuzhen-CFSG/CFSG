module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.SmallSpecialUnitaryChapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryLowerExclusionChapter12

/-!
# The complete marked octagon comparison

The preceding source-selection modules reduce every remaining unitary row to
the quadratic degree relation `n = 2 * b`.  The literal Fong--Seitz (6F)
lower-central argument excludes that pair, for both the projective and special
unitary scalar conventions.  Hence the same marked quotient supplies the Ree
comparison with no residual local alternative.

The theorem is a Chapter 12 consumer: it keeps the original quotient, split
data, rotation order, full Borel and both endpoint inclusion squares supplied
by the earlier source producers.  It does not identify the ambient completion.
Source: Fong--Seitz I (6F), printed pp.45--49; Aschbacher--Smith 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.OctagonStructure

variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
include D h hmany hn d hTH e split hm

/-- The complete marked comparison at the octagon boundary. -/
theorem rankOne_octagon_complete_comparison
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  rcases D.rankOne_octagon_comparison_or_quadratic_unitary h hmany hn d hTH Q e split hm hpsl with
    hcomp | ⟨b, hb, hR, _⟩
  · exact hcomp
  · exact (D.rankOne_octagon_unitary_pair_false h hmany hn d hTH Q e split hm hpsl hb hR).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
