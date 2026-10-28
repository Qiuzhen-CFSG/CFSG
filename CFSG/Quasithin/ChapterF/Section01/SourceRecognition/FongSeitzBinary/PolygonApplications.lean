module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter 12 application of the finite polygon square theorem

The marked finite polygon calculation supplies the square profile internally,
so the Chapter 12 hexagon preparation needs only its genuine rotation-six
configuration. The existing `ChosenModule` preparation supplies the original
F.1.1 hypothesis. Together with the supplied marked amalgam and split
structure, this feeds the exhaustive source catalogue.

Source: Aschbacher--Smith 12.2.2, printed p.795; DGS Theorem D, p.224;
Fong--Seitz I (1J), (6C)--(6E).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The Chapter 12 hexagon comparison with its square profile supplied by the
finite marked polygon metric. -/
theorem rankOne_hexagon_comparison_of_rotation_six
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact HexagonRecognition.marked_hexagon_catalogue_of_rotation_six Q mark hf split hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
