module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The unselected Chapter 12 finite polygon

The original Chapter 12 preparation supplies characteristic two and the
full marked source amalgam. Its actual quotient therefore gives a finite
thick polygon of rotation order greater than two, before any row selection.
The geometric input for Feit--Higman is constructed; the Weyl-order
restriction and the final seven-row assembly remain separate obligations.
All original KnownSimple/proper-K and quotient/marking premises are retained.

Source: AS 12.2.2 and F.1.1; DGS Theorem D, printed p.224;
Fong--Seitz I (1J), printed p.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 quotient supplies every geometric premise of the
finite thick polygon theorem, without a prescribed rotation order. -/
theorem rankOne_finite_thick_polygon
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    2 < rotationOrder Q ∧
      1 < Nat.card (simpleRoot Q split 1) ∧ 1 < Nat.card (simpleRoot Q split 0) ∧
      ∃ M : SimpleGraph.PolygonParameters.Datum
        (Subgroup.CosetGeometry.RankTwo.graph (GeneralGeometry.family Q))
        (rotationOrder Q) (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)),
        ∃ v, M.color v = 0 := by
  exact PolygonGeometry.marked_finite_thick_polygon Q e
    (d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH) split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
