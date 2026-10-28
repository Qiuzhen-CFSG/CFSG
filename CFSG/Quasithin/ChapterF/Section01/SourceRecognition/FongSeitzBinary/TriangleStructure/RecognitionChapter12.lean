module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.Recognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Catalogue

/-!
# The full Chapter 12 triangle comparison

The original preparation supplies F.1.1 and its first linear factor. The
triangle source theorem constructs projective field coordinates and six
compatible generating roots, and aligns the whole Borel and both endpoints.
The accepted catalogue transport then gives the concrete A₂ amalgam.
No natural-action record, source root equation or final model comparison
is supplied. The same quotient, full marking and proper-K/full KnownSimple
hypotheses are retained.

Source: AS 12.2.2 and F.1.1--3; Fong--Seitz I (3E), printed p.14;
DGS, Groups and Graphs (1985), (10.5) and Theorem D, printed pp.156,224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits)
include D h hmany hn hpsl d hTH e split

/-- The actual Chapter 12 triangle has the full concrete A₂ amalgam, with
natural actions, projective incidence and both endpoint squares discharged. -/
theorem rankOne_triangle_complete_comparison (hm : rotationOrder Q = 3) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨F,hF,hfin,hchar,_,j,⟨rd⟩⟩ :=
    TriangleStructure.original_rootData Q e hf split hm 0 hpsl
  exact A2Source.linear_catalogue_of_flagIso j
    (LinearThreePresentation.comparison Q e hf split rd)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
