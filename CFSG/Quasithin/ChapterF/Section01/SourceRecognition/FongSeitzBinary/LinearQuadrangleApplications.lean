module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearQuadrangleRecognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# All linear quadrangles in the original Chapter 12 pair

The original proper-K/full KnownSimple preparation supplies F.1.1 for
![L,R]. The linear quotient of L is already part of the Chapter 12 input;
only the opposite original quotient mark is needed here. Equal fields
now give full C₂ recognition without a natural-module profile, and the
proved unequal-field route gives U₄. Both cases preserve the whole Borel
and both endpoint inclusion squares; R may have the binary solvable factor.

The marked split quotient and its rotation order four remain with the
earlier source producers. This closes their entire linear quadrangle
consumer, not the nonlinear rows or unconditional seven-row assembly.

Source: AS 12.2.2 and F.1.1--3; DGS Theorem D, p.224;
Fong--Seitz I (6A), p.37, and II (8A)--(8B), pp.197--202.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary.LinearQuadrangle
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 linear quadrangle branch, including a binary
opposite endpoint and both C₂/U₄ parameter orientations. -/
theorem rankOne_linear_quadrangle_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    {m : ℕ} (hmpos : 0 < m)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact marked_linear_quadrangle_of_factor_types Q mark hf split hm (by omega) hmpos hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
