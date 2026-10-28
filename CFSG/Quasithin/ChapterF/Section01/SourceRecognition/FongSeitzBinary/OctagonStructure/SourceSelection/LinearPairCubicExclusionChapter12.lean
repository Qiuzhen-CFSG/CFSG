module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicExclusionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicCentralityChapter12

/-!
# Excluding Chapter 12's binary two-linear octagon

The original two-linear degree relation reduces a binary endpoint to the
PSL₂(2), PSL₂(4) pair. The complete degree-one root and normalizer argument
excludes it. Any remaining linear opposite endpoint has degree greater
than one. The same marked quotient, full Borel, both endpoint inclusions,
and full KnownSimple hypothesis are retained.

Source: Fong--Seitz I (6G), printed p.50, degree-one branch. The general
higher-degree exclusion and final seven-row comparison remain open.
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




/-- The actual Chapter 12 octagon cannot have a binary linear opposite
endpoint, for any selected linear degree n. -/
theorem rankOne_octagon_binary_linear_false
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2) : False := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_binary_endpoint_false Q e hf split hm 1 0
    (by decide) (by omega) hR hpsl

/-- Any remaining original linear opposite factor lies in the higher-degree
branch of (6G); the binary branch has been discharged. -/
theorem rankOne_octagon_selected_linear_degree_gt_one
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^b)) : 1 < b := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact (original_linear_pair_degrees_gt_one Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR).2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
