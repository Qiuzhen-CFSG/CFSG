module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicCentralitySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicNormalizerChapter12

/-!
# Chapter 12's whole-radical middle-root centrality

For the actual selected PSL₂(4), PSL₂(2) pair the middle odd root centralizes
the entire seven-root radical. The root-commutator contradiction removes
the index-sixteen alternative, retaining the full Borel and both endpoint maps.

Source: Fong--Seitz I (6G), printed p.50, first paragraph. The subsequent
degree-one normalizer contradiction is supplied by LinearPairCubicExclusionChapter12;
the higher-degree exclusion remains open.
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



/-- The selected middle-root centralizer is the whole radical. -/
theorem rankOne_octagon_selected_linear_degree_one_middle_centralizer_eq
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    middleRootCentralizer Q split 1 0 = simpleRemainder Q split 1 := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_middle_centralizer_eq Q e hf split hm 1 0
    (by decide) hR hpsl

/-- The actual middle root belongs to the center of the selected radical. -/
theorem rankOne_octagon_selected_linear_degree_one_middle_central
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) ≤
      simpleRemainder Q split 1 ⊓ centralizer (simpleRemainder Q split 1 : Set (X ⧸ Q.D)) := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_middle_central Q e hf split hm 1 0
    (by decide) hR hpsl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
