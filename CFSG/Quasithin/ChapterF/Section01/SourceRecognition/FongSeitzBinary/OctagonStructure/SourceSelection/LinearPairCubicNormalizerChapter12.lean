module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicNormalizerSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicDichotomyChapter12

/-!
# Chapter 12's cubic fixed-subgroup normalizer

For the selected original PSL₂(4), PSL₂(2) factors, the three-root fixed
subgroup has equal normalizer and centralizer inside the radical. In the
proper middle-root-centralizer branch, both are exactly the five middle
roots, and this five-root subgroup is abelian. The full Borel and both original endpoint maps are unchanged.

Source: Fong--Seitz I (6G), printed p.50, normalizer argument. Excluding
the proper-centralizer branch and terminal recognition remain open.
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


/-- The actual degree-one fixed radical has identical normalizer and
centralizer inside the selected seven-root radical. -/
theorem rankOne_octagon_selected_linear_degree_one_fixed_normalizer
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    simpleRemainder Q split 1 ⊓ normalizer (fixedOddRoots Q split 1 0 : Set (X ⧸ Q.D)) =
      simpleRemainder Q split 1 ⊓ centralizer (fixedOddRoots Q split 1 0 : Set (X ⧸ Q.D)) := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_oriented_linear_fixed_normalizer Q e hf split hm 1 0
    (by decide) (a := 1) (b := 2) (by decide) (by decide) (by decide) hR hpsl

/-- In the proper middle-root-centralizer branch, the literal Chapter 12
normalizer and centralizer are exactly the five-root subgroup. -/
theorem rankOne_octagon_selected_linear_degree_one_proper_fixed_normalizer
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2)
    (hproper : middleRootCentralizer Q split 1 0 ≠ simpleRemainder Q split 1) :
    (simpleRemainder Q split 1 ⊓ normalizer (fixedOddRoots Q split 1 0 : Set (X ⧸ Q.D)) =
      middleFive Q split 1 0) ∧
    (simpleRemainder Q split 1 ⊓ centralizer (fixedOddRoots Q split 1 0 : Set (X ⧸ Q.D)) =
      middleFive Q split 1 0) := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_proper_fixed_normalizer Q e hf split hm 1 0
    (by decide) hR hpsl hproper

/-- Cartan irreducibility and the central normal closure force the selected
five-root subgroup to be abelian in the proper-centralizer branch. -/
theorem rankOne_octagon_selected_linear_degree_one_proper_middle_abelian
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2)
    (hproper : middleRootCentralizer Q split 1 0 ≠ simpleRemainder Q split 1) :
    IsMulCommutative (middleFive Q split 1 0) := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_proper_middle_abelian Q e hf split hm 1 0
    (by decide) hR hpsl hproper

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
