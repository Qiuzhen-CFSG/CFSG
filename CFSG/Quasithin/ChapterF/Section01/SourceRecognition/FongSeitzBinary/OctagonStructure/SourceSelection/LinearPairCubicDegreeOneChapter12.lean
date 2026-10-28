module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearPairCubicDegreeOneSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairCubicTerminalChapter12

/-!
# Chapter 12 degree-one octagon Cartan and root calculations

The selected preparation supplies the genuine F.1.1 hypothesis and the two
original endpoint maps. The consumers use that same marked quotient to
exclude commuting full even rank-one groups, prove the even root-group
noncommutativity, and construct the odd-root diagonal involution. The later
(6G) normalizer contradiction remains to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.LinearPanel
open ChapterF.Source.FongSeitzBinary.OctagonStructure
open ChapterF.Source.FongSeitzBinary.ReeSource

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

/-- The degree-one selected linear row is excluded by the literal source
Cartan argument once the even endpoint's perpendicular commutator is present. -/
theorem rankOne_octagon_selected_linear_degree_one_exclusion
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2)
    (hcomm : ⁅rankOne Q split 0,
      rightConjugate (rankOne Q split 0)
        (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D)⁆ = ⊥) :
    False := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_cartan_exclusion Q e hf split hm
    1 0 (by decide) hR hpsl hcomm

/-- The selected degree-one source branch has a nontrivial commutator between
the full even rank-one group and its indicated Weyl conjugate. The separate
root-group conclusion below uses Weyl-reflection transport. -/
theorem rankOne_octagon_selected_linear_degree_one_perpendicular_nontrivial
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    ⁅rankOne Q split 0,
      rightConjugate (rankOne Q split 0)
        (representative (Q.simple 1 * Q.simple 0 * Q.simple 1) : X ⧸ Q.D)⁆ ≠ ⊥ := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_perpendicular_nontrivial Q e hf split hm
    1 0 (by decide) hR hpsl

/-- The selected degree-one source has the nonzero root commutator used in
the subsequent normalizer argument of (6G), with the original endpoint maps. -/
theorem rankOne_octagon_selected_linear_degree_one_root_perpendicular_nontrivial
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    ⁅simpleRoot Q split 0,
      rootAt Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1)⁆ ≠ ⊥ := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_root_perpendicular_nontrivial Q e hf split hm
    1 0 (by decide) hR hpsl

/-- The selected degree-one branch supplies the actual nonzero perpendicular
root commutator and diagonal involution used by the source normalizer proof. -/
theorem rankOne_octagon_selected_linear_degree_one_root_relations
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hR : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 2)
    (hn2 : n = 2) :
    ⁅simpleRoot Q split 0,
      rootAt Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1)⁆ ≠ ⊥ ∧
    ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0 * Q.simple 1)⁆ = ⊥ ∧
    ∃ x ∈ rootAt Q split 1 (Q.simple 0 * Q.simple 1 * Q.simple 0),
      ∃ y ∈ rootAt Q split 1 (Q.simple 0 * Q.simple 1),
        x ≠ 1 ∧ y ≠ 1 ∧
        ⁅simpleRoot Q split 1,rootAt Q split 1 (Q.simple 0)⁆ = zpowers (x*y) ∧
        orderOf (x*y) = 2 := by
  subst n
  have hf := d.hypothesisF11
    (D.rankOne_generic_input_of_many h hmany (n := 2) (by decide) hpsl) hTH
  exact original_linear_degree_one_root_relations Q e hf split hm
    1 0 (by decide) hR hpsl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
