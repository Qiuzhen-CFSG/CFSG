module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.LinearEndpointRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.LinearPairExclusionChapter12

/-!
# Chapter 12's complete marked octagon comparison

The original linear/unitary pair is excluded by lower-central persistence.
Together with the existing two-linear exclusion, this leaves the actual
source-constructed Ree row. The resulting comparison has no extra local
factor, representation, section-persistence or model-marking premise.

The genuine earlier marked quotient, its full amalgam isomorphism, split
data and rotation order remain explicit. Both endpoint squares, the full
Borel, proper-K and full KnownSimple scope are retained; this local result
does not identify the ambient completion with the finite quotient.

Source: Fong--Seitz I (6F)--(6H), II Section 10; AS 12.2.2; DGS p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups Pointwise
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

/-- The actual original unitary opposite factor is impossible in every
positive degree, for either scalar convention. -/
theorem rankOne_octagon_unitary_pair_false
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) : False := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_pair_false Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR

/-- Every scalar-fixed lower-central term in the actual Chapter 12 quotient
retains the projective eight-b section and escapes the nine-b subgroup. -/
theorem rankOne_octagon_unitary_scalar_lower_persistence
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b))
    (hK : simpleRemainder Q split 1 ≤ localKernel Q 1) :
    ∀ k : ℕ, let c := unitaryScalarLowerSection Q split 1 hK k
      ¬ IsPGroup 2 c.action.range ∧
      2^(8*b) ≤ Nat.card c.EffectiveCarrier ∧
      ¬ c.numerator ≤ unitaryNineSubgroup Q split 0 1 := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_scalar_lower_persistence Q e hf split hm 0 1
    (by decide) (by omega) hb hpsl hR hK

/-- The octagon branch now supplies Chapter 12's requested concrete marked
comparison on the original parabolic amalgam. -/
theorem rankOne_octagon_comparison
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨m,_,he⟩ := original_linear_octagon_comparison Q e hf split hm
    (by omega : 0 < n) hpsl
  exact .ree m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
