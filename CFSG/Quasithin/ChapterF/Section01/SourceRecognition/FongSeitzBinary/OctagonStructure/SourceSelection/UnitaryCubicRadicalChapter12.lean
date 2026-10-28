module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryCubicRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryCubicFixedChapter12

/-!
# Chapter 12's full cubic radical centralizer

Apply the original-factor result to Chapter 12's actual marked quotient.
Its cubic radical centralizer is the three-factor Frattini product and is
normalized by the full Cartan and the opposite unitary Frattini groups.
The special/projective scalar convention and the binary unitary case are
retained. This discharges the product and invariance step of Fong--Seitz I
(6F), pp.46--47, for the AS 12.2.2 consumer; the full centralizer is also proved abelian by the source commutator
argument. The later lower-central-series contradiction remains required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups Pointwise
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

/-- Chapter 12 supplies the literal full fixed-radical product, with both
normalizing groups used in the ensuing source commutator argument. -/
theorem rankOne_octagon_unitary_cubic_radical
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let Y := simpleRemainder Q split 1 ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))
    (Y : Set (X ⧸ Q.D)) =
      (rootFrattiniAt Q split 1 (Q.simple 0) : Set (X ⧸ Q.D)) *
      (rootFrattiniAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) *
      (rootFrattiniAt Q split 1 (Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) ∧
    Q.tits.B ⊓ Q.tits.N ≤ normalizer (Y : Set (X ⧸ Q.D)) ∧
    rootFrattiniAt Q split 1 1 ⊔ rootFrattiniAt Q split 1 (Q.simple 1) ≤
      normalizer (Y : Set (X ⧸ Q.D)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_cubic_radical Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

/-- Chapter 12's full cubic radical centralizer is abelian, from its
original local factors rather than an extra commutativity premise. -/
theorem rankOne_octagon_unitary_cubic_radical_abelian
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    IsMulCommutative ↥(simpleRemainder Q split 1 ⊓
      centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_cubic_radical_abelian Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
