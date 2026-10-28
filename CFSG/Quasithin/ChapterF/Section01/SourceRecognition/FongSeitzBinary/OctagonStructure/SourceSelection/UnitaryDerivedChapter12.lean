module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryDerived
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryCubicRadicalChapter12

/-!
# Chapter 12's derived unitary octagon radical

Apply the original-factor theorem to the same marked quotient and full
source amalgam. The derived radical lies in the five middle roots, has
order at most 2^(13b), is moved by the unitary actor, and has first
Frattini quotient of order at least 2^(6b). Its cubic centralizer is the
previous full abelian fixed radical. Both scalar conventions and b = 1
remain included, with no additional representation premise.

Source: Fong--Seitz I (6F), printed p.47, at the AS 12.2.2 consumer.
This supplies the initial derived configuration; the projective-section
and lower-central-series contradiction and final marked recognition
remain required.
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

/-- The original Chapter 12 factors give the same derived radical,
its five-root support and order bounds, its moving unitary actor, and
its abelian cubic centralizer. No extra representation input is assumed. -/
theorem rankOne_octagon_unitary_derived_bounds
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b)) :
    let V₂ := simpleRemainder Q split 1
    let D₂ := ⁅V₂,V₂⁆
    D₂ ≤ middleFive Q split 1 0 ∧ Nat.card D₂ ≤ 2^(13*b) ∧
      ⁅rankOne Q split 1,D₂⁆ ≠ ⊥ ∧ 2^(6*b) ≤ Nat.card (D₂ ⧸ frattini D₂) ∧
      D₂ ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) =
        V₂ ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D)) ∧
      IsMulCommutative ↥(D₂ ⊓ centralizer (cartanThreeCore Q : Set (X ⧸ Q.D))) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_derived_bounds Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
