module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.UnitaryNineQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OctagonStructure.SourceSelection.UnitaryNineProperChapter12

/-!
# Chapter 12's large irreducible section obstruction

The literal effective quotient of a Cartan-invariant RootSection inside
the nine-b subgroup cannot be both irreducible and of order at least
2^(8b). The source root geometry and center obstruction are discharged
from the original factors. The size and irreducibility hypotheses remain
explicit earlier representation inputs for final source assembly.

The quotient, full Borel and both endpoint maps are unchanged; degree one
and both special/projective unitary conventions are included.
Source: Fong--Seitz I (6F), printed p.47, applied at AS 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
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
  (split : SplitData Q.tits) (hm : rotationOrder Q=8)
include D h hmany hn d hTH e split hm

/-- The actual Chapter 12 root section satisfies the whole-subgroup
obstruction, with its effective action and projection unchanged. -/
theorem rankOne_octagon_unitary_nine_irreducible_section_false
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {b : ℕ} (hb : 0 < b)
    (hR : ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^b) ∨
      IsSU (R ⧸ pCore 2 R) 3 (2^b))
    (δ : RootSection Q split 1)
    (hδ : δ.numerator ≤ unitaryNineSubgroup Q split 0 1)
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (δ.numerator : Set (X ⧸ Q.D)))
    (hlarge : 2^(8*b) ≤ Nat.card δ.EffectiveCarrier)
    (hirr : δ.effectiveRepresentation.IsIrreducible) : False := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact original_linear_unitary_nine_irreducible_section_false Q e hf split hm 0 1 (by decide)
    (by omega) hb hpsl hR δ hδ hH hlarge hirr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
