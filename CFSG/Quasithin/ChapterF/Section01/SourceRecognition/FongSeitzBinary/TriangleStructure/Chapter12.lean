module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.LinearRadicals
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The original Chapter 12 triangle cores

The actual proper-K/full KnownSimple preparation gives F.1.1 for ![L,R].
Odd opposition then forces the other factor to be linear over the same
binary degree. In rotation three, both original full parabolic two-cores
are elementary of order q²; their full root-generated actions are
irreducible above the binary field. These conclusions are derived from
the original linear factor and the same marked split quotient.

The whole Borel and both endpoint inclusion squares are those of the
supplied amalgam isomorphism. No natural-action record or core conclusion
is supplied as a premise. The natural coordinates and the final A₂
marked comparison remain source-assembly obligations.

Source: Aschbacher--Smith 12.2.2 and F.1.1--3; Fong--Seitz I (3E), p.15,
and DGS, Groups and Graphs (1985), (10.5) and Theorem D, pp.156,224.
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

/-- Odd opposition identifies the actual opposite factor, with the same degree. -/
theorem rankOne_odd_opposite_linear (hm : Odd (rotationOrder Q)) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^n) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact MarkedLocal.odd_linear_factors_same_degree Q e hf split hm 0 1 (by decide) hpsl

/-- The actual triangle preparation has both elementary cores of order q². -/
theorem rankOne_triangle_cores (hm : rotationOrder Q = 3) (i : Fin 2) :
    IsElementaryAbelian 2 ((parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2) ∧
      Nat.card ((parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2) = 2^(2*n) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact TriangleStructure.original_cores_elementary_order Q e hf split hm 0 hpsl i

/-- The same original triangle gives the full irreducible radical actions. -/
theorem rankOne_triangle_radical_irreducible (hm : rotationOrder Q = 3) (i : Fin 2) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    let hV := (MarkedLocal.odd_linear_regularity Q e hf split
      (hm ▸ (by decide : Odd 3)) 0 hpsl i).1
    letI := TriangleStructure.original_remainders_elementary Q e hf split hm 0 hpsl i
    (Representation.elementaryRepresentation (p := 2) (radicalAction Q split i hV)).IsIrreducible := by
  exact TriangleStructure.original_radical_irreducible Q e
    (d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH)
    split hm 0 hn hpsl i
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
