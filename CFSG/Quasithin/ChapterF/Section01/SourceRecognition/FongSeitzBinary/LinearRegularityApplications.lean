module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericRootLocalCover
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.RootCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootCommutators

/-!
# Original linear regularity in the source structural consumers

The original even PSL₂ quotients now supply the (2B) containments consumed
by the hexagon middle-root bound and both orientations of the quadrangle
root calculation. The hexagon's separate root-abelianness premise remains
explicit. These are applications to the same canonical root intersections,
full panel kernels and actual dihedral quotient; no Weyl order is inferred.

For Chapter12's selected pair ![L,R], its already supplied PSL₂ hypothesis
on L discharges (2B) at the first endpoint. The result identifies the
pulled-back remainder with the original endpoint two-core and constructs
the same central odd stem cover, retaining its exact action kernel.
No new perfectness assumption or local-model witness is requested.

Source: Fong--Seitz I (2B), p.9, (5C), pp.25--26, (6A), pp.37--38,
and (6E), pp.43--44; Aschbacher--Smith, Chapter12, p.795.
The actual marked quotient and split datum retain the independent producer
qt-dgs85-apartment-exchange. The selected preparation and final exhaustive
comparison remain with the original Chapter12 and DGS assembly owners.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
include e h

/-- The genuine linear source input discharges the local-kernel premise in
the hexagon's initial middle-root bound. The root-abelianness premise is retained. -/
theorem linear_hexagon_radical_commutator (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n))
    (hcomm : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ middleRoots Q split i j :=
  radical_commutator_le_middle Q split hm i j hij
    (linear_remainder_le_kernel_of_model Q e h split i hmodel) hcomm

/-- Both regularity premises of the quadrangle root calculation now follow
from the two original linear quotients, including the nonperfect small cases. -/
theorem linear_quadrangle_root_commutators (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) {ni nj : ℕ}
    (hi : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^ni))
    (hj : ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^nj)) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅rootAt Q split i (Q.simple j),rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≤
        (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  have hVi := linear_remainder_le_kernel_of_model Q e h split i hi
  have hVj := linear_remainder_le_kernel_of_model Q e h split j hj
  exact ⟨QuadrangleStructure.adjacent_roots_commute Q split hm i j hij hVi hVj,
    QuadrangleStructure.middle_roots_commute Q split hm i j hij hVi hVj,
    QuadrangleStructure.cross_root_commutator_le_center Q split hm i j hij hVi hVj⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The original Chapter12 PSL₂ hypothesis discharges (2B) at its first
endpoint, with the literal original two-core and central odd cover retained. -/
theorem rankOne_global_linear_remainder_and_cover
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRemainder Q split 0 ≤ localKernel Q 0 ∧
      (simpleRemainder Q split 0).comap (MarkedLocal.endpointMap Q e 0) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) 0) ∧
      (MarkedLocal.originalRootProjection Q e split 0).ker =
        (MarkedLocal.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 0).subgroupOf
          (MarkedLocal.originalRankOne Q e split 0) ∧
      Function.Surjective (MarkedLocal.originalRootProjection Q e split 0) ∧
      (MarkedLocal.originalRootProjection Q e split 0).ker ≤
        center (MarkedLocal.originalRankOne Q e split 0) ∧
      Nat.Coprime 2 (Nat.card (MarkedLocal.originalRootProjection Q e split 0).ker) ∧
      (MarkedLocal.originalRootProjection Q e split 0).ker ≤
        _root_.commutator (MarkedLocal.originalRankOne Q e split 0) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  have hV := MarkedLocal.linear_remainder_le_kernel_of_model Q e hf split 0 hpsl
  exact ⟨hV,MarkedLocal.remainder_comap_of_containment Q e split 0 hV,
    D.rankOne_global_original_root_cover h hmany hn hpsl d hTH Q e split 0 hV⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
