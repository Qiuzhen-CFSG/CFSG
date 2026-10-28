module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.GeneralGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MinimalConfiguration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceApplication

/-!
# The original finite thick polygon before Weyl-order selection

The arbitrary-order BN geometry is applied to the same marked quotient,
with the complete original Borel and both endpoint inclusions. Source
characteristic two rules out rotation order two: two involutions whose
product has order two commute, contradicting the proved irreducibility.
The source specialization rewrites the polygon parameters as the original
parabolic/common-Borel indices minus one. No finiteness of the original
ambient completion and no choice of a Lie row is required.

These results discharge the geometric hypotheses of the finite polygon
nonexistence theorem used in Fong--Seitz I (1J), printed p.6. The
restriction to rotation orders 3, 4, 6, 8 is the remaining Feit--Higman
input, not a consequence asserted by this module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.PolygonGeometry
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- Original characteristic two excludes the reducible digon. -/
theorem marked_rotationOrder_gt_two
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) : 2 < rotationOrder Q := by
  have hlo := rotationOrder_ge_two Q
  have hne := (MarkedLocal.source_minimal_configuration Q e h split).2.2.2.2.2
  by_contra hsmall
  have he : rotationOrder Q = 2 := by omega
  have hp := pow_orderOf_eq_one (Q.simple 0 * Q.simple 1)
  change (Q.simple 0 * Q.simple 1) ^ rotationOrder Q = 1 at hp
  rw [he] at hp
  have hi (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
      (Q.tits.involutions _ (Q.simple_mem i)).2)
  have hab : (Q.simple 0 * Q.simple 1)⁻¹ = Q.simple 0 * Q.simple 1 :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
  apply hne
  change Q.simple 0 * Q.simple 1 = Q.simple 1 * Q.simple 0
  simpa only [mul_inv_rev, hi] using hab.symm

/-- The complete Feit--Higman geometric input on the same marked quotient. -/
theorem marked_finite_thick_polygon
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) :
    2 < rotationOrder Q ∧
      1 < Nat.card (simpleRoot Q split 1) ∧ 1 < Nat.card (simpleRoot Q split 0) ∧
      ∃ D : SimpleGraph.PolygonParameters.Datum
        (Subgroup.CosetGeometry.RankTwo.graph (GeneralGeometry.family Q))
        (rotationOrder Q) (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)),
        ∃ v, D.color v = 0 :=
  ⟨marked_rotationOrder_gt_two Q e h split,
    (GeneralGeometry.metricDatum_thick Q split).1,
    (GeneralGeometry.metricDatum_thick Q split).2,
    GeneralGeometry.metricDatum Q split, GeneralGeometry.metricDatum_point Q split⟩

/-- The same polygon with parameters given by the original full Borel indices. -/
theorem original_finite_thick_polygon
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits) :
    2 < rotationOrder Q ∧
      1 < ((commonBorel L S).subgroupOf (parabolic L S 1)).index - 1 ∧
      1 < ((commonBorel L S).subgroupOf (parabolic L S 0)).index - 1 ∧
      ∃ D : SimpleGraph.PolygonParameters.Datum
        (Subgroup.CosetGeometry.RankTwo.graph (GeneralGeometry.family Q))
        (rotationOrder Q)
        (((commonBorel L S).subgroupOf (parabolic L S 1)).index - 1)
        (((commonBorel L S).subgroupOf (parabolic L S 0)).index - 1),
        ∃ v, D.color v = 0 := by
  rw [RootCoordinates.original_commonBorel_root_index h Q split 1,
    RootCoordinates.original_commonBorel_root_index h Q split 0,
    Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  exact marked_finite_thick_polygon Q (originalMarkedIso Q) h split

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.PolygonGeometry
