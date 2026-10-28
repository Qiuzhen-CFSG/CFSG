module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.Gonality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.PolygonGeometryChapter12

/-!
# The original source quotient's allowed Weyl rotation orders

Feit--Higman restricts the finite quotient's rotation order to 2, 3, 4, 6, 8.
The original characteristic-two marking excludes the digon, leaving exactly
3, 4, 6, 8. The full Borel, both parabolics and their endpoint inclusion maps
remain those of the supplied source amalgam, including all binary cases.
The Chapter 12 application retains its preparation and K-group hypotheses.

Source: Fong--Seitz I (1J), printed p.6; AS F.1.1 and 12.2.2.
These exports discharge the gonality input; final model recognition is separate.
-/

public noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.PolygonGonality
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- Characteristic two removes the digon exception from the even spectrum. -/
theorem marked_even_minpoly
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    {half : ℕ} (he : rotationOrder Q=2*half) :
    minpoly ℝ ((GeneralGeometry.metricDatum Q split).distanceMatrix 1) =
      SimpleGraph.PolygonParameters.Gonality.evenAnnihilator half
        (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)) := by
  have hm := PolygonGeometry.marked_rotationOrder_gt_two Q e h split
  exact Gonality.marked_even_minpoly Q split (by omega) he

/-- The original quotient, with its canonical full amalgam marking. -/
theorem original_even_minpoly (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) {half : ℕ} (he : rotationOrder Q=2*half) :
    minpoly ℝ ((GeneralGeometry.metricDatum Q split).distanceMatrix 1) =
      SimpleGraph.PolygonParameters.Gonality.evenAnnihilator half
        (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)) :=
  marked_even_minpoly Q (originalMarkedIso Q) h split he

/-- Odd gonality equates the two original full-Borel panel indices. -/
theorem original_odd_panel_indices_eq (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (ho : Odd (rotationOrder Q)) :
    ((commonBorel L S).subgroupOf (parabolic L S 1)).index =
      ((commonBorel L S).subgroupOf (parabolic L S 0)).index := by
  rw [RootCoordinates.original_commonBorel_root_index h Q split 1,
    RootCoordinates.original_commonBorel_root_index h Q split 0,
    Gonality.marked_odd_parameters_eq Q split ho]
/-- The literal source marking excludes two from the Feit--Higman alternatives. -/
theorem marked_rotationOrder_allowed
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits) :
    rotationOrder Q=3 ∨ rotationOrder Q=4 ∨ rotationOrder Q=6 ∨ rotationOrder Q=8 := by
  have ha := Gonality.marked_rotationOrder_allowed Q split
  have hm := PolygonGeometry.marked_rotationOrder_gt_two Q e h split
  omega

/-- The original quotient with its canonical full source marking. -/
theorem original_rotationOrder_allowed (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) :
    rotationOrder Q=3 ∨ rotationOrder Q=4 ∨ rotationOrder Q=6 ∨ rotationOrder Q=8 :=
  marked_rotationOrder_allowed Q (originalMarkedIso Q) h split

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.PolygonGonality

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 quotient has the even polygon minimal polynomial. -/
theorem rankOne_even_polygon_minpoly
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) {half : ℕ} (he : rotationOrder Q=2*half) :
    minpoly ℝ ((GeneralGeometry.metricDatum Q split).distanceMatrix 1) =
      SimpleGraph.PolygonParameters.Gonality.evenAnnihilator half
        (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)) :=
  PolygonGonality.marked_even_minpoly Q e
    (d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH) split he
/-- The actual finite polygon in the Chapter 12 preparation has an allowed
rotation order, with the digon excluded by the original source hypotheses. -/
theorem rankOne_polygon_gonality
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    rotationOrder Q=3 ∨ rotationOrder Q=4 ∨ rotationOrder Q=6 ∨ rotationOrder Q=8 := by
  obtain ⟨hm,hs,ht,M,hp⟩ := D.rankOne_finite_thick_polygon h hmany hn hpsl d hTH Q e split
  have ha := M.gonality (by omega) hs ht hp
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
