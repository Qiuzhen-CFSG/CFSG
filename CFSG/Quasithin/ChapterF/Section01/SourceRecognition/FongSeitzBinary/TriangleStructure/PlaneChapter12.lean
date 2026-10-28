module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.Plane
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The actual Chapter 12 triangle plane and its translations

The original proper-K/full KnownSimple preparation supplies F.1.1 and one
linear factor. On the same marked split quotient, rotation three then
constructs the projective plane with the original binary field order.
Every nonidentity element of the axis radical is an elation, and evaluation
at any affine origin identifies that radical with all affine points.
All actions use the original quotient and marked full endpoints.

This discharges the regular-elation input to the affine-coordinate step.
It does not assert the final projective field coordinates or A₂ comparison.
Source: AS 12.2.2 and F.1.1--3; Fong--Seitz I (3E), printed p.14;
DGS, Groups and Graphs (1985), (10.5) and Theorem D, pp.156,224.
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

/-- The literal Chapter 12 triangle is a projective plane of the original
field order. Its actual axis radical acts regularly on affine points,
and every nonidentity radical element is an elation. -/
theorem rankOne_triangle_plane_geometry (hm : rotationOrder Q = 3) :
    ∃ pl : Configuration.ProjectivePlane
        (Subgroup.CosetGeometry.RankTwo.Point (TriangleGeometry.family Q))
        (Subgroup.CosetGeometry.RankTwo.Line (TriangleGeometry.family Q)),
      let := pl
      Configuration.ProjectivePlane.order
          (Subgroup.CosetGeometry.RankTwo.Point (TriangleGeometry.family Q))
          (Subgroup.CosetGeometry.RankTwo.Line (TriangleGeometry.family Q)) = 2^n ∧
      Nonempty {p : Subgroup.CosetGeometry.RankTwo.Point (TriangleGeometry.family Q) //
        p ∉ A2Source.QuotientPlane.axis Q} ∧
      (∀ x : simpleRemainder Q split 1, x ≠ 1 →
        ∃ C : Subgroup.CosetGeometry.RankTwo.Point (TriangleGeometry.family Q),
          Configuration.IsElation (x : X ⧸ Q.D) C (A2Source.QuotientPlane.axis Q)) ∧
      (∀ o : {p : Subgroup.CosetGeometry.RankTwo.Point (TriangleGeometry.family Q) //
          p ∉ A2Source.QuotientPlane.axis Q},
        ∃ c : simpleRemainder Q split 1 ≃
          {p : Subgroup.CosetGeometry.RankTwo.Point (TriangleGeometry.family Q) //
            p ∉ A2Source.QuotientPlane.axis Q},
          ∀ a, (c a).val = (a : X ⧸ Q.D) • o.val) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  refine ⟨TriangleStructure.original_plane Q e hf split hm 0 hpsl,
    TriangleStructure.original_plane_order Q e hf split hm 0 hpsl,
    TriangleStructure.original_affine_origin Q e hf split hm 0 hpsl,
    TriangleStructure.original_radical_isElation Q e hf split hm 0 hpsl,?_⟩
  intro o
  exact ⟨TriangleStructure.original_affineOrbitEquiv Q e hf split hm 0 hpsl o,
    TriangleStructure.original_affineOrbitEquiv_apply Q e hf split hm 0 hpsl o⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
