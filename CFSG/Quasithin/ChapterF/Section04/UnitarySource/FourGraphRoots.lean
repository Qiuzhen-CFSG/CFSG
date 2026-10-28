module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraphRoots
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourGraph

/-!
# The graph-fixed root plane in the literal projective unitary model

The injective SU₄ projectivization preserves the intersection of the
actual graph-fixed characteristic plane with the original point residual
center. That intersection is the entire q-element long-root line.
The local projective equivalence is the restriction of the same projection;
no alternate simple carrier or quotient convention is used.

Source: Aschbacher–Smith F.4.37(4), printed p.293 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourGraph
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable (m : ℕ) (hm : 1 ≤ m)

private theorem point_center_project :
    ((center (PointLocal.MatrixLocal m hm)).map (PointLocal.MatrixLocal m hm).subtype).map
      (projection m hm) =
      (center (PointLocal.ProjectiveLocal m hm)).map (PointLocal.ProjectiveLocal m hm).subtype := by
  rw [←center_map_equiv (PointLocal.localEquiv m hm),Subgroup.map_map,Subgroup.map_map]
  congr 1

/-- The literal projective map retains exactly the full long-root intersection. -/
theorem projective_rootPlane_inf_point_center :
    ((rootPlaneHom (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).range.map
      (projection m hm)) ⊓
      (center (PointLocal.ProjectiveLocal m hm)).map (PointLocal.ProjectiveLocal m hm).subtype =
    (longRootHom (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).range.map
      (projection m hm) := by
  rw [←point_center_project m hm]
  exact (Subgroup.map_inf _ _ (projection m hm) (projection_injective m hm)).symm.trans
    (congrArg (fun P => P.map (projection m hm))
      (rootPlane_inf_point_center (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)))

/-- The actual projective intersection has order q, also when q=4. -/
theorem projective_rootPlane_inf_point_center_card :
    Nat.card (((rootPlaneHom (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).range.map
      (projection m hm)) ⊓
      (center (PointLocal.ProjectiveLocal m hm)).map (PointLocal.ProjectiveLocal m hm).subtype :
      Subgroup (ProjectiveGroup m hm)) = 2^m := by
  rw [projective_rootPlane_inf_point_center]
  exact (card_map_of_injective (K :=
    (longRootHom (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).range)
      (projection_injective m hm)).trans
    ((Nat.card_congr (MulEquiv.subgroupCongr (rootPlane_inf_point_center (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)).symm).toEquiv).trans
      ((rootPlane_inf_point_center_card (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm)).trans (PointLocal.fixedField_card m hm)))

/-- The fixed-root intersection is nontrivial on the literal projective carrier. -/
theorem projective_rootPlane_inf_point_center_ne_bot :
    ((rootPlaneHom (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)).range.map
      (projection m hm)) ⊓
      (center (PointLocal.ProjectiveLocal m hm)).map (PointLocal.ProjectiveLocal m hm).subtype ≠ ⊥ := by
  intro hh
  have hc := projective_rootPlane_inf_point_center_card m hm
  rw [hh,card_bot] at hc
  have hq : 1<2^m := Nat.one_lt_pow (by omega) (by decide)
  omega

end CFSG.Quasithin.ChapterF.UnitarySource.FourGraph
