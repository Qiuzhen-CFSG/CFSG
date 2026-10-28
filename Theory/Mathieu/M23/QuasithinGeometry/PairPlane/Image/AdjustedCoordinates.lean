module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Action

/-!
# Adjusted coordinates for the M23 pair plane

Scale the first point coordinate by `a`, and the first line covector coordinate
by `a + 1 = a⁻¹`. The tables encode these diagonal projectivities on normalized
representatives. This preserves incidence and chooses the conjugate of the
index-three field extension containing pure coordinate Frobenius.

Source: Aschbacher, *Sporadic Groups*, §18, the three PSL hyperoval orbits.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage
open PairPlaneCoordinates

/-- Diagonal scaling by `a` on normalized point rows. -/
def pointRow : Fin 21 → Fin 21 :=
  ![0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10, 16, 17, 18, 19, 20]

/-- Inverse diagonal scaling on normalized line covector rows. -/
def lineRow : Fin 21 → Fin 21 :=
  ![0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5, 16, 17, 18, 19, 20]

def pointRowEquiv : Equiv.Perm (Fin 21) where
  toFun := pointRow
  invFun := lineRow
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The adjusted table coordinates; the original coordinates remain available. -/
noncomputable def adjustedCoordinates : Coordinates where
  pointEquiv := pointLabelEquiv.symm.trans (pointRowEquiv.trans projectiveEquiv)
  lineEquiv := lineLabelEquiv.symm.trans (pointRowEquiv.symm.trans projectiveEquiv)
  incident_iff p l := by
    obtain ⟨i, rfl⟩ := pointLabelEquiv.surjective p
    obtain ⟨j, rfl⟩ := lineLabelEquiv.surjective l
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [projective_incident]
    change pointLabel (pointRow i) ∈ lineSet (lineRow j) ↔ pointLabel i ∈ lineSet j
    revert i j
    decide +kernel

@[simp] theorem adjusted_point_labeledPoint (i : Fin 21) :
    adjustedCoordinates.pointEquiv (labeledPoint i) = projectivePoint (pointRow i) :=
  (pointRowEquiv.trans projectiveEquiv).congr_arg (pointLabelEquiv.symm_apply_apply i)

@[simp] theorem adjusted_line_labeledLine (i : Fin 21) :
    adjustedCoordinates.lineEquiv (labeledLine i) = projectivePoint (lineRow i) :=
  (pointRowEquiv.symm.trans projectiveEquiv).congr_arg (lineLabelEquiv.symm_apply_apply i)

end Sporadic.Mathieu.M23Geometry.PairPlaneImage
