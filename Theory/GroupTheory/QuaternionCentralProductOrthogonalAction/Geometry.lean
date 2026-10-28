module

public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Geometry.Coordinates
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport

/-!
# Square geometry on the intrinsic quaternion central quotient

Squaring on the literal quotient `Q / Z(Q)` gives a nondegenerate binary
quadratic form of dimension four with a totally singular plane. These
plus-type properties and the marked quaternion-generator coordinates are
re-exported from `Basic` and `Coordinates`.

The coordinates identify this form with the orthogonal sum of two anisotropic
binary planes. Conjugating linear maps gives an equivalence of the full
isometry groups, and the explicit binary model identifies this group with
`S₃ wr C₂`, of order 72. The inverse equivalence constructs every isometry
from its two permutations and its plane interchange. The final action formula
intertwines the actual automorphism action on `Q / Z(Q)` with this wreath
action, supplying the geometry for the outer-action assembly.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988, PDF p.1005.
-/

public section

namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)

/-- The quadratic-space identification marked by the two actual quaternion factors. -/
noncomputable def coordinateIsometry (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) :
    d.quadraticForm.IsometryEquiv BinaryFourPlus.q where
  toLinearEquiv := d.coordinates eL eR
  map_app' v := by
    rw [BinaryFourPlus.q_apply]
    exact (d.quadraticForm_coordinates eL eR v).symm

/-- The left quaternion generators give the first anisotropic plane. -/
@[simp] theorem coordinateIsometry_left (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i : Fin 2) :
    d.coordinateIsometry eL eR (d.factorVector d.left eL i) = (Pi.single i 1, 0) :=
  d.coordinates_left eL eR i

/-- The right quaternion generators give the second anisotropic plane. -/
@[simp] theorem coordinateIsometry_right (eL : d.left ≃* QuaternionGroup 2)
    (eR : d.right ≃* QuaternionGroup 2) (i : Fin 2) :
    d.coordinateIsometry eL eR (d.factorVector d.right eR i) = (0, Pi.single i 1) :=
  d.coordinates_right eL eR i

/-- The intrinsic square form is the concrete binary four-dimensional plus form. -/
noncomputable def squareFormIsometry : d.quadraticForm.IsometryEquiv BinaryFourPlus.q where
  toLinearEquiv := d.squareCoordinates
  map_app' v := by
    rw [BinaryFourPlus.q_apply]
    exact (d.quadraticForm_squareCoordinates v).symm

@[simp] theorem squareFormIsometry_apply (v : d.SquareSpace) :
    d.squareFormIsometry v = d.squareCoordinates v := by rfl

/-- Conjugate intrinsic square-preserving linear maps into the explicit plus model. -/
noncomputable def squareIsometriesEquivModel :
    d.squareIsometries ≃* BinaryFourPlus.q.isometrySubgroup :=
  d.squareFormIsometry.isometrySubgroupCongr

/-- The model equivalence retains the linear action on every quotient vector. -/
theorem squareIsometriesEquivModel_intertwines (g : d.squareIsometries)
    (v : d.SquareSpace) :
    (d.squareIsometriesEquivModel g).val (d.squareCoordinates v) =
      d.squareCoordinates (g.val v) :=
  d.squareFormIsometry.isometrySubgroupCongr_intertwines g v

/-- The full intrinsic square-isometry group is `S₃ wr C₂`, via its actual action. -/
noncomputable def squareIsometriesEquivWreath : d.squareIsometries ≃* BinaryFourPlus.Wreath :=
  d.squareIsometriesEquivModel.trans BinaryFourPlus.isometryEquivWreath

/-- Each output plane uses its base permutation and the inverse wreath shift. -/
theorem squareIsometriesEquivWreath_action (g : d.squareIsometries)
    (v : d.SquareSpace) (i : BinaryFourPlus.C2) :
    BinaryFourPlus.coordinate (d.squareCoordinates (g.val v)) i =
      BinaryFourPlus.planeLinear ((d.squareIsometriesEquivWreath g).left i)
        (BinaryFourPlus.coordinate (d.squareCoordinates v)
          ((d.squareIsometriesEquivWreath g).right⁻¹ * i)) := by
  rw [← d.squareIsometriesEquivModel_intertwines]
  exact BinaryFourPlus.isometryEquivWreath_action _ _ _

/-- Every wreath element gives the indicated isometry of the actual central quotient. -/
theorem squareIsometriesEquivWreath_symm_apply (w : BinaryFourPlus.Wreath)
    (v : d.SquareSpace) :
    (d.squareIsometriesEquivWreath.symm w).val v =
      d.squareCoordinates.symm
        ((BinaryFourPlus.wreathToIsometry w).val (d.squareCoordinates v)) := by
  change (d.squareFormIsometry.isometrySubgroupCongr.symm
    (BinaryFourPlus.isometryEquivWreath.symm w)).val v = _
  rw [QuadraticMap.IsometryEquiv.isometrySubgroupCongr_symm_apply,
    BinaryFourPlus.isometryEquivWreath_symm_apply]
  rfl

/-- The full intrinsic isometry group has order 72, by the concrete identification. -/
theorem card_squareIsometries : Nat.card d.squareIsometries = 72 :=
  (Nat.card_congr d.squareIsometriesEquivModel.toEquiv).trans BinaryFourPlus.card_isometrySubgroup

/-- The actual automorphism action, expressed in the concrete orthogonal wreath model. -/
noncomputable def quotientWreathAction : MulAut Q →* BinaryFourPlus.Wreath :=
  d.squareIsometriesEquivWreath.toMonoidHom.comp d.squareIsometryAction

@[simp] theorem quotientWreathAction_eq (a : MulAut Q) :
    d.quotientWreathAction a =
      d.squareIsometriesEquivWreath (d.squareIsometryAction a) := by rfl

/-- Compatibility with the literal quotient action, including the wreath indexing convention. -/
theorem quotientWreathAction_apply (a : MulAut Q) (v : Q ⧸ center Q)
    (i : BinaryFourPlus.C2) :
    BinaryFourPlus.coordinate
      (d.squareCoordinates (Additive.ofMul (quotientAut (center Q) a v))) i =
      BinaryFourPlus.planeLinear ((d.quotientWreathAction a).left i)
        (BinaryFourPlus.coordinate (d.squareCoordinates (Additive.ofMul v))
          ((d.quotientWreathAction a).right⁻¹ * i)) := by
  change _ = BinaryFourPlus.planeLinear
    ((d.squareIsometriesEquivWreath (d.squareIsometryAction a)).left i) _
  rw [← d.squareIsometryAction_apply]
  exact d.squareIsometriesEquivWreath_action _ _ _

end Subgroup.QuaternionCentralProductData
