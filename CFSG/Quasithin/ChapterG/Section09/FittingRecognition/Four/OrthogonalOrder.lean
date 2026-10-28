module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Models
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport
import Mathlib.Tactic.FinCases

/-!
# The full split orthogonal carrier in the degree-four branch

An explicit change of coordinates identifies the prescribed hyperbolic form
with the orthogonal sum of two anisotropic binary planes. Conjugation then
identifies the full isometry groups, retaining the natural action. The existing
wreath-product calculation gives order 72 for this exact carrier, as needed
for the index bound in G.9.4(4). No identification with the elementary
orthogonal subgroup is made.

Source: Aschbacher--Smith, G.9.4, printed pp.354--355/PDF pp.365--366.
-/


open ClassicalOrthogonal
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
/-- Hyperbolic coordinates as two perpendicular anisotropic binary planes. -/
@[expose] public def splitCoordinates : VectorD 2 (ZMod 2) ≃ₗ[ZMod 2] BinaryFourPlus.V where
  toFun x := (![x (.inl 1) + x (.inr 0) + x (.inl 0), x (.inr 1) + x (.inl 1)],
    ![x (.inr 0) + x (.inl 0), x (.inl 0) + x (.inr 1) + x (.inl 1)])
  invFun v := Sum.elim ![v.1 1 + v.2 1, v.1 0 + v.2 0]
    ![v.1 1 + v.2 0 + v.2 1, v.1 0 + v.1 1 + v.2 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

/-- The coordinate map preserves the quadratic form itself. -/
public def splitIsometry : (formD 2 (ZMod 2)).IsometryEquiv BinaryFourPlus.q where
  toLinearEquiv := splitCoordinates
  map_app' := by decide +kernel

/-- Conjugation identifies the full isometry groups on the two carriers. -/
public def splitOrthogonalEquiv : OrthogonalFour ≃* BinaryFourPlus.q.isometrySubgroup :=
  (MulEquiv.subgroupCongr (by
    ext g
    exact (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).trans
      (QuadraticMap.mem_isometrySubgroup _ _).symm)).trans splitIsometry.isometrySubgroupCongr

/-- The group comparison intertwines the literal natural actions. -/
public theorem splitOrthogonalEquiv_intertwines (g : OrthogonalFour)
    (v : VectorD 2 (ZMod 2)) :
    (splitOrthogonalEquiv g).val (splitCoordinates v) = splitCoordinates (g.val v) :=
  splitIsometry.isometrySubgroupCongr_intertwines _ _

/-- The full split binary orthogonal group has order 72. -/
public theorem card_orthogonalFour : Nat.card OrthogonalFour = 72 :=
  (Nat.card_congr splitOrthogonalEquiv.toEquiv).trans BinaryFourPlus.card_isometrySubgroup
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
