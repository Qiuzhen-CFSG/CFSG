module
public import Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.Core
import all Theory.SpecificGroups.Rudvalis.Model.PointQuaternion.Embedding
import all Theory.SpecificGroups.Rudvalis.Model.PointCoreBound

/-!
# Square certificate for the Rudvalis point-core quaternion

Two original max6 blocks detect the point core inside the marked Sylow.
For each permitted normal form, the two-point decoder verifies that its
square commutes with both quaternion generators. Sixteen sequential batches
bound kernel-checking memory; the small block lists are checked against the
original alignment. CoreDerived turns this internal certificate into the
intrinsic derived-subgroup centralization theorem.

This internal split intentionally retains the native private coordinates.
Source: Aschbacher--Smith J.2.2--3 and 4.2.13, pp.432--433,611--612.
ATLAS attribution and left-action conventions remain those of Embedding.
-/

namespace Rudvalis.PointQuaternion
open Subgroup SylowOvergroups PointCoreBound
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder
set_option maxRecDepth 30000
set_option Elab.async false

private def blockOne : Finset (Fin 4060) := {460,491,546,887,1366,1412,1444,1596,1659,1959,2473,2482,2637,3336,3551,3575}
private def blockThree : Finset (Fin 4060) := {128,337,433,840,919,966,1008,1145,1614,1626,1648,2229,3135,3432,3669,3696}
private theorem blockOne_eq : blockOne = alignedBlock 1 := by decide +kernel
private theorem blockThree_eq : blockThree = alignedBlock 3 := by decide +kernel

private def squareCommutes (n : Fin 16384) : Prop :=
  normalMap n 460 ∈ blockOne → normalMap n 128 ∈ blockThree →
    (normalMap 1148 (normalMap n (normalMap n 0)) =
      normalMap n (normalMap n (normalMap 1148 0)) ∧
    normalMap 1148 (normalMap n (normalMap n 1)) =
      normalMap n (normalMap n (normalMap 1148 1))) ∧
    (normalMap 3772 (normalMap n (normalMap n 0)) =
      normalMap n (normalMap n (normalMap 3772 0)) ∧
    normalMap 3772 (normalMap n (normalMap n 1)) =
      normalMap n (normalMap n (normalMap 3772 1)))

private instance (n : Fin 16384) : Decidable (squareCommutes n) := inferInstanceAs (Decidable (_ → _ → _))
private theorem square_check_0 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 0 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_1 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 1 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_2 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 2 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_3 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 3 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_4 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 4 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_5 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 5 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_6 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 6 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_7 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 7 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_8 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 8 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_9 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 9 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_10 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 10 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_11 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 11 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_12 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 12 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_13 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 13 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_14 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 14 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem square_check_15 : ∀ n : Fin 1024,
    squareCommutes ⟨1024 * 15 + n.val,by omega⟩ := by
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

end Rudvalis.PointQuaternion
