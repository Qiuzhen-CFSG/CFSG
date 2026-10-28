module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.RootRelations
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry

/-!
# Full coroot covariance of the actual F4 root curves

The positive-coroot word `n(t)n(1)⁻¹` maps to the inverse of the integral
diagonal torus parameter. The diagonal Chevalley conjugation formula therefore
scales a root parameter by its positive coroot pairing. The carrier's faithful
matrix inclusion transports this identity back to actual algebraic-group points.
For a negative simple root the exponent is the negative Cartan row.

The coroot-word realization is reused from `ZeroAndMiddle.Geometry`; this
module supplies the root covariance needed for lowering in rational factors.
The private import of that implementation exposes `matrixH` only inside these
proofs, so its shared public boundary and defining module remain unchanged.

Source: GLS3, Theorem 1.12.1 and the weight conventions of Section 1.14.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
open ZeroAndMiddle

private theorem carrierMatrix_coroot_inverse (j : typeF4RootPairing_base.support) (t : Fˣ) :
    carrierMatrix (algebraicCorootElement j t) =
      (integralChevalleyTorusElement (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter j t))⁻¹ := by
  rw [algebraicCorootElement, map_mul, map_inv, carrierMatrix_n, carrierMatrix_n]
  simp only [Units.val_one]
  rw [← matrixN_neg_one]
  change matrixH (F := F) j t = _
  rw [matrixH_simple, ← integralChevalleyTorusElement_inv]
  congr 1
  funext k
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp

theorem coroot_root_commute (j : typeF4RootPairing_base.support) (r : F4Chevalley.Root)
    (t : Fˣ) (a : F) :
    algebraicCorootElement j t * algebraicRootElement r a =
      algebraicRootElement r
        (((t : F) ^ (typeF4RootPairing.pairingIn ℤ r j)) * a) * algebraicCorootElement j t := by
  apply carrierMatrix_injective
  simp only [map_mul, carrierMatrix_root, carrierMatrix_coroot_inverse]
  have h :
      (integralChevalleyTorusElement (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter j t))⁻¹ * F4Chevalley.rootCurve r a *
      integralChevalleyTorusElement (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter j t) =
      F4Chevalley.rootCurve r
        (((t ^ typeF4RootPairing.pairingIn ℤ r j : Fˣ) : F) * a) :=
    integralChevalleyRootCurve_simpleCoroot_conjugation j t r a
  have he := congrArg (fun g => g *
    (integralChevalleyTorusElement (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter j t))⁻¹) h
  simpa only [mul_assoc, mul_inv_cancel, mul_one, Units.val_zpow_eq_zpow_val] using he

theorem coroot_negativeSimple_commute (i j : Fin 4) (t : Fˣ) (a : F) :
    algebraicCorootElement (typeF4SimpleRootIndex j) t *
      algebraicRootElement (-typeF4SimpleRootIndex i) a =
    algebraicRootElement (-typeF4SimpleRootIndex i)
      (((t : F) ^ (-typeF4CartanMatrix i j)) * a) *
      algebraicCorootElement (typeF4SimpleRootIndex j) t := by
  have h := coroot_root_commute (typeF4RootPairing_baseEquiv j)
    (-typeF4SimpleRootIndex i) t a
  have hp : typeF4RootPairing.pairingIn ℤ (-typeF4SimpleRootIndex i)
      (typeF4RootPairing_baseEquiv j) = -typeF4CartanMatrix i j := by
    rw [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left]
    exact congrArg Neg.neg (typeF4RootPairing_base_cartan_apply i j)
  rw [hp] at h
  simpa only [typeF4RootPairing_baseEquiv_val] using h

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
