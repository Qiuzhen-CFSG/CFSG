module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.LiftMatrices
/-!
# Integer arithmetic for the icosian pair orbit

Integer quaternions over Z[tau]/(tau²-tau-1), divided by eight, encode the
actual rational quaternion matrices. A faithful coefficient map transfers
kernel-checked integer products to these matrices without repeated rational
normalization. The consumers are the spanning-tree certificates in this
folder and the root-orbit generation proof.

The coordinate conventions come from Gerald Höhn's ATLAS construction;
see LICENSES/ATLAS.txt and the attribution in the imported modules.
-/

@[expose] public section

open Atlas.Algebra
open Sporadic.LeechRelated.J2.IcosianComparison.Generators
open RelatorMatrices
set_option backward.isDefEq.respectTransparency false
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators.OrbitCertificate
abbrev ZQuaternion := Quaternion GoldenInteger
abbrev ZMatrix := Matrix (Fin 3) (Fin 3) ZQuaternion
instance : DecidableEq ZQuaternion := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    QuaternionAlgebra.ext_iff.symm

def qCast : ZQuaternion →+* IcosianQuaternion where
  toFun a := ⟨goldenIntegerToRational a.re, goldenIntegerToRational a.imI,
    goldenIntegerToRational a.imJ, goldenIntegerToRational a.imK⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp

theorem qCast_injective : Function.Injective qCast := by
  intro a b h
  apply QuaternionAlgebra.ext
  · exact goldenIntegerToRational_injective (congrArg QuaternionAlgebra.re h)
  · exact goldenIntegerToRational_injective (congrArg QuaternionAlgebra.imI h)
  · exact goldenIntegerToRational_injective (congrArg QuaternionAlgebra.imJ h)
  · exact goldenIntegerToRational_injective (congrArg QuaternionAlgebra.imK h)

def castMatrix : ZMatrix →+* QMatrix := qCast.mapMatrix

def decode (M : ZMatrix) : QMatrix := (1 / 8 : ℚ) • castMatrix M

theorem castMatrix_zsmul (n : ℤ) (M : ZMatrix) :
    castMatrix (n • M) = (n : ℚ) • castMatrix M := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem decode_mul (A B C : ZMatrix) (h : A * B = (8 : ℤ) • C) :
    decode A * decode B = decode C := by
  simp only [decode, smul_mul_assoc, mul_smul_comm, smul_smul, ← map_mul, h,
    castMatrix_zsmul]
  norm_num [smul_smul]

theorem decode_injective : Function.Injective decode := by
  intro A B h
  apply Matrix.map_injective qCast_injective
  change castMatrix A = castMatrix B
  have hh := congrArg (fun M : QMatrix => (8 : ℚ) • M) h
  simpa [decode, smul_smul] using hh

def ofCoeffs (d : Fin 3 → Fin 3 → Fin 8 → ℤ) : ZMatrix := fun i j =>
  ⟨⟨d i j 0, d i j 1⟩, ⟨d i j 2, d i j 3⟩,
   ⟨d i j 4, d i j 5⟩, ⟨d i j 6, d i j 7⟩⟩

theorem decode_ofCoeffs (d : Fin 3 → Fin 3 → Fin 8 → ℤ) :
    decode (ofCoeffs d) = ofData d := by
  ext i j <;> simp [decode, castMatrix, qCast, ofCoeffs, ofData,
    goldenIntegerToRational, div_eq_mul_inv, mul_comm]
end Sporadic.LeechRelated.J2.IcosianComparison.Generators.OrbitCertificate
