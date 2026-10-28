module

public import Theory.Representation.HigmanSims.Twenty.Data
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A checked degree-twenty binary matrix action

The two published HSG1-f2r20B0 matrices generate a subgroup of GL₂₀(2).
Packed-row multiplication certifies their inverses, the order-eleven word
`ab`, and an inverse of `ab - 1`. Thus this word has no nonzero fixed vector.
The subgroup's tautological representation is faithful and has degree twenty.
Comparison with the degree-100 HS carrier and absolute irreducibility are
separate obligations; neither is asserted by naming this matrix group.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
HSG1-f2r20B0; original data and transcription in `source/`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.Twenty

theorem a_square : aMatrix * aMatrix = 1 := by
  apply Thompson.BinaryMatrix.decode_mul_one
  decide +kernel

theorem b_mul_inverse : bMatrix * bInvMatrix = 1 := by
  apply Thompson.BinaryMatrix.decode_mul_one
  decide +kernel

theorem inverse_mul_b : bInvMatrix * bMatrix = 1 := by
  apply Thompson.BinaryMatrix.decode_mul_one
  decide +kernel

theorem a_mul_b : aMatrix * bMatrix = xMatrix := by
  apply Thompson.BinaryMatrix.decode_mul
  decide +kernel

private theorem x_square : xMatrix * xMatrix = x2Matrix := by
  apply Thompson.BinaryMatrix.decode_mul
  decide +kernel

private theorem x2_square : x2Matrix * x2Matrix = x4Matrix := by
  apply Thompson.BinaryMatrix.decode_mul
  decide +kernel

private theorem x4_square : x4Matrix * x4Matrix = x8Matrix := by
  apply Thompson.BinaryMatrix.decode_mul
  decide +kernel

private theorem x8_mul_x2 : x8Matrix * x2Matrix = x10Matrix := by
  apply Thompson.BinaryMatrix.decode_mul
  decide +kernel

private theorem x10_mul_x : x10Matrix * xMatrix = 1 := by
  apply Thompson.BinaryMatrix.decode_mul_one
  decide +kernel

theorem x_pow_eleven : xMatrix ^ 11 = 1 := by
  have h2 : xMatrix ^ 2 = x2Matrix := by simpa only [pow_two] using x_square
  have h4 : xMatrix ^ 4 = x4Matrix := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, h2, pow_two, x2_square]
  have h8 : xMatrix ^ 8 = x8Matrix := by
    rw [show 8 = 4 * 2 from rfl, pow_mul, h4, pow_two, x4_square]
  rw [show 11 = 8 + 2 + 1 from rfl, pow_add, pow_add, h8, h2, pow_one,
    x8_mul_x2, x10_mul_x]

theorem difference_eq : differenceMatrix = xMatrix - 1 := by decide +kernel

theorem inverse_mul_difference : differenceInvMatrix * (xMatrix - 1) = 1 := by
  rw [← difference_eq]
  apply Thompson.BinaryMatrix.decode_mul_one
  decide +kernel

abbrev Ambient := Matrix.GeneralLinearGroup (Fin 20) (ZMod 2)
abbrev Vector := Fin 20 → ZMod 2

def generatorA : Ambient := ⟨aMatrix, aMatrix, a_square, a_square⟩
def generatorB : Ambient := ⟨bMatrix, bInvMatrix, b_mul_inverse, inverse_mul_b⟩

def matrixGroup : Subgroup Ambient := Subgroup.closure {generatorA, generatorB}
abbrev MatrixCarrier := matrixGroup

def a : MatrixCarrier := ⟨generatorA, Subgroup.subset_closure (by simp)⟩
def b : MatrixCarrier := ⟨generatorB, Subgroup.subset_closure (by simp)⟩
def eleven : MatrixCarrier := a * b

def toMatrix : MatrixCarrier →* BinaryMatrix :=
  (Units.coeHom BinaryMatrix).comp matrixGroup.subtype

theorem toMatrix_injective : Function.Injective toMatrix :=
  Units.val_injective.comp Subtype.val_injective

def representation : Representation (ZMod 2) MatrixCarrier Vector :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp toMatrix

theorem representation_injective : Function.Injective representation :=
  Matrix.toLinAlgEquiv'.injective.comp toMatrix_injective

theorem representation_finrank : Module.finrank (ZMod 2) Vector = 20 := by
  simp [Vector]

theorem toMatrix_eleven : toMatrix eleven = xMatrix := a_mul_b

theorem eleven_order : orderOf eleven = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply toMatrix_injective
    rw [map_pow, toMatrix_eleven, x_pow_eleven, map_one]
  · intro h
    have he : xMatrix = 1 := by simpa only [toMatrix_eleven, map_one] using congrArg toMatrix h
    exact (by decide +kernel : xMatrix 0 0 ≠ (1 : BinaryMatrix) 0 0)
      (congrArg (fun m : BinaryMatrix => m 0 0) he)

/-- The order-eleven source word has zero fixed space, proved by an explicit
left inverse of its displacement matrix. -/
theorem eleven_fixedFree : LinearMap.ker (representation eleven - 1) = ⊥ := by
  let L : BinaryMatrix ≃ₐ[ZMod 2] Module.End (ZMod 2) Vector := Matrix.toLinAlgEquiv'
  have hi : L differenceInvMatrix * (representation eleven - 1) = 1 := by
    change L differenceInvMatrix * (L (toMatrix eleven) - 1) = 1
    rw [toMatrix_eleven]
    have h := congrArg L inverse_mul_difference
    simpa only [map_mul, map_sub, map_one] using h
  apply LinearMap.ker_eq_bot.mpr
  intro u v huv
  have h := congrArg (fun w => L differenceInvMatrix w) huv
  change (L differenceInvMatrix * (representation eleven - 1)) u =
    (L differenceInvMatrix * (representation eleven - 1)) v at h
  simpa only [hi, Module.End.one_apply] using h

end Sporadic.LeechRelated.HS.Twenty
