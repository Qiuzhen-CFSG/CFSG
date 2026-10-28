module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientModel
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Checked comparison of the two max2 binary matrix pairs

The matrices Q record right conjugation on the proposed twelve quotient
coordinates. The matrices R are the literal generators of the independently
counted `LowerBound.quotientSubgroup`. The saved intertwiner P is invertible
and satisfies Q_X P = P R_X and Q_Y P = P R_Y; all seven matrix identities
are checked by kernel reduction. This file supplies an injective action of
the canonical matrix group on the binary vector group. Inverse right
multiplication is used so this is a homomorphism for left composition.

Witness provenance: `ActionKernel/Presentation/source/comparison12.json`
and `quotient_action12.json`; the proposed inverse was obtained by binary
Gaussian elimination and is checked here. The realization of Q on the
actual N/<t> is a separate obligation. Source motivation: GLS3 Table 5.3i,
printed p.270; no order, recognition or simplicity assertion is used.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.OuterImageComparison
open LowerBound Matrix

abbrev BinaryVector := Fin 12 → ZMod 2

def actionX : QuotientMatrix := quotientDecode #v[1, 2, 8, 4, 32, 16, 256, 512, 64, 128, 1085, 3023]
def actionY : QuotientMatrix := quotientDecode #v[2, 4, 1, 16, 64, 128, 8, 1024, 2048, 2982, 32, 3714]
def actionYInverse : QuotientMatrix := quotientDecode #v[4, 1, 2, 64, 8, 1024, 16, 32, 3714, 2465, 128, 256]

def changeBasis : QuotientMatrix := quotientDecode #v[2518, 3898, 1001, 3882, 2513, 1090, 3422, 2679, 1049, 2349, 3311, 2383]
def changeBasisInverse : QuotientMatrix := quotientDecode #v[3736, 3895, 446, 2368, 10, 3314, 2501, 4051, 2547, 1227, 1746, 359]

theorem actionX_square : actionX * actionX = 1 := by decide +kernel
theorem actionY_mul_inverse : actionY * actionYInverse = 1 := by decide +kernel
theorem actionY_inverse_mul : actionYInverse * actionY = 1 := by decide +kernel

theorem changeBasis_mul_inverse : changeBasis * changeBasisInverse = 1 := by decide +kernel
theorem changeBasis_inverse_mul : changeBasisInverse * changeBasis = 1 := by decide +kernel

theorem intertwine_x : actionX * changeBasis = changeBasis * matrixX := by decide +kernel
theorem intertwine_y : actionY * changeBasis = changeBasis * matrixY := by decide +kernel

def actionUnitX : QuotientMatrixˣ := ⟨actionX, actionX, actionX_square, actionX_square⟩
def actionUnitY : QuotientMatrixˣ := ⟨actionY, actionYInverse, actionY_mul_inverse, actionY_inverse_mul⟩
def changeBasisUnit : QuotientMatrixˣ :=
  ⟨changeBasis, changeBasisInverse, changeBasis_mul_inverse, changeBasis_inverse_mul⟩

theorem conjugate_x : changeBasisUnit⁻¹ * actionUnitX * changeBasisUnit = quotientX := by
  have h : actionUnitX * changeBasisUnit = changeBasisUnit * quotientX := Units.ext intertwine_x
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem conjugate_y : changeBasisUnit⁻¹ * actionUnitY * changeBasisUnit = quotientY := by
  have h : actionUnitY * changeBasisUnit = changeBasisUnit * quotientY := Units.ext intertwine_y
  rw [mul_assoc, h, inv_mul_cancel_left]

/-- Inverse right multiplication is a left action and hence a homomorphism. -/
def rowAction : QuotientMatrixˣ →* MulAut (Multiplicative BinaryVector) where
  toFun u := AddEquiv.toMultiplicative
    ({ toFun := fun v => v ᵥ* (↑u⁻¹ : QuotientMatrix)
       invFun := fun v => v ᵥ* (↑u : QuotientMatrix)
       left_inv := fun v => by dsimp only; rw [vecMul_vecMul, Units.inv_mul, vecMul_one]
       right_inv := fun v => by dsimp only; rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
       map_add' := fun a b => add_vecMul _ a b } : BinaryVector ≃+ BinaryVector)
  map_one' := by
    ext v i
    exact congrFun (vecMul_one v.toAdd) i
  map_mul' u v := by
    ext w i
    exact congrFun (vecMul_vecMul w.toAdd (↑v⁻¹ : QuotientMatrix) (↑u⁻¹ : QuotientMatrix)).symm i

theorem rowAction_apply (u : QuotientMatrixˣ) (v : Multiplicative BinaryVector) :
    (rowAction u v).toAdd = v.toAdd ᵥ* (↑u⁻¹ : QuotientMatrix) := rfl

theorem rowAction_injective : Function.Injective rowAction := by
  intro u v h
  have hi : u⁻¹ = v⁻¹ := by
    apply Units.ext
    apply Matrix.ext_iff_vecMul.mpr
    intro w
    exact congrArg (fun a : MulAut (Multiplicative BinaryVector) =>
      (a (Multiplicative.ofAdd w)).toAdd) h
  exact inv_injective hi

attribute [local irreducible] rowAction changeBasisUnit

/-- Canonical quotient matrices act after the certified change of coordinates. -/
def canonicalRowAction : QuotientMatrixˣ →* MulAut (Multiplicative BinaryVector) :=
  rowAction.comp (MulAut.conj changeBasisUnit).toMonoidHom

theorem canonicalRowAction_injective : Function.Injective canonicalRowAction :=
  rowAction_injective.comp (MulAut.conj changeBasisUnit).injective

theorem canonicalRowAction_x : canonicalRowAction quotientX = rowAction actionUnitX := by
  change rowAction (changeBasisUnit * quotientX * changeBasisUnit⁻¹) = _
  rw [← conjugate_x]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]

theorem canonicalRowAction_y : canonicalRowAction quotientY = rowAction actionUnitY := by
  change rowAction (changeBasisUnit * quotientY * changeBasisUnit⁻¹) = _
  rw [← conjugate_y]
  simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.OuterImageComparison
