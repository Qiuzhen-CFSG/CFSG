module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Field.ZMod

/-!
# The binary special-linear affine group

The model is the semidirect product of the binary natural module by SL_d(2).
Its multiplication uses the literal column-vector action. These coordinates
are used to reconstruct the split local group in Aschbacher--Smith 12.2.26--27,
printed pp.806--807. No recognition theorem is included in this model.
-/

public noncomputable section
namespace BinaryLinear.Affine
/-- The literal special-linear action on the multiplicative binary natural module. -/
@[expose] def action (d : ℕ) : Matrix.SpecialLinearGroup (Fin d) (ZMod 2) →*
    MulAut (Multiplicative (Fin d → ZMod 2)) where
  toFun a := (Matrix.SpecialLinearGroup.toLin' a).toAddEquiv.toMultiplicative
  map_one' := by ext x; exact congrArg Multiplicative.ofAdd (by simp)
  map_mul' a b := by ext x; exact congrArg Multiplicative.ofAdd (by simp)

abbrev Model (d : ℕ) :=
  Multiplicative (Fin d → ZMod 2) ⋊[action d]
    Matrix.SpecialLinearGroup (Fin d) (ZMod 2)

theorem action_apply (d : ℕ) (a : Matrix.SpecialLinearGroup (Fin d) (ZMod 2))
    (v : Multiplicative (Fin d → ZMod 2)) :
    action d a v = Multiplicative.ofAdd (Representation.specialLinearNatural d a v.toAdd) := by
  rfl

end BinaryLinear.Affine
