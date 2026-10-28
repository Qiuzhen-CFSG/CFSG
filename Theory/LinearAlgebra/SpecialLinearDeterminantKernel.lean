module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The determinant kernel

The natural embedding of SL into GL identifies SL with the kernel of the
unit-valued determinant. The inverse simply retains the underlying matrix.
This standard identification works over any commutative ring.
-/

public section

open Matrix
namespace Matrix.SpecialLinearGroup
variable (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]

/-- The special linear group is the determinant kernel in the general linear group. -/
noncomputable def determinantKernelEquiv : SpecialLinearGroup n R ≃*
    (GeneralLinearGroup.det (n := n) (R := R)).ker := by
  let f : SpecialLinearGroup n R →* (GeneralLinearGroup.det (n := n) (R := R)).ker :=
    toGL.codRestrict _ (fun A => coeToGL_det A)
  apply MulEquiv.ofBijective f
  constructor
  · intro A B h
    exact toGL_injective (congrArg Subtype.val h)
  · intro A
    refine ⟨⟨(A : GL n R), ?_⟩, ?_⟩
    · exact Units.ext_iff.mp A.property
    · apply Subtype.ext
      apply GeneralLinearGroup.ext
      intro i j
      rfl
end Matrix.SpecialLinearGroup


end
