module

public import Theory.FieldTheory.Nine
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Concrete unitary generators for the three-dimensional representation of SL₃(2)

Over `F₃[i]`, with `i² = -1`, the displayed determinant-one matrices preserve
the identity Hermitian form. They are the intended images of the elementary
matrix `1 + E₀₁` and the cyclic permutation matrix in SL₃(2). This module
provides the matrices and their elementary identities; construction of the
representation requires checking compatibility with the source group.

The identities below are direct finite-field calculations, checked by the
Lean kernel. No presentation or subgroup recognition is assumed here.
-/

namespace Matrix.PSL3Two

open FiniteField
open scoped Matrix

/-- The involution in the unitary representation, with entries written as
`(real part, imaginary part)` in `F₃[i]`. -/
@[expose] public def unitaryInvolution : SpecialLinearGroup (Fin 3) Nine :=
  ⟨!![1, 1, ⟨2, 1⟩; 1, 1, ⟨1, 2⟩; ⟨2, 2⟩, ⟨1, 1⟩, 0], by decide⟩

/-- The cyclic permutation of the three coordinates. -/
@[expose] public def unitaryCycle : SpecialLinearGroup (Fin 3) Nine :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩

public theorem unitaryInvolution_sq : unitaryInvolution ^ 2 = 1 := by decide

public theorem unitaryCycle_cube : unitaryCycle ^ 3 = 1 := by decide

public theorem unitaryInvolution_unitary :
    (unitaryInvolution.val.map star).transpose * unitaryInvolution.val = 1 := by decide

public theorem unitaryCycle_unitary :
    (unitaryCycle.val.map star).transpose * unitaryCycle.val = 1 := by decide

/-- A special unitary matrix whose order is twelve, used to witness
properness of the binary linear subgroup. -/
@[expose] public def unitaryTwelve : SpecialLinearGroup (Fin 3) Nine :=
  ⟨!![⟨2, 1⟩, ⟨2, 1⟩, 0; ⟨2, 2⟩, ⟨1, 1⟩, 0; 0, 0, 2], by decide⟩

public theorem unitaryTwelve_unitary :
    (unitaryTwelve.val.map star).transpose * unitaryTwelve.val = 1 := by decide

set_option maxRecDepth 10000 in
public theorem unitaryTwelve_pow_twelve : unitaryTwelve ^ 12 = 1 := by decide +kernel

set_option maxRecDepth 10000 in
public theorem unitaryTwelve_powers_ne_one :
    unitaryTwelve ^ 3 ≠ 1 ∧ unitaryTwelve ^ 4 ≠ 1 ∧ unitaryTwelve ^ 7 ≠ 1 := by
  decide +kernel

end Matrix.PSL3Two
