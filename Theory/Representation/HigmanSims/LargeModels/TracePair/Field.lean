module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Data.Fintype.Prod

/-!+# Coefficient field for the degree-896 HS matrices

The ATLAS coefficients lie in GF(4). We realize it as F₂[ω], with
ω² = ω + 1, and encode its elements by two bits. The encoding sends the
ATLAS element `Z(4)` to ω. Its Frobenius image differs from ω, providing
the scalar separation used by the trace certificate.

Source: ATLAS of Finite Group Representations, HSG1-f4r896aB0 and
HSG1-f4r896bB0. Exact downloads and encoding are recorded in `source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair

/-- The computable quadratic field F₂[ω], with ω² = ω + 1. -/
abbrev Four := QuadraticAlgebra (ZMod 2) 1 1

instance fourNoRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩

instance fourFintype : Fintype Four :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm

instance fourCharP : CharP Four 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) Four).injective 2

/-- The chosen image of the ATLAS coefficient `Z(4)`. -/
def omega : Four := ⟨0, 1⟩

theorem omega_sq : omega ^ 2 = omega + 1 := by decide +kernel

theorem omega_ne_sq : omega ≠ omega ^ 2 := by decide +kernel

/-- Entry `i` of a row encoded with two little-endian bits per coefficient. -/
def entry (row i : ℕ) : Four :=
  ⟨if row.testBit (2 * i) then 1 else 0,
    if row.testBit (2 * i + 1) then 1 else 0⟩

end Representation.HigmanSims.LargeModels.TracePair
