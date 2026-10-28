module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.BlockData
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Binary coordinates for the Suz centralizer's 27 pairs

The given labels are exactly the nonzero singular vectors of the displayed
six-dimensional quadratic form. Six labelled points are the standard basis.
The two matrices below preserve the quadratic form and induce the literal
permutations `blockC` and `blockD`; all finite identities are checked in the
Lean kernel. This constructs isometries, without asserting that they generate
the whole orthogonal group or its commutator subgroup.

Source: GLS3 Table 5.3o and Aschbacher--Smith A.2.19, printed pp.40--41.
Coordinate provenance is in `CentralizerSection/source/README.md`.
-/

@[expose] public section

open ClassicalOrthogonal.Minus
namespace Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel
abbrev K := ZMod 2
abbrev V := Fin 6 → K

def bits (n : ℕ) : V := fun i => if n.testBit i.val then 1 else 0

def pointCode : Fin 27 → ℕ :=
  ![1,2,4,8,16,21,13,32,20,11,52,54,29,44,38,6,12,39,3,60,61,35,31,19,57,46,58]
def pointVector (i : Fin 27) : V := bits (pointCode i)

def term (i j : Fin 6) : QuadraticForm K V :=
  QuadraticMap.linMulLin (LinearMap.proj i) (LinearMap.proj j)
def form : QuadraticForm K V :=
  term 0 2 + term 0 3 + term 0 4 + term 0 5 + term 1 3 + term 1 4 + term 1 5 +
    term 2 5 + term 3 4 + term 3 5 + term 4 5

theorem form_apply (v : V) : form v =
    v 0*v 2 + v 0*v 3 + v 0*v 4 + v 0*v 5 + v 1*v 3 + v 1*v 4 + v 1*v 5 +
    v 2*v 5 + v 3*v 4 + v 3*v 5 + v 4*v 5 := rfl

theorem pointVector_injective : Function.Injective pointVector := by decide +kernel

theorem pointVector_singular : ∀ i, pointVector i ≠ 0 ∧ form (pointVector i) = 0 := by
  decide +kernel

theorem pointVector_exhausts : ∀ v : V, v ≠ 0 → form v = 0 → ∃ i, pointVector i = v := by
  decide +kernel

def basisIndex : Fin 6 → Fin 27 := ![0,1,2,3,4,7]
theorem pointVector_basis : ∀ j : Fin 6,
    pointVector (basisIndex j) = Pi.single j 1 := by decide +kernel

abbrev O := Orthogonal K V form

def columns (w : Fin 6 → ℕ) : Matrix (Fin 6) (Fin 6) K := fun i j => bits (w j) i

def cMatrix := columns ![35,32,20,16,1,57]
def cInverse := columns ![16,19,12,58,8,2]
def dMatrix := columns ![38,6,4,20,61,3]
def dInverse := columns ![38,6,4,61,12,3]

private theorem c_inverse : cInverse * cMatrix = 1 ∧ cMatrix * cInverse = 1 := by
  decide +kernel
private theorem d_inverse : dInverse * dMatrix = 1 ∧ dMatrix * dInverse = 1 := by
  decide +kernel

def cLinear : V ≃ₗ[K] V := Matrix.toLin'OfInv (M := cInverse) (M' := cMatrix)
  (by exact c_inverse.1) (by exact c_inverse.2)
def dLinear : V ≃ₗ[K] V := Matrix.toLin'OfInv (M := dInverse) (M' := dMatrix)
  (by exact d_inverse.1) (by exact d_inverse.2)

theorem c_preserves : ∀ v, form (cLinear v) = form v := by decide +kernel
theorem d_preserves : ∀ v, form (dLinear v) = form v := by decide +kernel

def cIsometry : O := ⟨cLinear,
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form cLinear).mpr c_preserves⟩
def dIsometry : O := ⟨dLinear,
  (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup form dLinear).mpr d_preserves⟩

theorem c_pointVector : ∀ i, cLinear (pointVector i) = pointVector (blockC i) := by
  decide +kernel
theorem d_pointVector : ∀ i, dLinear (pointVector i) = pointVector (blockD i) := by
  decide +kernel

end Sporadic.LeechRelated.Suz.CentralizerSection.ClassicalModel
