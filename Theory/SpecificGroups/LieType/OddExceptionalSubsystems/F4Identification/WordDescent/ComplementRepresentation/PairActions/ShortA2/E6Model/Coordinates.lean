module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.E6Model.BlockAction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates

/-!
# Explicit coordinates for the E6 end-chain representation

This module fixes an integral candidate change of coordinates from the literal
E6 Geck lattice to the matrix, natural, dual and fixed blocks. Root labels are
integer coefficients in the existing numbered E6 simple roots. The signs on
the matrix block and the alternating signs on the dual triples retain the
same parameter for both signed simple curves.

The three active Cartan columns are (-1,1,0), (0,1,-1), and (0,1,1),
for nodes 1, 0, and 2 respectively. Their determinant has absolute value two;
the intended inverse therefore works in characteristic three. No traceless
summand is split off. Bijectivity and the Geck intertwining identities are
separate obligations, not conclusions asserted by this coordinate definition.

The table derivation in `source/derive.py` is an external consistency check,
not a Lean proof. Source: the common-lattice construction in GLS3 §2.6.2,
used in Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.E6Model
open Theory.AlgebraicGroup.StandardRootSystem WordDescent Matrix
attribute [local instance] Classical.decEq

abbrev RootKey := Fin 6 → ℤ

/-- Interpret a label in the literal numbered E6 simple roots. -/
def rootVector (a : RootKey) : Vec 8 := ∑ i, (a i : ℝ) • typeE6SimpleRoot i

def naturalKeys : Fin 9 → Fin 3 → RootKey :=
![
  ![
  ![0, 0, -1, -1, -1, -1],
  ![0, -1, -1, -1, -1, -1],
  ![-1, -1, -1, -1, -1, -1]],
  ![
  ![0, 0, -1, -1, -1, 0],
  ![0, -1, -1, -1, -1, 0],
  ![-1, -1, -1, -1, -1, 0]],
  ![
  ![0, 0, -1, -1, 0, 0],
  ![0, -1, -1, -1, 0, 0],
  ![-1, -1, -1, -1, 0, 0]],
  ![
  ![0, 0, -1, 0, -1, -1],
  ![0, -1, -1, 0, -1, -1],
  ![-1, -1, -1, 0, -1, -1]],
  ![
  ![0, 0, -1, 0, -1, 0],
  ![0, -1, -1, 0, -1, 0],
  ![-1, -1, -1, 0, -1, 0]],
  ![
  ![0, 0, -1, 0, 0, 0],
  ![0, -1, -1, 0, 0, 0],
  ![-1, -1, -1, 0, 0, 0]],
  ![
  ![1, 2, 2, 1, 1, 0],
  ![1, 1, 2, 1, 1, 0],
  ![0, 1, 2, 1, 1, 0]],
  ![
  ![1, 2, 2, 1, 1, 1],
  ![1, 1, 2, 1, 1, 1],
  ![0, 1, 2, 1, 1, 1]],
  ![
  ![1, 2, 2, 1, 2, 1],
  ![1, 1, 2, 1, 2, 1],
  ![0, 1, 2, 1, 2, 1]]]

def dualKeys : Fin 9 → Fin 3 → RootKey :=
![
  ![
  ![-1, -2, -2, -1, -2, -1],
  ![-1, -1, -2, -1, -2, -1],
  ![0, -1, -2, -1, -2, -1]],
  ![
  ![-1, -2, -2, -1, -1, -1],
  ![-1, -1, -2, -1, -1, -1],
  ![0, -1, -2, -1, -1, -1]],
  ![
  ![-1, -2, -2, -1, -1, 0],
  ![-1, -1, -2, -1, -1, 0],
  ![0, -1, -2, -1, -1, 0]],
  ![
  ![0, 0, 1, 0, 0, 0],
  ![0, 1, 1, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0]],
  ![
  ![0, 0, 1, 0, 1, 0],
  ![0, 1, 1, 0, 1, 0],
  ![1, 1, 1, 0, 1, 0]],
  ![
  ![0, 0, 1, 0, 1, 1],
  ![0, 1, 1, 0, 1, 1],
  ![1, 1, 1, 0, 1, 1]],
  ![
  ![0, 0, 1, 1, 0, 0],
  ![0, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 0, 0]],
  ![
  ![0, 0, 1, 1, 1, 0],
  ![0, 1, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 0]],
  ![
  ![0, 0, 1, 1, 1, 1],
  ![0, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1]]]

def fixedKeys : Fin 12 → RootKey :=
![
  ![-1, -2, -3, -2, -2, -1],
  ![-1, -2, -3, -1, -2, -1],
  ![0, 0, 0, -1, 0, 0],
  ![0, 0, 0, 0, -1, -1],
  ![0, 0, 0, 0, -1, 0],
  ![0, 0, 0, 0, 0, -1],
  ![0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 1, 0, 0],
  ![1, 2, 3, 1, 2, 1],
  ![1, 2, 3, 2, 2, 1]]

def matrixKeys : Fin 3 → Fin 3 → RootKey :=
![
  ![
  ![0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0]],
  ![
  ![0, -1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0]],
  ![
  ![-1, -1, 0, 0, 0, 0],
  ![-1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0]]]

/-- The root and pinning sign attached to each non-Cartan block coordinate. -/
def rootData : BlockIndex → Option (RootKey × ℤ)
  | .inl (i,j) => if i = j then none else
      some (matrixKeys i j, (!![0, 1, -1; -1, 0, -1; -1, 1, 0] : Matrix (Fin 3) (Fin 3) ℤ) i j)
  | .inr (.inl (true,h,i)) => some (naturalKeys h i, 1)
  | .inr (.inl (false,h,i)) => some (dualKeys h i, if i = 1 then -1 else 1)
  | .inr (.inr i) => if h : 3 ≤ i.val then some (fixedKeys ⟨i.val - 3, by omega⟩, 1) else none

/-- The six Cartan columns. The matrix block retains its scalar direction. -/
def cartanCoefficient : BlockIndex → Fin 6 → ℤ
  | .inl (i,j), k => if i = j then
      if i = 0 then (if k = 1 then -1 else 0)
      else if i = 1 then (if k.val ≤ 2 then 1 else 0)
      else (if k = 0 then -1 else if k = 2 then 1 else 0)
    else 0
  | .inr (.inl _), _ => 0
  | .inr (.inr i), k => if i.val < 3 ∧ k.val = i.val + 3 then 1 else 0

/-- The integral coordinate matrix, on the original Cartan-plus-root indices. -/
def coordinateMatrix : Matrix BlockIndex Index ℤ
  | c, .inl i => cartanCoefficient c (typeE6RootPairing_baseEquiv.symm i)
  | c, .inr r => match rootData c with
    | none => 0
    | some (a,sgn) => if r.val = rootVector a then sgn else 0

variable (R : Type*) [CommRing R]

/-- Scalar extension of the explicit integral coordinate matrix. -/
def coordinates : (Index → R) →ₗ[R] BlockSpace R :=
  (coordinateMatrix.map (Int.castRingHom R)).mulVecLin

@[simp] theorem coordinates_single (j : Index) :
    coordinates R (Pi.single j 1) = fun c => (coordinateMatrix c j : R) := by
  exact Matrix.mulVec_single_one _ j

/-- Reading a Cartan column requires no root enumeration. -/
theorem coordinates_cartan (j : Fin 6) :
    coordinates R (Pi.single (.inl (simpleIndex j)) 1) =
      fun c => (cartanCoefficient c j : R) := by
  rw [coordinates_single]
  simp only [coordinateMatrix, simpleIndex, Equiv.symm_apply_apply]

/-- The active Cartan coordinates in the order of E6 nodes 0, 1, 2. -/
def cartanCore : Matrix (Fin 3) (Fin 3) R := !![0, -1, 0; 1, 1, 1; -1, 0, 1]

theorem cartanCore_coefficient (i j : Fin 3) :
    (cartanCoefficient (.inl (i,i)) (Fin.castLE (by decide) j) : R) =
      cartanCore R i j := by
  fin_cases i <;> fin_cases j <;> norm_num [cartanCoefficient, cartanCore, Fin.ext_iff]

/-- The active Cartan change of basis requires only inversion of two. -/
theorem cartanCore_det : (cartanCore R).det = 2 := by
  simp [cartanCore, Matrix.det_fin_three, ← two_mul]

variable (F : Type*) [Field F]

/-- In particular, the Cartan block is invertible in characteristic three. -/
theorem cartanCore_bijective (htwo : (2 : F) ≠ 0) :
    Function.Bijective ((cartanCore F).mulVec) := by
  have hu : IsUnit (cartanCore F) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [cartanCore_det]
    exact isUnit_iff_ne_zero.mpr htwo)
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,
    Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.E6Model
