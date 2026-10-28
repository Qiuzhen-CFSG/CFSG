/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionDiagonal.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonalData
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialEmbedding

/-!
# IcosianReflectionDiagonal

An explicit word in root reflections is a diagonal monomial transformation.
Coordinate-axis evaluation identifies its finite reduction and order-three diagonal
part.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionDiagonal.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes
open scoped Matrix

/-- A right-quaternion-linear rational map is determined on the three axes. -/
theorem icosian_right_linear_ext
    (f g : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates)
    (hf : ∀ a x, f (icosianRightMul x a) = icosianRightMul (f x) a)
    (hg : ∀ a x, g (icosianRightMul x a) = icosianRightMul (g x) a)
    (h : ∀ i : Fin 3, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearEquiv.ext
  intro x
  have hx : x = icosianRightMul (Pi.single 0 1) (x 0) +
      icosianRightMul (Pi.single 1 1) (x 1) +
      icosianRightMul (Pi.single 2 1) (x 2) := by
    funext i
    fin_cases i <;> simp [icosianRightMul]
  rw [hx]
  simp only [map_add,hf,hg,h]

def icosianReflectionDiagonalWord : icosianHermitianGroup :=
  icosianReflectionDiagonalGenerator 0 * icosianReflectionDiagonalGenerator 2 *
    icosianReflectionDiagonalGenerator 1 * icosianReflectionDiagonalGenerator 0

theorem icosianReflectionDiagonalWord_mem (H : Subgroup icosianHermitianGroup)
    (h : ∀ k, icosianReflectionDiagonalGenerator k ∈ H) :
    icosianReflectionDiagonalWord ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem (h 0) (h 2)) (h 1)) (h 0)

def icosianReflectionDiagonalPermutation : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

def icosianReflectionDiagonalMonomial : IcosianUnitMonomial :=
  ⟨icosianReflectionDiagonalUnit,icosianReflectionDiagonalPermutation⟩

def icosianReflectionDiagonalRaw (x : IcosianRationalCoordinates) :
    IcosianRationalCoordinates :=
  icosianReflection (icosianReflectionDiagonalRoot 0)
    (icosianReflection (icosianReflectionDiagonalRoot 2)
      (icosianReflection (icosianReflectionDiagonalRoot 1)
        (icosianReflection (icosianReflectionDiagonalRoot 0) x)))

attribute [local irreducible] icosianReflectionDiagonalWord icosianReflectionDiagonalMonomial

theorem icosianReflectionDiagonalGenerator_apply (k : Fin 3)
    (x : IcosianRationalCoordinates) :
    (icosianReflectionDiagonalGenerator k).val x =
      icosianReflection (icosianReflectionDiagonalRoot k) x := rfl

theorem icosianReflectionDiagonalWord_apply (x : IcosianRationalCoordinates) :
    icosianReflectionDiagonalWord.val x = icosianReflectionDiagonalRaw x := by
  simp only [icosianReflectionDiagonalWord,Subgroup.coe_mul,LinearEquiv.mul_apply,
    icosianReflectionDiagonalGenerator_apply,icosianReflectionDiagonalRaw]

theorem icosianReflectionMonomial_apply (g : IcosianUnitMonomial)
    (x : IcosianRationalCoordinates) (i : Fin 3) :
    icosianMonomialRepresentation g x i =
      (icosianMonomialUnits (g.left i) : IcosianQuaternion)*x (g.right.symm i) := rfl

theorem icosianReflectionDiagonalUnit_value (i : Fin 3) :
    (icosianMonomialUnits (icosianReflectionDiagonalUnit i) : IcosianQuaternion) =
      (icosianReflectionDiagonalUnitIntegral i).val := rfl

theorem icosianReflectionDiagonalMonomial_apply (x : IcosianRationalCoordinates)
    (i : Fin 3) :
    icosianMonomialRepresentation icosianReflectionDiagonalMonomial x i =
      (icosianReflectionDiagonalUnitIntegral i).val *
        x (icosianReflectionDiagonalPermutation.symm i) := by
  rw [icosianReflectionMonomial_apply]
  have hl : icosianReflectionDiagonalMonomial.left = icosianReflectionDiagonalUnit := by
    unfold icosianReflectionDiagonalMonomial
    rfl
  have hr : icosianReflectionDiagonalMonomial.right = icosianReflectionDiagonalPermutation := by
    unfold icosianReflectionDiagonalMonomial
    rfl
  rw [hl,hr,icosianReflectionDiagonalUnit_value]

set_option maxHeartbeats 500000 in
theorem icosianReflectionDiagonalRaw_axes :
    ∀ i j : Fin 3, icosianReflectionDiagonalRaw (Pi.single i 1) j =
      (icosianReflectionDiagonalUnitIntegral j).val *
        (Pi.single i 1 : IcosianRationalCoordinates) (icosianReflectionDiagonalPermutation.symm j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> apply QuaternionAlgebra.ext <;> decide +kernel

/-- The four-reflection word is checked on only three quaternionic basis vectors. -/
theorem icosianReflectionDiagonalWord_axes :
    ∀ i j : Fin 3, icosianReflectionDiagonalWord.val (Pi.single i 1) j =
      icosianMonomialRepresentation icosianReflectionDiagonalMonomial (Pi.single i 1) j := by
  intro i j
  rw [icosianReflectionDiagonalWord_apply,icosianReflectionDiagonalMonomial_apply]
  exact icosianReflectionDiagonalRaw_axes i j

/-- An identity of actual rational linear maps, with no permutation certificate. -/
theorem icosianReflectionDiagonalWord_linear :
    icosianReflectionDiagonalWord.val =
      icosianMonomialRepresentation icosianReflectionDiagonalMonomial := by
  apply icosian_right_linear_ext
  · exact icosianReflectionDiagonalWord.property.1
  · exact icosianMonomialRepresentation_right_linear _
  · intro i
    funext j
    exact icosianReflectionDiagonalWord_axes i j

theorem icosianReflectionDiagonalMonomial_reduction (i : Fin 3) :
    ((icosianMonomialReduction icosianReflectionDiagonalMonomial).left i).val =
      !![goldenFourTau, (![goldenFourTau+1,1,goldenFourTau] i);0,goldenFourTau+1] := by
  unfold icosianReflectionDiagonalMonomial
  change icosianModuloTwo (icosianNormOneToOrder (icosianReflectionDiagonalUnit i)) = _
  have h : icosianNormOneToOrder (icosianReflectionDiagonalUnit i) =
      icosianReflectionDiagonalUnitIntegral i := by apply Subtype.ext; rfl
  rw [h,icosianReflectionDiagonalUnit_reduction]

theorem icosianReflectionDiagonal_nontrivial : goldenFourTau ≠ 1 := by decide +kernel

theorem icosianReflectionDiagonal_order_three : goldenFourTau^3 = 1 := by decide +kernel

end Atlas.Conway
