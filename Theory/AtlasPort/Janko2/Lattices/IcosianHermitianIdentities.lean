/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianHermitianIdentities.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRationalSpace

/-!
# Icosian Hermitian Identities

The quaternion-valued Hermitian pairing is additive, conjugate-symmetric,
and compatible with right scalar multiplication. Expanding its finite
sum proves the identities with the correct multiplication order.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianHermitianIdentities.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators Quaternion

def icosianRightMul (x : IcosianRationalCoordinates) (a : IcosianQuaternion) :
    IcosianRationalCoordinates := fun i => x i*a

@[simp] theorem icosianHermitian_add_left (x y z : IcosianRationalCoordinates) :
    icosianHermitian (x+y) z=icosianHermitian x z+icosianHermitian y z := by
  simp [icosianHermitian,star_add (R := IcosianQuaternion),add_mul,Finset.sum_add_distrib,smul_add]

@[simp] theorem icosianHermitian_add_right (x y z : IcosianRationalCoordinates) :
    icosianHermitian x (y+z)=icosianHermitian x y+icosianHermitian x z := by
  simp [icosianHermitian,mul_add,Finset.sum_add_distrib,smul_add]

@[simp] theorem icosianHermitian_sub_left (x y z : IcosianRationalCoordinates) :
    icosianHermitian (x-y) z=icosianHermitian x z-icosianHermitian y z := by
  simp [icosianHermitian,star_sub (R := IcosianQuaternion),sub_mul,Finset.sum_sub_distrib,smul_sub]

@[simp] theorem icosianHermitian_sub_right (x y z : IcosianRationalCoordinates) :
    icosianHermitian x (y-z)=icosianHermitian x y-icosianHermitian x z := by
  simp [icosianHermitian,mul_sub,Finset.sum_sub_distrib,smul_sub]

@[simp] theorem icosianHermitian_rightMul_right (x y : IcosianRationalCoordinates)
    (a : IcosianQuaternion) :
    icosianHermitian x (icosianRightMul y a)=icosianHermitian x y*a := by
  unfold icosianHermitian icosianRightMul
  rw [Algebra.smul_mul_assoc (R := ℚ) (A := IcosianQuaternion)]
  congr 1
  simp [Finset.sum_mul,mul_assoc]

@[simp] theorem icosianHermitian_rightMul_left (x y : IcosianRationalCoordinates)
    (a : IcosianQuaternion) :
    icosianHermitian (icosianRightMul x a) y=star a*icosianHermitian x y := by
  simp [icosianHermitian,icosianRightMul,star_mul,mul_assoc,← Finset.mul_sum,
    Algebra.mul_smul_comm (R := ℚ) (A := IcosianQuaternion)]

theorem icosianHermitian_star (x y : IcosianRationalCoordinates) :
    star (icosianHermitian x y)=icosianHermitian y x := by
  simp [icosianHermitian,star_sum,star_mul]

@[simp] theorem icosianHermitian_smul_right (a : ℚ) (x y : IcosianRationalCoordinates) :
    icosianHermitian x (a • y)=a • icosianHermitian x y := by
  simp only [icosianHermitian,Pi.smul_apply,Algebra.mul_smul_comm (R := ℚ) (A := IcosianQuaternion),← Finset.smul_sum]
  exact smul_comm _ _ _

end Atlas.Lattices
