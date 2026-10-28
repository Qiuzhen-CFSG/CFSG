/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianScalarCenter.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianDivision

/-!
# IcosianScalarCenter

A quaternion commuting with both i and j is a golden scalar.
Coordinate commutators kill the three imaginary parts; norm one then
forces that scalar to be one or minus one.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianScalarCenter.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

theorem icosian_scalar_of_commutes_I_J (q : IcosianQuaternion)
    (hi : q*icosianI=icosianI*q) (hj : q*icosianJ=icosianJ*q) :
    q=(q.re : IcosianQuaternion) := by
  have hk := congrArg QuaternionAlgebra.imJ hi
  have hji := congrArg QuaternionAlgebra.imK hi
  have hii := congrArg QuaternionAlgebra.imK hj
  simp [icosianI,icosianJ,Quaternion.imJ_mul,Quaternion.imK_mul] at hk hji hii
  have hK : q.imK=0 := CharZero.eq_neg_self_iff.mp hk
  have hJ : q.imJ=0 := CharZero.neg_eq_self_iff.mp hji
  have hI : q.imI=0 := CharZero.eq_neg_self_iff.mp hii
  ext <;> simp [hI,hJ,hK]

theorem icosian_norm_one_commutes_I_J (q : IcosianQuaternion)
    (hn : icosianNorm q=1) (hi : q*icosianI=icosianI*q)
    (hj : q*icosianJ=icosianJ*q) : q=1 ∨ q= -1 := by
  have he := icosian_scalar_of_commutes_I_J q hi hj
  have hs : q.re^2=1 := by
    rw [he] at hn
    simpa [icosianNorm,Quaternion.normSq,pow_two] using hn
  rcases sq_eq_one_iff.mp hs with h | h
  · left; rw [he,h]; rfl
  · right; rw [he,h]; rfl

end Atlas.Algebra
