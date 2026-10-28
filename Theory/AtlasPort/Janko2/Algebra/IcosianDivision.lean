/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianDivision.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianQuaternion

/-!
# IcosianDivision

The golden quaternion algebra is a division ring. Nondegeneracy of the
rational norm pairing shows that the reduced norm vanishes only at zero;
conjugation divided by that norm then supplies the inverse.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianDivision.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

theorem icosianNorm_eq_zero (x : IcosianQuaternion) : icosianNorm x=0 ↔ x=0 := by
  constructor
  · intro h
    apply (icosianFunctional_star_mul_self_eq_zero x).mp
    rw [Quaternion.star_mul_self]
    change goldenFunctional (icosianNorm x)=0
    rw [h]
    rfl
  · rintro rfl
    exact map_zero Quaternion.normSq

instance icosianQuaternion_inv : Inv IcosianQuaternion :=
  ⟨fun x => (icosianNorm x)⁻¹ • star x⟩

instance icosianQuaternion_groupWithZero : GroupWithZero IcosianQuaternion :=
  { (inferInstance : MonoidWithZero IcosianQuaternion), (inferInstance : Nontrivial IcosianQuaternion) with
    inv_zero := by change (icosianNorm 0)⁻¹ • star (0 : IcosianQuaternion)=0; simp
    mul_inv_cancel := fun x hx => by
      change x*((icosianNorm x)⁻¹ • star x)=1
      rw [Algebra.mul_smul_comm (icosianNorm x)⁻¹ x (star x),
        Quaternion.self_mul_star,Quaternion.smul_coe]
      change (((icosianNorm x)⁻¹*icosianNorm x : GoldenRational) : IcosianQuaternion)=1
      rw [inv_mul_cancel₀ (fun h => hx ((icosianNorm_eq_zero x).mp h))]
      rfl }

theorem icosianQuaternion_coe_inv (a : GoldenRational) :
    ((a⁻¹ : GoldenRational) : IcosianQuaternion)=(a : IcosianQuaternion)⁻¹ :=
  map_inv₀ (algebraMap GoldenRational IcosianQuaternion) a

theorem icosianQuaternion_coe_div (a b : GoldenRational) :
    ((a/b : GoldenRational) : IcosianQuaternion)=(a : IcosianQuaternion)/(b : IcosianQuaternion) :=
  map_div₀ (algebraMap GoldenRational IcosianQuaternion) a b

instance icosianQuaternion_divisionRing : DivisionRing IcosianQuaternion where
  __ := Quaternion.instRing
  __ := icosianQuaternion_groupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def _ := by
    rw [← Quaternion.coe_nnratCast,NNRat.cast_def,icosianQuaternion_coe_div,
      Quaternion.coe_natCast,Quaternion.coe_natCast]
  ratCast_def _ := by
    rw [← Quaternion.coe_ratCast,Rat.cast_def,icosianQuaternion_coe_div,
      Quaternion.coe_intCast,Quaternion.coe_natCast]
  nnqsmul_def _ _ := by
    rw [← Quaternion.coe_nnratCast,Quaternion.coe_mul_eq_smul]
    ext1 <;> exact NNRat.smul_def ..
  qsmul_def _ _ := by
    rw [← Quaternion.coe_ratCast,Quaternion.coe_mul_eq_smul]
    ext1 <;> exact Rat.smul_def ..

end Atlas.Algebra
