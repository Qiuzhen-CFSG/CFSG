/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianUnitNormShells.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReductionSurjective
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneKernelCard

/-!
# IcosianUnitNormShells

Multiplication by an integral unit identifies the norm-one group
with the shell having that unit's reduced norm. Multiplication by its
inverse proves the bijection, so each such shell has 120 elements.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianUnitNormShells.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

/-- An actual scalar reduced-norm fiber inside the integral icosian order. -/
abbrev IcosianNormShell (t : GoldenRational) := {x : icosianOrder // icosianNorm x.val=t}

theorem icosianNorm_unit_inverse (a : icosianOrderˣ) :
    icosianNorm ((a⁻¹ : icosianOrderˣ) : icosianOrder).val*
      icosianNorm (a : icosianOrder).val=1 := by
  rw [← icosianNorm_mul]
  change icosianNorm (((a⁻¹ : icosianOrderˣ) : icosianOrder)*
    (a : icosianOrder)).val=1
  rw [Units.inv_mul]
  exact icosianNormOneGroup_norm 1

def icosianUnitNormParameter (a : icosianOrderˣ) (u : icosianNormOneGroup) :
    IcosianNormShell (icosianNorm (a : icosianOrder).val) :=
  ⟨(a : icosianOrder)*icosianNormOneToOrder u,by
    change icosianNorm ((a : icosianOrder).val*u.val.val)=_
    rw [icosianNorm_mul,icosianNormOneGroup_norm,mul_one]⟩

def icosianUnitNormInverse (a : icosianOrderˣ)
    (x : IcosianNormShell (icosianNorm (a : icosianOrder).val)) : icosianNormOneGroup :=
  icosianNormOneGroupOf (((a⁻¹ : icosianOrderˣ) : icosianOrder)*x.val).val
    (((a⁻¹ : icosianOrderˣ) : icosianOrder)*x.val).property (by
      change icosianNorm (((a⁻¹ : icosianOrderˣ) : icosianOrder).val*x.val.val)=1
      rw [icosianNorm_mul,x.property,icosianNorm_unit_inverse])

def icosianUnitNormEquiv (a : icosianOrderˣ) :
    icosianNormOneGroup ≃ IcosianNormShell (icosianNorm (a : icosianOrder).val) where
  toFun := icosianUnitNormParameter a
  invFun := icosianUnitNormInverse a
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change (((a⁻¹ : icosianOrderˣ) : icosianOrder)*
      ((a : icosianOrder)*icosianNormOneToOrder u)).val=u.val.val
    rw [← mul_assoc,Units.inv_mul,one_mul]
    rfl
  right_inv x := by
    apply Subtype.ext
    change (a : icosianOrder)*
      (((a⁻¹ : icosianOrderˣ) : icosianOrder)*x.val)=x.val
    rw [← mul_assoc,Units.mul_inv,one_mul]

theorem icosianUnitNormShell_card (a : icosianOrderˣ) :
    Nat.card (IcosianNormShell (icosianNorm (a : icosianOrder).val))=120 := by
  rw [← Nat.card_congr (icosianUnitNormEquiv a),icosianNormOneGroup_card]

end Atlas.Algebra
