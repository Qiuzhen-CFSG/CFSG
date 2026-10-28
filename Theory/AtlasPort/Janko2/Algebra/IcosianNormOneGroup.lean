/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormOneGroup.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianConjugation
public import Mathlib.Algebra.Star.Unitary

/-!
# IcosianNormOneGroup

Integral quaternions of reduced norm one form a subgroup of the
quaternion unitary group. Closure under multiplication and conjugation
provides the group and its constructor from actual norm-one quaternions.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormOneGroup.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


namespace Atlas.Algebra
open scoped Quaternion

/-- Integral quaternions of reduced norm one, inside the actual quaternion algebra. -/
def icosianNormOneGroup : Subgroup (unitary IcosianQuaternion) where
  carrier u := IsIcosian u.val
  one_mem' := icosianOrder.one_mem
  mul_mem' hu hv := icosianOrder.mul_mem hu hv
  inv_mem' hu := icosianOrder_star_mem hu

 theorem icosianNormOneGroup_norm (u : icosianNormOneGroup) :
    icosianNorm u.val.val=1 := by
  have h := Unitary.coe_star_mul_self u.val
  rw [Quaternion.star_mul_self] at h
  exact Quaternion.coe_inj.mp h

/-- Any actual integral reduced-norm-one quaternion gives a scalar group element. -/
def icosianNormOneGroupOf (x : IcosianQuaternion) (hx : IsIcosian x)
    (hn : icosianNorm x=1) : icosianNormOneGroup :=
  ⟨⟨x,by
    change star x*x=1 ∧ x*star x=1
    rw [Quaternion.star_mul_self,Quaternion.self_mul_star]
    change (icosianNorm x : IcosianQuaternion)=1 ∧ (icosianNorm x : IcosianQuaternion)=1
    simp [hn]⟩,hx⟩

end Atlas.Algebra
