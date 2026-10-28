/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianReflection.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianHermitianIdentities
public import Mathlib.Tactic.NoncommRing

/-!
# Icosian Reflection

A vector of Hermitian norm two defines a quaternionic reflection.
The Hermitian identities show that the reflection is involutive and
preserves the full quaternion-valued pairing.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianReflection.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra

/-- The quaternionic reflection associated with a root of Hermitian norm two. -/
def icosianReflection (r v : IcosianRationalCoordinates) : IcosianRationalCoordinates :=
  v-icosianRightMul r (icosianHermitian r v)

theorem icosianReflection_pairing (r v : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) :
    icosianHermitian r (icosianReflection r v)= -icosianHermitian r v := by
  simp only [icosianReflection,icosianHermitian_sub_right,
    icosianHermitian_rightMul_right,hr]
  noncomm_ring

theorem icosianReflection_involutive (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) : Function.Involutive (icosianReflection r) := by
  intro v
  change icosianReflection r v-icosianRightMul r
    (icosianHermitian r (icosianReflection r v))=v
  rw [icosianReflection_pairing r v hr]
  funext i
  simp only [icosianReflection,icosianRightMul,Pi.sub_apply]
  rw [mul_neg (r i) (icosianHermitian r v),sub_neg_eq_add,sub_add_cancel]

theorem icosianReflection_hermitian (r v w : IcosianRationalCoordinates)
    (hr : icosianHermitian r r=2) :
    icosianHermitian (icosianReflection r v) (icosianReflection r w)=
      icosianHermitian v w := by
  have hv : icosianHermitian v r=star (icosianHermitian r v) :=
    (icosianHermitian_star r v).symm
  simp only [icosianReflection,icosianHermitian_sub_left,icosianHermitian_sub_right,
    icosianHermitian_rightMul_left,icosianHermitian_rightMul_right,hr,hv]
  rw [mul_two (star (icosianHermitian r v)),sub_mul,add_mul]
  abel

end Atlas.Lattices
