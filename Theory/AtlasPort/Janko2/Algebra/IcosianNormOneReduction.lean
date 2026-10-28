/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormOneReduction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianReductionNorm
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneGroup
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# IcosianNormOneReduction

Reduction sends the actual integral norm-one group to SL₂(F₄).
Compatibility of reduced norm with determinant proves that the ring
homomorphism restricts to this group homomorphism.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormOneReduction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra

def icosianNormOneToOrder : icosianNormOneGroup →* icosianOrder where
  toFun u := ⟨u.val.val,u.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual scalar
 norm-one group reduces to determinant-one matrices. -/
def icosianNormOneReduction : icosianNormOneGroup →*
    Matrix.SpecialLinearGroup (Fin 2) GoldenFour where
  toFun u := ⟨icosianModuloTwo ⟨u.val.val,u.property⟩,by
    rw [icosianModuloTwo_det]
    have h : icosianIntegralNorm ⟨u.val.val,u.property⟩=1 :=
      (icosianIntegralNorm_eq_one _).mpr (icosianNormOneGroup_norm u)
    rw [h,map_one]⟩
  map_one' := by
    apply Subtype.ext
    change icosianModuloTwo (1 : icosianOrder)=1
    exact map_one icosianModuloTwo
  map_mul' u v := by
    apply Subtype.ext
    change icosianModuloTwo (⟨u.val.val,u.property⟩*⟨v.val.val,v.property⟩)=_
    exact map_mul icosianModuloTwo _ _

theorem icosianNormOneReduction_apply (u : icosianNormOneGroup) :
    (icosianNormOneReduction u).val=icosianModuloTwo ⟨u.val.val,u.property⟩ := rfl

end Atlas.Algebra
