/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAxisTransitionEvaluation.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisTransitionCoordinates

/-!
# IcosianAxisTransitionEvaluation

Right quaternionic linearity recovers a map from its coordinate-axis images. This
gives a matrix formula for the axis transition words.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianAxisTransitionEvaluation.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Evaluation of a right-linear map from its three doubled basis images. -/
theorem icosianRightLinear_apply_two_axes
    (f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates)
    (hf : ∀ a x,f (icosianRightMul x a)=icosianRightMul (f x) a)
    (x : IcosianRationalCoordinates) :
    f x=(1/2 : ℚ) • (icosianRightMul (f (Pi.single 0 2)) (x 0)+
      icosianRightMul (f (Pi.single 1 2)) (x 1)+
      icosianRightMul (f (Pi.single 2 2)) (x 2)) := by
  have hx : x=(1/2 : ℚ) • (icosianRightMul (Pi.single 0 2) (x 0)+
      icosianRightMul (Pi.single 1 2) (x 1)+
      icosianRightMul (Pi.single 2 2) (x 2)) := by
    funext i
    fin_cases i <;> simp [icosianRightMul,two_mul,smul_add,← add_smul] <;> norm_num
  calc
    f x=f ((1/2 : ℚ) • (icosianRightMul (Pi.single 0 2) (x 0)+
      icosianRightMul (Pi.single 1 2) (x 1)+
      icosianRightMul (Pi.single 2 2) (x 2))) := congrArg f hx
    _=_ := by rw [map_smul,map_add,map_add,hf,hf,hf]

def icosianAxisTransitionMatrixApply (k : Fin 4) (x : IcosianRationalCoordinates)
    (j : Fin 3) : IcosianQuaternion :=
  (1/2 : ℚ) • ((icosianAxisTransitionTargetRaw k 0 j * icosianAxisTransitionScalar k 0)*x 0+
    (icosianAxisTransitionTargetRaw k 1 j * icosianAxisTransitionScalar k 1)*x 1+
    (icosianAxisTransitionTargetRaw k 2 j * icosianAxisTransitionScalar k 2)*x 2)

theorem icosianAxisTransitionWord_matrix_apply (k : Fin 4) (x : IcosianRationalCoordinates)
    (j : Fin 3) :
    (icosianAxisTransitionWord k).val x j=icosianAxisTransitionMatrixApply k x j := by
  rw [icosianRightLinear_apply_two_axes _ (icosianAxisTransitionWord k).property.1]
  change (1/2 : ℚ) • (((icosianAxisTransitionWord k).val (Pi.single 0 2) j)*x 0+
    ((icosianAxisTransitionWord k).val (Pi.single 1 2) j)*x 1+
    ((icosianAxisTransitionWord k).val (Pi.single 2 2) j)*x 2)=_
  simp only [icosianAxisTransitionWord_apply,icosianAxisTransitionRaw_axes,
    icosianAxisTransitionMatrixApply]

end Atlas.Conway
