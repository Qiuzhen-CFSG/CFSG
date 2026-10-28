/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionAxisNorm.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisReflections
public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointAction

/-!
# IcosianReflectionAxisNorm

The coordinate formula for reflecting an axis determines each resulting coordinate
norm. These identities certify links between the local root shapes.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionAxisNorm.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Quaternion

theorem icosianHermitian_two_axis (r : IcosianRationalCoordinates) (i : Fin 3) :
    icosianHermitian r (Pi.single i 2)=star (r i) := by
  rw [← icosianHermitian_star,icosianHermitian_axis_two]

theorem icosianReflection_axis_apply (r : IcosianRationalCoordinates) (i j : Fin 3) :
    icosianReflection r (Pi.single i 2) j=
      (if j=i then 2 else 0)-r j*star (r i) := by
  simp [icosianReflection,icosianHermitian_two_axis,icosianRightMul,Pi.single_apply]

theorem icosianReflection_axis_norm (r : IcosianRationalCoordinates) (i j : Fin 3) :
    icosianNorm (icosianReflection r (Pi.single i 2) j)=
      if j=i then (2-icosianNorm (r i))^2 else icosianNorm (r j)*icosianNorm (r i) := by
  rw [icosianReflection_axis_apply]
  by_cases h : j=i
  · subst j
    simp only [ite_true,Quaternion.self_mul_star]
    have he : (2 : IcosianQuaternion)-(icosianNorm (r i) : IcosianQuaternion)=
        ((2-icosianNorm (r i) : GoldenRational) : IcosianQuaternion) := by
      rw [Quaternion.coe_sub]
      exact congrArg (fun z : IcosianQuaternion => z-(icosianNorm (r i) : IcosianQuaternion))
        (Quaternion.coe_natCast (R := GoldenRational) 2).symm
    change icosianNorm ((2 : IcosianQuaternion)-(icosianNorm (r i) : IcosianQuaternion))=
      (2-icosianNorm (r i))^2
    rw [he]
    exact Quaternion.normSq_coe _
  · simp only [h,ite_false,zero_sub]
    simp only [icosianNorm,Quaternion.normSq_neg,map_mul,Quaternion.normSq_star]

end Atlas.Conway
